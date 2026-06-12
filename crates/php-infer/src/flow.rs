//! M-T5: **flow-sensitive statement analysis**.
//!
//! Expression inference ([`crate::TypeCtx::infer`]) reads variable types from an
//! environment but never populates it. This module walks statements and *builds*
//! that environment: assignments record the assigned type, `foreach` binds its
//! key/value variables, function parameters seed from their reflected types, and
//! conditional branches merge by unioning each variable's type across paths.
//!
//! It is a bounded forward pass: straight-line flow is single-pass, while loop
//! bodies iterate a few times to stabilize loop-carried facts. A variable
//! assigned on only some paths widens to include its prior/`mixed` value. This
//! approximation is sound enough to drive diagnostics and never panics.

use crate::{
    arrays, collection_method,
    refine::{strip_false, strip_falsy, strip_null_strict},
    CallableAlias, TypeCtx,
};
use php_ast::{
    Arg, ArrowFn, BinOp, ClosureExpr, Expr, ExprKind, FunctionDecl, Name, Param, Stmt, StmtKind,
    UnOp,
};
use php_types::Type;
use std::collections::{HashMap, HashSet};

/// A variable environment: name (without `$`) → type.
type Env = HashMap<String, Type>;

/// Flow-local callable aliases: variable name → direct closure/arrow target.
type CallableEnv = HashMap<String, CallableAlias>;

type FlowState = (Env, CallableEnv);

/// The recording target for [`TypeCtx::record_block`]: a `span (start,end) → Type`
/// map (the same shape as [`crate::TypeMap`]).
type RecMap = HashMap<(u32, u32), Type>;

/// A flow-narrowing fact: a "place" (a variable, or `$this->prop`/`$v->prop`)
/// and the type it definitely has in the branch. Only *sound* refinements are
/// produced (the branch guarantees them) — under-narrowing is safe; over-narrowing
/// (which would cause false positives) never happens. Strip-style narrowings
/// (`$x !== null`, truthy `if ($x)`) are resolved to a concrete type at collection
/// time against the place's current type, so a property's declared type (not
/// `mixed`) is the baseline.
type Fact = (String, Type);

const LOOP_FIXPOINT_LIMIT: usize = 6;

impl TypeCtx<'_> {
    /// Seed parameters from a function/method's reflected signature, then analyse
    /// its body, leaving `self.vars` reflecting the end-of-body environment.
    pub fn analyze_function_body(&mut self, f: &FunctionDecl) {
        let refl = php_reflect::reflect_function(self.scope, self.interner, f);
        for p in &refl.params {
            self.vars.insert(p.name.clone(), p.local_type());
        }
        self.exec_block(&f.body);
    }

    /// Analyse a sequence of statements, advancing `self.vars` (without retaining
    /// the per-expression type map). A thin wrapper over the single flow engine
    /// ([`record_block`]) with a throw-away recording sink — used by consumers that
    /// only need the end-of-block environment (definedness-adjacent rules, sweeps).
    pub fn exec_block(&mut self, stmts: &[Stmt]) {
        let mut scratch = RecMap::new();
        self.record_block(stmts, &mut scratch);
    }

    /// Analyse one statement, advancing `self.vars`. Like [`exec_block`], a wrapper
    /// over [`record_stmt`] that discards the recording.
    pub fn exec_stmt(&mut self, s: &Stmt) {
        let mut scratch = RecMap::new();
        self.record_stmt(s, &mut scratch);
    }

    /// Analyse `e` for its effect on the environment (recording assignments to
    /// simple variables) and return its inferred type.
    pub fn apply_expr(&mut self, e: &Expr) -> Type {
        match &e.kind {
            // Peel parentheses so a parenthesised assignment still binds — e.g. the
            // common `if (($x = f()))` / `while (($row = next()))` idiom.
            ExprKind::Paren(inner) => self.apply_expr(inner),
            ExprKind::Assign { target, rhs } | ExprKind::AssignRef { target, rhs } => {
                let t = self.apply_expr(rhs);
                let callable = self.callable_alias_from_expr(rhs);
                let bound = if matches!(&peel_paren(rhs).kind, ExprKind::Str(_)) {
                    t
                } else {
                    self.callable_expr_type(rhs).unwrap_or(t)
                };
                self.bind_target_with_callable(target, &bound, callable);
                bound
            }
            ExprKind::AssignOp { op, target, rhs } => {
                let t = self.binary_type(*op, target, rhs);
                self.bind_target(target, &t);
                t
            }
            _ => self.infer(e),
        }
    }

    /// Record an assignment target's new type. Simple `$var` targets are stored;
    /// list-destructuring targets bind their leaf variables to `mixed` (precise
    /// element typing is a later refinement). `$this` is never rebound.
    fn bind_target(&mut self, target: &Expr, ty: &Type) {
        match &target.kind {
            ExprKind::Variable(sym) => {
                let name = self.interner.resolve(*sym).to_string();
                if name != "this" {
                    self.vars.insert(name.clone(), ty.clone());
                    self.callables.remove(&name);
                }
            }
            ExprKind::Array { items, .. } => {
                for it in items.iter() {
                    if let Some(v) = &it.value {
                        self.bind_target(v, &Type::Mixed);
                    }
                }
            }
            _ => {}
        }
    }

    fn bind_target_with_callable(
        &mut self,
        target: &Expr,
        ty: &Type,
        callable: Option<CallableAlias>,
    ) {
        match &target.kind {
            ExprKind::Variable(sym) => {
                let name = self.interner.resolve(*sym).to_string();
                if name == "this" {
                    return;
                }
                self.vars.insert(name.clone(), ty.clone());
                match callable {
                    Some(alias) => {
                        self.callables.insert(name, alias);
                    }
                    None => {
                        self.callables.remove(&name);
                    }
                }
            }
            ExprKind::Array { items, .. } => {
                for it in items.iter() {
                    if let Some(v) = &it.value {
                        self.bind_target(v, &Type::Mixed);
                    }
                }
            }
            _ => self.bind_target(target, ty),
        }
    }

    fn callable_alias_from_expr(&self, e: &Expr) -> Option<CallableAlias> {
        match &peel_paren(e).kind {
            ExprKind::Closure(c) => {
                let mut vars = Env::new();
                let mut callables = CallableEnv::new();
                for u in &c.uses {
                    let name = self.interner.resolve(u.name).to_string();
                    vars.insert(
                        name.clone(),
                        self.vars.get(&name).cloned().unwrap_or(Type::Mixed),
                    );
                    if let Some(alias) = self.callables.get(&name) {
                        callables.insert(name, alias.clone());
                    }
                }
                Some(CallableAlias::Closure {
                    id: span_key(e),
                    expr: c.clone(),
                    vars,
                    callables,
                    class: (!c.is_static).then(|| self.class.clone()).flatten(),
                })
            }
            ExprKind::ArrowFn(a) => {
                let mut vars = self.vars.clone();
                if a.is_static {
                    strip_this_vars(&mut vars);
                }
                Some(CallableAlias::Arrow {
                    id: span_key(e),
                    expr: a.clone(),
                    vars,
                    callables: self.callables.clone(),
                    class: (!a.is_static).then(|| self.class.clone()).flatten(),
                })
            }
            ExprKind::Variable(sym) => {
                let name = self.interner.resolve(*sym);
                self.callables.get(name).cloned()
            }
            _ => None,
        }
    }

    /// Collect the narrowing facts implied by `cond` evaluating to `truthy`.
    fn narrow_facts(&self, cond: &Expr, truthy: bool) -> Vec<Fact> {
        let mut out = Vec::new();
        self.collect_facts(cond, truthy, &mut out);
        out
    }

    fn collect_facts(&self, cond: &Expr, truthy: bool, out: &mut Vec<Fact>) {
        match &cond.kind {
            ExprKind::Paren(inner) => self.collect_facts(inner, truthy, out),
            ExprKind::Unary {
                op: UnOp::Not,
                expr,
            } => self.collect_facts(expr, !truthy, out),
            ExprKind::Binary { op, lhs, rhs } => match op {
                // `a && b` true ⇒ both true. `a || b` false ⇒ both false.
                BinOp::BoolAnd | BinOp::LogicalAnd if truthy => {
                    self.collect_facts(lhs, true, out);
                    self.collect_facts(rhs, true, out);
                }
                BinOp::BoolOr | BinOp::LogicalOr if !truthy => {
                    self.collect_facts(lhs, false, out);
                    self.collect_facts(rhs, false, out);
                }
                // `a || b` true ⇒ at least one holds. A place can only be asserted
                // if *both* operands constrain it — then it is the *union* of the
                // two narrowings (`$n instanceof A || $n instanceof B` ⇒ `$n: A|B`).
                // Places constrained by only one side are dropped.
                BinOp::BoolOr | BinOp::LogicalOr if truthy => {
                    let l = self.narrow_facts(lhs, true);
                    let r = self.narrow_facts(rhs, true);
                    for (place, lt) in &l {
                        if let Some((_, rt)) = r.iter().find(|(p, _)| p == place) {
                            out.push((place.clone(), Type::union(vec![lt.clone(), rt.clone()])));
                        }
                    }
                }
                // `$x === null` true ⇒ $x is null; false ⇒ null stripped.
                BinOp::Identical | BinOp::Eq => self.null_cmp(lhs, rhs, truthy, out),
                BinOp::NotIdentical | BinOp::NotEq => self.null_cmp(lhs, rhs, !truthy, out),
                // Integer-range narrowing: `$x < 2` false ⇒ `$x: int<2, max>`, etc.
                BinOp::Lt | BinOp::LtEq | BinOp::Gt | BinOp::GtEq => {
                    self.int_cmp_facts(*op, lhs, rhs, truthy, out)
                }
                _ => {}
            },
            ExprKind::Instanceof { expr, class } => {
                if let (Some(place), Some(t)) = (self.place_key(expr), self.class_type(class)) {
                    if truthy {
                        out.push((place, t));
                    } else {
                        // `!($x instanceof C)` ⇒ drop the union members that are
                        // *confidently* subclasses of C (both indexed). Unknown
                        // members are kept (sound under-narrowing).
                        let cur = self.infer(expr);
                        let narrowed =
                            subtract_union(&cur, |m| confident_subclass(m, &t, self.index));
                        if narrowed != cur {
                            out.push((place, narrowed));
                        }
                    }
                }
            }
            ExprKind::Call { callee, args } => {
                if let ExprKind::Name(n) = &callee.kind {
                    let fname = last_segment(&n.text).to_ascii_lowercase();
                    if let Some(arg0) = args.first() {
                        if let Some(place) = self.place_key(&arg0.value) {
                            if truthy {
                                if let Some(t) = predicate_type(&fname) {
                                    out.push((place, t));
                                }
                            } else if fname == "is_null" {
                                // `!is_null($x)` ⇒ null stripped from $x's type.
                                out.push((place, strip_null_strict(&self.infer(&arg0.value))));
                            } else if let Some(t) = predicate_type(&fname) {
                                // `!is_string($x)` etc. ⇒ drop the union members of
                                // that kind (`string|array` → `array`). Only narrows a
                                // union, never to empty (sound under-narrowing).
                                let cur = self.infer(&arg0.value);
                                let narrowed = subtract_union(&cur, |m| predicate_matches(m, &t));
                                if narrowed != cur {
                                    out.push((place, narrowed));
                                }
                            }
                        }
                    }
                }
            }
            // A bare truthy place (`if ($x)`, `if ($this->x)`) is non-null *and*
            // non-false in the then-branch.
            _ if truthy => {
                if let Some(place) = self.place_key(cond) {
                    out.push((place, strip_falsy(&self.infer(cond))));
                }
            }
            _ => {}
        }
    }

    /// Integer-range narrowing from a `<`/`<=`/`>`/`>=` comparison between a place
    /// and an int literal. Produces `place: int<min, max>` for the branch where the
    /// comparison has truth value `truthy` (intersected with the place's current
    /// range). E.g. the false branch of `$n < 2` ⇒ `$n: int<2, max>`.
    fn int_cmp_facts(&self, op: BinOp, lhs: &Expr, rhs: &Expr, truthy: bool, out: &mut Vec<Fact>) {
        // Normalise to `place OP literal`. If the literal is on the left, flip the op.
        let (place_expr, lit, op) = if let Some(n) = int_lit(rhs) {
            (lhs, n, op)
        } else if let Some(n) = int_lit(lhs) {
            (rhs, n, flip_cmp(op))
        } else {
            return;
        };
        let Some(place) = self.place_key(place_expr) else {
            return;
        };
        // The effective op for this branch (negate when the condition is false).
        let eff = if truthy { op } else { negate_cmp(op) };
        // `place eff lit` ⇒ a half-bounded int range.
        let (min, max) = match eff {
            BinOp::Lt => (None, Some(lit - 1)),
            BinOp::LtEq => (None, Some(lit)),
            BinOp::Gt => (Some(lit + 1), None),
            BinOp::GtEq => (Some(lit), None),
            _ => return,
        };
        // Only narrow a value that's currently int-like (avoid clobbering unknowns).
        let cur = self.infer(place_expr);
        if !matches!(cur, Type::Int | Type::IntRange { .. } | Type::LiteralInt(_)) {
            return;
        }
        out.push((place, Type::int_range(min, max)));
    }

    /// `$x <cmp> null|false` / `null|false <cmp> $x`. `eq` = whether the
    /// comparison asserts equality (so the place *is* that literal) in this branch.
    fn null_cmp(&self, lhs: &Expr, rhs: &Expr, eq: bool, out: &mut Vec<Fact>) {
        let (operand, lit) = if let Some(l) = self.cmp_lit(rhs) {
            (lhs, l)
        } else if let Some(l) = self.cmp_lit(lhs) {
            (rhs, l)
        } else {
            return;
        };
        let Some(place) = self.place_key(operand) else {
            return;
        };
        let t = match (lit, eq) {
            (Type::Null, true) => Type::Null,
            (Type::Null, false) => strip_null_strict(&self.infer(operand)),
            (Type::False, true) => Type::False,
            (Type::False, false) => strip_false(&self.infer(operand)),
            _ => return,
        };
        out.push((place, t));
    }

    /// If `e` is a `null` or `false` literal, the corresponding [`Type`].
    fn cmp_lit(&self, e: &Expr) -> Option<Type> {
        match &e.kind {
            ExprKind::Name(n) if n.text.eq_ignore_ascii_case("null") => Some(Type::Null),
            ExprKind::Name(n) if n.text.eq_ignore_ascii_case("false") => Some(Type::False),
            _ => None,
        }
    }

    fn apply_facts(&mut self, facts: &[Fact]) {
        let idx = self.index;
        let mut vars = std::mem::take(&mut self.vars);
        apply_facts_to(&mut vars, facts, idx);
        self.vars = vars;
    }

    /// The narrowable "place" key of `e`: a simple variable (`x`), or a property
    /// fetch on a simple variable / `$this` (`this->prop`, `obj->prop`). `$this`
    /// itself is not a place. Property places let guards on object state narrow
    /// (`if ($this->c instanceof X)`, `if (!$this->c) return`), which OO code
    /// relies on pervasively.
    pub(crate) fn place_key(&self, e: &Expr) -> Option<String> {
        match &e.kind {
            ExprKind::Variable(sym) => {
                let n = self.interner.resolve(*sym);
                (n != "this").then(|| n.to_string())
            }
            ExprKind::Prop {
                base,
                name: php_ast::MemberName::Ident(p),
                nullsafe: false,
            } => {
                let ExprKind::Variable(b) = &base.kind else {
                    return None;
                };
                Some(format!(
                    "{}->{}",
                    self.interner.resolve(*b),
                    self.interner.resolve(*p)
                ))
            }
            ExprKind::MethodCall {
                recv,
                method: php_ast::MemberName::Ident(m),
                args,
                nullsafe: false,
                ..
            } if args.is_empty() => {
                let base = self.place_key(recv)?;
                Some(format!("{base}->{}()", self.interner.resolve(*m)))
            }
            _ => None,
        }
    }

    // -- The flow engine (advance env + record per-expression types) -------
    //
    // This is the single statement walker. It advances `self.vars` AND records
    // each expression's inferred type into `map` at its *current* (narrowed) flow
    // point — recording each node as flow reaches it is what types expressions
    // inside `if`/`elseif`/`else`/loop bodies against the narrowed environment
    // (e.g. `$node->name` after `if ($node instanceof Stmt\Namespace_)`), which a
    // single up-front walk could not do. The `exec_*` methods above are thin
    // wrappers that run this engine with a throw-away map when only the resulting
    // environment is wanted.

    /// Record (and flow through) every statement in `stmts`.
    pub fn record_block(&mut self, stmts: &[Stmt], map: &mut RecMap) {
        for s in stmts {
            self.record_stmt(s, map);
        }
    }

    /// Record every sub-expression of `e` at the current environment, applying
    /// **intra-expression narrowing** through `&&`/`||`: the right operand of
    /// `a && b` is recorded under `a`'s truthy facts, and of `a || b` under `a`'s
    /// false facts (PHP short-circuits, so the right side is reached only then).
    /// This is what types `$x->m()` correctly in `$x instanceof Y && $x->m()`.
    fn rec_here(&mut self, e: &Expr, map: &mut RecMap) {
        map.insert(span_key(e), self.infer(e));
        match &e.kind {
            ExprKind::Paren(inner) => self.rec_here(inner, map),
            ExprKind::Unary { expr, .. } | ExprKind::Cast { expr, .. } => self.rec_here(expr, map),
            ExprKind::Clone(x)
            | ExprKind::Print(x)
            | ExprKind::Throw(x)
            | ExprKind::ErrorSuppress(x)
            | ExprKind::YieldFrom(x)
            | ExprKind::Eval(x)
            | ExprKind::Empty(x)
            | ExprKind::PreInc(x)
            | ExprKind::PreDec(x)
            | ExprKind::PostInc(x)
            | ExprKind::PostDec(x) => self.rec_here(x, map),
            ExprKind::Prop { base, name, .. } => {
                self.rec_here(base, map);
                self.rec_member(name, map);
            }
            ExprKind::StaticProp { class, name } | ExprKind::ClassConst { class, name } => {
                self.rec_here(class, map);
                self.rec_member(name, map);
            }
            ExprKind::Index { base, index } => {
                self.rec_here(base, map);
                if let Some(i) = index {
                    self.rec_here(i, map);
                }
            }
            ExprKind::Instanceof { expr, .. } => self.rec_here(expr, map),
            // `a && b` records `b` under `a`'s truthy facts (short-circuit); `a || b`
            // under `a`'s false facts. Other binary ops just recurse both sides.
            ExprKind::Binary {
                op: BinOp::BoolAnd | BinOp::LogicalAnd,
                lhs,
                rhs,
            } => {
                self.rec_here(lhs, map);
                self.rec_under(lhs, true, rhs, map);
            }
            ExprKind::Binary {
                op: BinOp::BoolOr | BinOp::LogicalOr,
                lhs,
                rhs,
            } => {
                self.rec_here(lhs, map);
                self.rec_under(lhs, false, rhs, map);
            }
            ExprKind::Binary { lhs, rhs, .. }
            | ExprKind::Assign { target: lhs, rhs }
            | ExprKind::AssignOp {
                target: lhs, rhs, ..
            }
            | ExprKind::AssignRef { target: lhs, rhs }
            | ExprKind::Coalesce { lhs, rhs } => {
                self.rec_here(lhs, map);
                self.rec_here(rhs, map);
            }
            // `cond ? then : els` — `then` sees `cond`'s truthy facts, `els` its
            // false facts (`$x->p ? f($x->p) : ''`, `null !== $x->d ? f($x->d) : ''`).
            ExprKind::Ternary { cond, then, els } => {
                self.rec_here(cond, map);
                if let Some(t) = then {
                    self.rec_under(cond, true, t, map);
                }
                self.rec_under(cond, false, els, map);
            }
            ExprKind::Call { callee, args } => {
                self.rec_here(callee, map);
                self.rec_args(args, map);
                self.rec_builtin_callback_args(callee, args, map);
            }
            ExprKind::MethodCall {
                recv, method, args, ..
            } => {
                self.rec_here(recv, map);
                self.rec_member(method, map);
                self.rec_args(args, map);
                self.rec_collection_callback_args(recv, method, args, map);
            }
            ExprKind::StaticCall {
                class,
                method,
                args,
            } => {
                self.rec_here(class, map);
                self.rec_member(method, map);
                self.rec_args(args, map);
            }
            ExprKind::New { class, args } => {
                self.rec_here(class, map);
                self.rec_args(args, map);
            }
            ExprKind::NewAnon { args, .. } => self.rec_args(args, map),
            ExprKind::Array { items, .. } => {
                for it in items {
                    if let Some(k) = &it.key {
                        self.rec_here(k, map);
                    }
                    if let Some(v) = &it.value {
                        self.rec_here(v, map);
                    }
                }
            }
            ExprKind::Match { subject, arms } => {
                self.rec_here(subject, map);
                for arm in arms {
                    if let Some(conds) = &arm.conds {
                        for c in conds {
                            self.rec_here(c, map);
                        }
                    }
                    self.rec_here(&arm.body, map);
                }
            }
            ExprKind::Isset(es) => {
                for x in es {
                    self.rec_here(x, map);
                }
            }
            ExprKind::Interpolated(parts) | ExprKind::ShellExec(parts) => {
                for p in parts {
                    self.rec_here(p, map);
                }
            }
            ExprKind::Closure(c) => self.rec_closure(c, &[], map),
            ExprKind::ArrowFn(a) => self.rec_arrow(a, &[], map),
            ExprKind::Yield { key, value } => {
                if let Some(key) = key {
                    self.rec_here(key, map);
                }
                if let Some(value) = value {
                    self.rec_here(value, map);
                }
            }
            // Leaves and yield-ish forms — nothing more to record at this scope
            // (`e` itself is already recorded above).
            _ => {}
        }
    }

    fn rec_closure(&self, c: &ClosureExpr, inferred_params: &[Type], map: &mut RecMap) {
        let mut vars = Env::new();
        let mut callables = CallableEnv::new();
        for u in &c.uses {
            let name = self.interner.resolve(u.name).to_string();
            let ty = self.vars.get(&name).cloned().unwrap_or(Type::Mixed);
            vars.insert(name, ty);
            if let Some(alias) = self.callables.get(self.interner.resolve(u.name)) {
                callables.insert(self.interner.resolve(u.name).to_string(), alias.clone());
            }
        }
        self.seed_ast_params(&mut vars, &c.params, inferred_params);
        let class = (!c.is_static).then(|| self.class.clone()).flatten();
        let generator_send = c.return_type.as_ref().and_then(|t| {
            crate::generator_send_type(&php_reflect::resolve_ast_type(self.scope, t))
        });
        self.record_child_block(class, vars, callables, generator_send, &c.body, map);
    }

    fn rec_arrow(&self, a: &ArrowFn, inferred_params: &[Type], map: &mut RecMap) {
        let mut vars = self.vars.clone();
        if a.is_static {
            strip_this_vars(&mut vars);
        }
        self.seed_ast_params(&mut vars, &a.params, inferred_params);
        let class = (!a.is_static).then(|| self.class.clone()).flatten();
        let generator_send = a.return_type.as_ref().and_then(|t| {
            crate::generator_send_type(&php_reflect::resolve_ast_type(self.scope, t))
        });
        self.record_child_expr(
            class,
            vars,
            self.callables.clone(),
            generator_send,
            &a.body,
            map,
        );
    }

    fn seed_ast_params(&self, vars: &mut Env, params: &[Param], inferred: &[Type]) {
        for (i, p) in params.iter().enumerate() {
            let name = self.interner.resolve(p.name).to_string();
            vars.insert(
                name,
                self.ast_param_local_type(p, &inferred[i.min(inferred.len())..]),
            );
        }
    }

    fn ast_param_local_type(&self, p: &Param, inferred: &[Type]) -> Type {
        if self.native {
            return if p.variadic {
                Type::Array(None)
            } else {
                p.ty.as_ref()
                    .map(|t| php_reflect::resolve_ast_type(self.scope, t))
                    .unwrap_or_else(|| inferred.first().cloned().unwrap_or(Type::Mixed))
            };
        }
        if let Some(ast_ty) =
            p.ty.as_ref()
                .map(|t| php_reflect::resolve_ast_type(self.scope, t))
        {
            if p.variadic {
                Type::List(Box::new(ast_ty))
            } else {
                ast_ty
            }
        } else if p.variadic {
            let item = if inferred.is_empty() {
                Type::Mixed
            } else {
                Type::union(inferred.to_vec())
            };
            Type::List(Box::new(item))
        } else {
            inferred.first().cloned().unwrap_or(Type::Mixed)
        }
    }

    fn rec_builtin_callback_args(&self, callee: &Expr, args: &[Arg], map: &mut RecMap) {
        if !args_are_plain_positional(args) {
            return;
        }
        let ExprKind::Name(name) = &callee.kind else {
            return;
        };
        let Some(func) = self.function_reflection(name).filter(|f| f.builtin) else {
            return;
        };
        let fname = last_segment(&func.fqn).to_ascii_lowercase();
        match fname.as_str() {
            "array_map" => {
                let Some(callback) = args.first() else { return };
                let inferred: Vec<Type> = args
                    .iter()
                    .skip(1)
                    .map(|a| self.arg_array_value_type(a))
                    .collect();
                self.rec_callback_arg(callback, inferred, map);
            }
            "array_filter" => {
                let (Some(array), Some(callback)) = (args.first(), args.get(1)) else {
                    return;
                };
                let value = self.arg_array_value_type(array);
                let key = self.arg_array_key_type(array);
                let Some(inferred) = array_filter_callback_params(args, value, key) else {
                    return;
                };
                self.rec_callback_arg(callback, inferred, map);
            }
            "array_walk" => {
                let (Some(array), Some(callback)) = (args.first(), args.get(1)) else {
                    return;
                };
                let mut inferred = vec![
                    self.arg_array_value_type(array),
                    self.arg_array_key_type(array),
                ];
                if let Some(user_arg) = args.get(2) {
                    inferred.push(self.infer(&user_arg.value));
                }
                self.rec_callback_arg(callback, inferred, map);
            }
            "usort" | "uasort" => {
                let (Some(array), Some(callback)) = (args.first(), args.get(1)) else {
                    return;
                };
                let value = self.arg_array_value_type(array);
                self.rec_callback_arg(callback, vec![value.clone(), value], map);
            }
            "uksort" => {
                let (Some(array), Some(callback)) = (args.first(), args.get(1)) else {
                    return;
                };
                let key = self.arg_array_key_type(array);
                self.rec_callback_arg(callback, vec![key.clone(), key], map);
            }
            "preg_replace_callback" => {
                let Some(callback) = args.get(1) else { return };
                if !preg_replace_callback_flags_are_plain(args) {
                    return;
                }
                self.rec_callback_arg(callback, vec![preg_match_array_type()], map);
            }
            _ => {}
        }
    }

    fn rec_collection_callback_args(
        &self,
        recv: &Expr,
        method: &php_ast::MemberName,
        args: &[Arg],
        map: &mut RecMap,
    ) {
        if !args_are_plain_positional(args) {
            return;
        }
        let php_ast::MemberName::Ident(sym) = method else {
            return;
        };
        let method_name = self.interner.resolve(*sym);
        let Some(kind) = collection_method(method_name) else {
            return;
        };
        let recv_ty = self.infer(recv);
        let Some(inferred) = self.collection_callback_params(&recv_ty, kind, args) else {
            return;
        };
        let Some(callback) = args.first() else { return };
        self.rec_callback_arg(callback, inferred, map);
    }

    fn rec_callback_arg(&self, arg: &Arg, inferred: Vec<Type>, map: &mut RecMap) {
        match &peel_paren(&arg.value).kind {
            ExprKind::Closure(c) => self.rec_closure(c, &inferred, map),
            ExprKind::ArrowFn(a) => self.rec_arrow(a, &inferred, map),
            ExprKind::Variable(sym) => {
                let name = self.interner.resolve(*sym);
                if let Some(alias) = self.callables.get(name) {
                    self.rec_callable_alias(alias, &inferred, map);
                }
            }
            _ => {}
        }
    }

    fn rec_callable_alias(&self, alias: &CallableAlias, inferred: &[Type], map: &mut RecMap) {
        match alias {
            CallableAlias::Closure {
                expr,
                vars,
                callables,
                class,
                ..
            } => {
                let mut vars = vars.clone();
                self.seed_ast_params(&mut vars, &expr.params, inferred);
                let generator_send = expr.return_type.as_ref().and_then(|t| {
                    crate::generator_send_type(&php_reflect::resolve_ast_type(self.scope, t))
                });
                self.record_child_block(
                    class.clone(),
                    vars,
                    callables.clone(),
                    generator_send,
                    &expr.body,
                    map,
                );
            }
            CallableAlias::Arrow {
                expr,
                vars,
                callables,
                class,
                ..
            } => {
                let mut vars = vars.clone();
                self.seed_ast_params(&mut vars, &expr.params, inferred);
                let generator_send = expr.return_type.as_ref().and_then(|t| {
                    crate::generator_send_type(&php_reflect::resolve_ast_type(self.scope, t))
                });
                self.record_child_expr(
                    class.clone(),
                    vars,
                    callables.clone(),
                    generator_send,
                    &expr.body,
                    map,
                );
            }
        }
    }

    fn arg_array_value_type(&self, arg: &Arg) -> Type {
        arrays::array_value_type(&self.infer(&arg.value)).unwrap_or(Type::Mixed)
    }

    fn arg_array_key_type(&self, arg: &Arg) -> Type {
        arrays::array_key_type(&self.infer(&arg.value)).unwrap_or(Type::Mixed)
    }

    fn record_child_block(
        &self,
        class: Option<String>,
        vars: Env,
        callables: CallableEnv,
        generator_send: Option<Type>,
        body: &[Stmt],
        map: &mut RecMap,
    ) {
        let mut child = TypeCtx::new(self.index, self.scope, self.interner);
        child.class = class;
        child.vars = vars;
        child.callables = callables;
        child.depth = self.depth;
        child.native = self.native;
        child.generator_send = generator_send;
        child.record_block(body, map);
    }

    fn record_child_expr(
        &self,
        class: Option<String>,
        vars: Env,
        callables: CallableEnv,
        generator_send: Option<Type>,
        e: &Expr,
        map: &mut RecMap,
    ) {
        let mut child = TypeCtx::new(self.index, self.scope, self.interner);
        child.class = class;
        child.vars = vars;
        child.callables = callables;
        child.depth = self.depth;
        child.native = self.native;
        child.generator_send = generator_send;
        child.rec_here(e, map);
    }

    fn rec_args(&mut self, args: &[php_ast::Arg], map: &mut RecMap) {
        for a in args {
            self.rec_here(&a.value, map);
        }
    }

    /// Record a dynamic member name expression (`$o->{$x}`, `A::{$x}`).
    fn rec_member(&mut self, m: &php_ast::MemberName, map: &mut RecMap) {
        if let php_ast::MemberName::Expr(e) = m {
            self.rec_here(e, map);
        }
    }

    /// Record `rhs` with the facts implied by `gate` evaluating to `truthy`
    /// temporarily applied, then restore the environment.
    fn rec_under(&mut self, gate: &Expr, truthy: bool, rhs: &Expr, map: &mut RecMap) {
        let facts = self.narrow_facts(gate, truthy);
        let saved = self.vars.clone();
        self.apply_facts(&facts);
        self.rec_here(rhs, map);
        self.vars = saved;
    }

    /// Honour an inline `/** @var T $x */` on a statement: narrow `$x` to the
    /// annotated type for this statement onward (phpstan does the same). Resolves
    /// the PHPDoc type in the current scope; unnamed/unresolvable `@var`s are
    /// ignored. The type set is the narrower of the annotation and the current type
    /// so a bogus widening annotation can't introduce false positives.
    fn apply_inline_var(&mut self, s: &Stmt) {
        let Some(doc) = &s.doc else { return };
        for v in php_phpdoc::parse(doc).vars {
            let (Some(name), Some(dt)) = (v.name, v.ty) else {
                continue;
            };
            let t = php_reflect::resolve_doc_type(self.scope, &[], &dt);
            let cur = self.vars.get(&name).cloned().unwrap_or(Type::Mixed);
            let narrowed = narrow_to(&cur, &t, self.index);
            self.callables.remove(&name);
            self.vars.insert(name, narrowed);
        }
    }

    fn unnamed_inline_var_type(&self, s: &Stmt) -> Option<Type> {
        let doc = s.doc.as_ref()?;
        php_phpdoc::parse(doc)
            .vars
            .into_iter()
            .find_map(|v| match (v.name, v.ty) {
                (None, Some(dt)) => Some(php_reflect::resolve_doc_type(self.scope, &[], &dt)),
                _ => None,
            })
    }

    /// `assert($cond)` narrows the environment by the facts `$cond` implies (it
    /// holds for all following code, like a guard that always passes) — e.g.
    /// `assert($x !== false)` strips `false` from `$x`. Reuses the condition
    /// narrowing; only sound refinements are applied.
    fn apply_assert(&mut self, e: &Expr) {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let ExprKind::Name(n) = &callee.kind else {
            return;
        };
        if !last_segment(&n.text).eq_ignore_ascii_case("assert") {
            return;
        }
        let Some(cond) = args.first() else { return };
        let facts = self.narrow_facts(&cond.value, true);
        self.apply_facts(&facts);
    }

    fn record_stmt(&mut self, s: &Stmt, map: &mut RecMap) {
        self.apply_inline_var(s);
        match &s.kind {
            StmtKind::Expr(e) => {
                self.rec_here(e, map);
                self.apply_expr(e);
                if let Some(t) = self.unnamed_inline_var_type(s) {
                    self.bind_unnamed_inline_assignment(e, &t, map);
                }
                self.apply_inline_var(s);
                self.apply_assert(e);
            }
            StmtKind::Echo(es) => {
                for e in es {
                    self.rec_here(e, map);
                    self.apply_expr(e);
                }
                self.apply_inline_var(s);
            }
            StmtKind::Return(Some(e)) => {
                self.rec_here(e, map);
                if let Some(t) = self.unnamed_inline_var_type(s) {
                    map.insert(span_key(e), t);
                }
                self.apply_expr(e);
                self.apply_inline_var(s);
            }
            StmtKind::Block(b) => self.record_block(b, map),
            StmtKind::If {
                cond,
                then,
                elseifs,
                els,
            } => {
                self.rec_here(cond, map);
                self.apply_expr(cond);
                self.record_if(cond, then, elseifs, els.as_deref(), map);
            }
            StmtKind::While { cond, body } => {
                self.rec_here(cond, map);
                self.apply_expr(cond);
                let entry_facts = self.narrow_facts(cond, true);
                self.record_maybe_loop(body, map, &entry_facts);
            }
            StmtKind::DoWhile { body, cond } => {
                self.record_definite_loop(body, map, &[]);
                self.rec_here(cond, map);
                self.apply_expr(cond);
            }
            StmtKind::For {
                init,
                cond,
                update,
                body,
            } => {
                for e in init {
                    self.rec_here(e, map);
                    self.apply_expr(e);
                }
                // A `for` whose condition is provably true after `init` runs at
                // least once, so its body's assignments are definite (post-loop env
                // = post-body, not merged with the pre-loop env). PHP uses the *last*
                // condition expression; check it before `update` advances the loop var.
                let definite = cond
                    .last()
                    .is_some_and(|c| crate::returns::static_truth(self, c) == Some(true));
                let entry_facts = cond
                    .last()
                    .map(|c| self.narrow_facts(c, true))
                    .unwrap_or_default();
                for e in cond.iter().chain(update) {
                    self.rec_here(e, map);
                    self.apply_expr(e);
                }
                if definite {
                    self.record_definite_loop(body, map, &entry_facts);
                } else {
                    self.record_maybe_loop(body, map, &entry_facts);
                }
            }
            StmtKind::Foreach {
                subject,
                key,
                value,
                body,
                ..
            } => {
                self.record_foreach(subject, key.as_ref(), value, body, map);
            }
            StmtKind::Switch { subject, cases } => {
                self.rec_here(subject, map);
                self.apply_expr(subject);
                let base = self.flow_state();
                let mut envs = vec![base.clone()];
                for case in cases {
                    self.set_flow_state(base.clone());
                    if let Some(t) = &case.test {
                        self.rec_here(t, map);
                    }
                    self.record_block(&case.body, map);
                    envs.push(self.take_flow_state());
                }
                self.set_flow_state(merge_states(envs));
            }
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                self.record_try(body, catches, finally.as_deref(), map);
            }
            // Other statements (global/unset/static/declare/const/return;/…) carry
            // no narrowing-sensitive branch bodies and bind no simple-variable types
            // the flow tracks, so just record their expressions flatly at the
            // current environment (no environment transition to apply).
            _ => {
                php_ast::walk::for_each_expr_in_scope(s, &mut |e| {
                    map.insert(span_key(e), self.infer(e));
                });
            }
        }
    }

    fn bind_unnamed_inline_assignment(&mut self, e: &Expr, ty: &Type, map: &mut RecMap) {
        let (ExprKind::Assign { target, .. } | ExprKind::AssignRef { target, .. }) = &e.kind else {
            return;
        };
        self.bind_target(target, ty);
        map.insert(span_key(target), ty.clone());
        map.insert(span_key(e), ty.clone());
    }

    fn record_if(
        &mut self,
        cond: &Expr,
        then: &Stmt,
        elseifs: &[php_ast::ElseIf],
        els: Option<&Stmt>,
        map: &mut RecMap,
    ) {
        let base = self.flow_state();
        let mut envs: Vec<FlowState> = Vec::new();

        // Facts resolve against the branch-entry env (`base`); compute before the
        // then-branch mutates `self.vars`. (Mirrors `exec_if`.)
        let then_facts = self.narrow_facts(cond, true);
        let mut else_facts = self.narrow_facts(cond, false);

        self.set_flow_state(base.clone());
        self.apply_facts(&then_facts);
        self.record_stmt(then, map);
        if !always_terminates(then) {
            envs.push(self.take_flow_state());
        }

        for ei in elseifs {
            self.set_flow_state(base.clone());
            self.apply_facts(&else_facts);
            let pos = self.narrow_facts(&ei.cond, true);
            let neg = self.narrow_facts(&ei.cond, false);
            self.rec_here(&ei.cond, map);
            self.apply_facts(&pos);
            self.apply_expr(&ei.cond);
            self.record_stmt(&ei.body, map);
            if !always_terminates(&ei.body) {
                envs.push(self.take_flow_state());
            }
            else_facts.extend(neg);
        }

        match els {
            Some(e) => {
                self.set_flow_state(base.clone());
                self.apply_facts(&else_facts);
                self.record_stmt(e, map);
                if !always_terminates(e) {
                    envs.push(self.take_flow_state());
                }
            }
            None => {
                let mut fall = base.0.clone();
                apply_facts_to(&mut fall, &else_facts, self.index);
                envs.push((fall, base.1.clone()));
            }
        }

        if envs.is_empty() {
            self.set_flow_state(base);
        } else {
            self.set_flow_state(merge_states(envs));
        }
    }

    fn record_maybe_loop(&mut self, body: &Stmt, map: &mut RecMap, entry_facts: &[Fact]) {
        self.record_loop(body, map, entry_facts, true);
    }

    fn record_definite_loop(&mut self, body: &Stmt, map: &mut RecMap, entry_facts: &[Fact]) {
        self.record_loop(body, map, entry_facts, false);
    }

    fn record_loop(&mut self, body: &Stmt, map: &mut RecMap, entry_facts: &[Fact], may_skip: bool) {
        self.widen_loop_assignments(body);
        let base = self.flow_state();
        let mut current = base.clone();
        for _ in 0..LOOP_FIXPOINT_LIMIT {
            self.set_flow_state(current.clone());
            self.apply_facts(entry_facts);
            self.record_stmt(body, map);
            let after = widen_loop_state(self.take_flow_state());
            let next = if may_skip {
                merge_states(vec![base.clone(), after])
            } else {
                after
            };
            if flow_state_same(&current, &next) {
                self.set_flow_state(next);
                return;
            }
            current = next;
        }
        self.set_flow_state(current);
    }

    /// Before recording a loop body, generalize the *literal* type of any simple
    /// variable assigned inside it. A flag set `false` before the loop and `true`
    /// (or vice-versa) within it is loop-carried, so a use earlier in source order
    /// may see either value across iterations — treating it as the constant literal
    /// `false` would yield spurious `if.alwaysFalse`. We don't iterate to fixpoint,
    /// so this single widening stands in for it (only literal scalars are touched).
    fn widen_loop_assignments(&mut self, body: &Stmt) {
        let interner = self.interner;
        let mut assigned: HashSet<String> = HashSet::new();
        php_ast::walk::for_each_expr_in_scope(body, &mut |e: &Expr| {
            let target = match &e.kind {
                ExprKind::Assign { target, .. }
                | ExprKind::AssignRef { target, .. }
                | ExprKind::AssignOp { target, .. } => target,
                _ => return,
            };
            if let ExprKind::Variable(sym) = &target.kind {
                assigned.insert(interner.resolve(*sym).to_string());
            }
        });
        for name in assigned {
            if let Some(t) = self.vars.get(&name) {
                let g = generalize_literal(t);
                if &g != t {
                    self.vars.insert(name.clone(), g);
                }
            }
            self.callables.remove(&name);
        }
    }

    fn record_foreach(
        &mut self,
        subject: &Expr,
        key: Option<&Expr>,
        value: &Expr,
        body: &Stmt,
        map: &mut RecMap,
    ) {
        self.rec_here(subject, map);
        let subj_ty = self.apply_expr(subject);
        let (k, v) = self
            .index
            .iterable_key_value_on_type(&subj_ty)
            .unwrap_or_else(|| crate::arrays::iter_key_value(&subj_ty));
        self.widen_loop_assignments(body);
        let base = self.flow_state();
        let mut current = base.clone();
        for _ in 0..LOOP_FIXPOINT_LIMIT {
            self.set_flow_state(current.clone());
            if let Some(key) = key {
                self.bind_target(key, &k);
                self.rec_here(key, map);
            }
            self.bind_target(value, &v);
            self.rec_here(value, map);
            self.record_stmt(body, map);
            let after = widen_loop_state(self.take_flow_state());
            let next = merge_states(vec![base.clone(), after]);
            if flow_state_same(&current, &next) {
                self.set_flow_state(next);
                return;
            }
            current = next;
        }
        self.set_flow_state(current);
    }

    fn record_try(
        &mut self,
        body: &[Stmt],
        catches: &[php_ast::Catch],
        finally: Option<&[Stmt]>,
        map: &mut RecMap,
    ) {
        let base = self.flow_state();
        let mut exits = Vec::new();

        self.set_flow_state(base.clone());
        self.record_block(body, map);
        if !block_always_terminates(body) {
            exits.push(self.take_flow_state());
        }

        for catch in catches {
            self.set_flow_state(base.clone());
            if let Some(var) = catch.var {
                let name = self.interner.resolve(var).to_string();
                let ty = self.catch_type(catch);
                self.vars.insert(name.clone(), ty);
                self.callables.remove(&name);
            }
            self.record_block(&catch.body, map);
            if !block_always_terminates(&catch.body) {
                exits.push(self.take_flow_state());
            }
        }

        let merged = if exits.is_empty() {
            base.clone()
        } else {
            merge_states(exits)
        };

        if let Some(finally) = finally {
            self.set_flow_state(merged);
            self.record_block(finally, map);
            if block_always_terminates(finally) {
                self.set_flow_state(base);
            }
        } else {
            self.set_flow_state(merged);
        }
    }

    fn catch_type(&self, catch: &php_ast::Catch) -> Type {
        let types: Vec<Type> = catch
            .types
            .iter()
            .filter_map(|n| self.name_class_type(n))
            .collect();
        if types.len() == catch.types.len() && !types.is_empty() {
            Type::union(types)
        } else {
            Type::Mixed
        }
    }

    fn name_class_type(&self, n: &Name) -> Option<Type> {
        match self.scope.resolve_class(n) {
            php_resolve::Resolution::Fqn(fqn) => Some(Type::Named { fqn: fqn.into(), args: vec![] }),
            php_resolve::Resolution::LateStatic(s) => match s.as_str() {
                "self" => self.self_type(),
                "static" => Some(Type::StaticType),
                _ => self.parent_type(),
            },
            php_resolve::Resolution::BuiltinType(_) | php_resolve::Resolution::Fallback { .. } => {
                None
            }
        }
    }

    fn flow_state(&self) -> FlowState {
        (self.vars.clone(), self.callables.clone())
    }

    fn set_flow_state(&mut self, state: FlowState) {
        self.vars = state.0;
        self.callables = state.1;
    }

    fn take_flow_state(&mut self) -> FlowState {
        (
            std::mem::take(&mut self.vars),
            std::mem::take(&mut self.callables),
        )
    }
}

/// Span key for the type map: an expression's `(start, end)` byte range.
fn span_key(e: &Expr) -> (u32, u32) {
    let r = e.span.range();
    (r.start as u32, r.end as u32)
}

fn args_are_plain_positional(args: &[Arg]) -> bool {
    args.iter()
        .all(|a| !a.spread && !a.placeholder && a.name.is_none())
}

fn peel_paren(e: &Expr) -> &Expr {
    match &e.kind {
        ExprKind::Paren(inner) => peel_paren(inner),
        _ => e,
    }
}

fn array_filter_callback_params(args: &[Arg], value: Type, key: Type) -> Option<Vec<Type>> {
    match args.get(2).map(|a| &a.value) {
        None => Some(vec![value]),
        Some(mode) => match array_filter_mode(mode)? {
            ArrayFilterMode::Value => Some(vec![value]),
            ArrayFilterMode::Key => Some(vec![key]),
            ArrayFilterMode::Both => Some(vec![value, key]),
        },
    }
}

enum ArrayFilterMode {
    Value,
    Key,
    Both,
}

fn array_filter_mode(e: &Expr) -> Option<ArrayFilterMode> {
    match int_lit(e) {
        Some(0) => return Some(ArrayFilterMode::Value),
        Some(1) => return Some(ArrayFilterMode::Both),
        Some(2) => return Some(ArrayFilterMode::Key),
        Some(_) => return None,
        None => {}
    }
    let ExprKind::Name(n) = &peel_paren(e).kind else {
        return None;
    };
    match global_const_text(&n.text)? {
        "ARRAY_FILTER_USE_BOTH" => Some(ArrayFilterMode::Both),
        "ARRAY_FILTER_USE_KEY" => Some(ArrayFilterMode::Key),
        _ => None,
    }
}

fn global_const_text(text: &str) -> Option<&str> {
    let stripped = text.strip_prefix('\\').unwrap_or(text);
    (!stripped.contains('\\')).then_some(stripped)
}

fn preg_replace_callback_flags_are_plain(args: &[Arg]) -> bool {
    match args.get(5).map(|a| &a.value) {
        None => true,
        Some(flags) => int_lit(flags) == Some(0),
    }
}

fn preg_match_array_type() -> Type {
    Type::Array(Some(Box::new((
        Type::union(vec![Type::Int, Type::String]),
        Type::String,
    ))))
}

fn strip_this_vars(vars: &mut Env) {
    vars.retain(|k, _| k != "this" && !k.starts_with("this->"));
}

/// Apply narrowing facts to an environment in place.
fn apply_facts_to(vars: &mut Env, facts: &[Fact], index: &php_reflect::ReflectionIndex) {
    for (place, t) in facts {
        let cur = vars.get(place).cloned().unwrap_or(Type::Mixed);
        vars.insert(place.clone(), narrow_to(&cur, t, index));
    }
}

/// Refine `cur` with the branch fact `t`, choosing the *narrower* of the two
/// (their intersection, approximated): if `t ⊑ cur` use `t` (the case for
/// `instanceof`/`is_*`/strip facts, where `t` is the computed narrowing — e.g.
/// `mixed|null` stripped to `mixed`, or `Node` narrowed to `ClassMethod`); if
/// instead `cur ⊑ t` keep `cur` (it's already more precise, e.g. an
/// `array<int,string>` past an `is_array` check); otherwise the branch fact wins.
/// Sound either way — both `cur` and `t` hold in the branch.
fn narrow_to(cur: &Type, t: &Type, index: &php_reflect::ReflectionIndex) -> Type {
    match cur {
        Type::Mixed | Type::Unknown(_) => t.clone(),
        _ if crate::is_assignable(index, t, cur) => t.clone(),
        _ if crate::is_assignable(index, cur, t) => cur.clone(),
        _ => t.clone(),
    }
}

/// The narrowed type asserted by a `is_*($x)` type-predicate built-in, if known.
fn predicate_type(fname: &str) -> Option<Type> {
    Some(match fname {
        "is_int" | "is_integer" | "is_long" => Type::Int,
        "is_string" => Type::String,
        "is_bool" => Type::Bool,
        "is_float" | "is_double" => Type::Float,
        "is_array" => Type::Array(None),
        "is_callable" => Type::Callable(None),
        "is_object" => Type::Object,
        "is_iterable" => Type::Iterable(None),
        "is_null" => Type::Null,
        _ => return None, // is_scalar/is_numeric etc. are unions — skip (safe).
    })
}

/// Remove from a *union* the members for which `remove` returns true, used for the
/// negative branch of `is_*`/`instanceof`. Only narrows a union and never to empty:
/// if `cur` is not a union, or removal would drop every member, returns `cur`
/// unchanged (sound under-narrowing — we never assert a place is `never`).
fn subtract_union(cur: &Type, mut remove: impl FnMut(&Type) -> bool) -> Type {
    let Type::Union(parts) = cur else {
        return cur.clone();
    };
    let kept: Vec<Type> = parts.iter().filter(|p| !remove(p)).cloned().collect();
    if kept.is_empty() || kept.len() == parts.len() {
        cur.clone()
    } else {
        Type::union(kept)
    }
}

/// Whether union member `m` is *definitely* of the kind asserted by a type
/// predicate `t` (from [`predicate_type`]) — so `!is_<kind>` removes it. Matches
/// on concrete kind, not lenient assignability, to avoid over-removing.
fn predicate_matches(m: &Type, t: &Type) -> bool {
    use Type::*;
    match t {
        String => matches!(m, String | LiteralString(_) | ClassString(_)),
        Int => matches!(m, Int | LiteralInt(_)),
        Float => matches!(m, Float),
        Bool => matches!(m, Bool | True | False),
        Array(_) => matches!(m, Array(_) | List(_) | Shape { .. }),
        Object => matches!(m, Object | Named { .. } | SelfType | StaticType),
        Iterable(_) => matches!(m, Iterable(_) | Array(_) | List(_) | Shape { .. }),
        Callable(_) => matches!(m, Callable(_)),
        Null => matches!(m, Null),
        _ => false,
    }
}

/// Whether union member `m` is a *confident* subclass of class type `t` — both are
/// indexed classes and the subtype relation holds. Used for `!($x instanceof C)`.
fn confident_subclass(m: &Type, t: &Type, index: &php_reflect::ReflectionIndex) -> bool {
    let (Type::Named { fqn: mf, .. }, Type::Named { fqn: tf, .. }) = (m, t) else {
        return false;
    };
    if mf.eq_ignore_ascii_case(tf) {
        return true;
    }
    index.class(mf).is_some() && index.class(tf).is_some() && index.is_subclass_of(mf, tf)
}

/// The integer value of a literal expression (`5`, `(5)`, `-5`), if any.
fn int_lit(e: &Expr) -> Option<i64> {
    match &e.kind {
        ExprKind::Int(n) => Some(*n),
        ExprKind::Paren(inner) => int_lit(inner),
        ExprKind::Unary {
            op: UnOp::Minus,
            expr,
        } => int_lit(expr).map(|n| n.wrapping_neg()),
        ExprKind::Unary {
            op: UnOp::Plus,
            expr,
        } => int_lit(expr),
        _ => None,
    }
}

/// Swap a comparison operator's operands (`a < b` ⇔ `b > a`).
fn flip_cmp(op: BinOp) -> BinOp {
    match op {
        BinOp::Lt => BinOp::Gt,
        BinOp::Gt => BinOp::Lt,
        BinOp::LtEq => BinOp::GtEq,
        BinOp::GtEq => BinOp::LtEq,
        other => other,
    }
}

/// Logical negation of a comparison operator (`!(a < b)` ⇔ `a >= b`).
fn negate_cmp(op: BinOp) -> BinOp {
    match op {
        BinOp::Lt => BinOp::GtEq,
        BinOp::GtEq => BinOp::Lt,
        BinOp::Gt => BinOp::LtEq,
        BinOp::LtEq => BinOp::Gt,
        other => other,
    }
}

/// Generalize a *literal* scalar type to its base, used to widen a loop-carried
/// variable so it isn't mistaken for a compile-time constant. Non-literal types
/// pass through unchanged.
fn generalize_literal(t: &Type) -> Type {
    match t {
        Type::False | Type::True => Type::Bool,
        Type::LiteralInt(_) => Type::Int,
        Type::LiteralString(_) => Type::String,
        _ => t.clone(),
    }
}

fn widen_loop_state(state: FlowState) -> FlowState {
    let (mut vars, callables) = state;
    for ty in vars.values_mut() {
        *ty = widen_loop_type(ty);
    }
    (vars, callables)
}

fn widen_loop_type(t: &Type) -> Type {
    match t {
        Type::Union(parts) if parts.len() > 8 => {
            let widened = Type::union(parts.iter().map(generalize_literal).collect());
            match &widened {
                Type::Union(parts) if parts.len() > 8 => Type::Mixed,
                _ => widened,
            }
        }
        Type::Nullable(inner) => Type::nullable(widen_loop_type(inner)),
        Type::Array(Some(kv)) => Type::Array(Some(Box::new((
            widen_loop_type(&kv.0),
            widen_loop_type(&kv.1),
        )))),
        Type::Iterable(Some(kv)) => Type::Iterable(Some(Box::new((
            widen_loop_type(&kv.0),
            widen_loop_type(&kv.1),
        )))),
        Type::List(inner) => Type::List(Box::new(widen_loop_type(inner))),
        Type::Named { fqn, args } => Type::Named {
            fqn: fqn.clone(),
            args: args.iter().map(widen_loop_type).collect(),
        },
        Type::Shape { fields, sealed } => Type::Shape {
            fields: fields
                .iter()
                .map(|f| php_types::ShapeField {
                    key: f.key.clone(),
                    optional: f.optional,
                    ty: widen_loop_type(&f.ty),
                })
                .collect(),
            sealed: *sealed,
        },
        _ => t.clone(),
    }
}

fn flow_state_same(a: &FlowState, b: &FlowState) -> bool {
    a.0 == b.0 && callable_env_same(&a.1, &b.1)
}

fn callable_env_same(a: &CallableEnv, b: &CallableEnv) -> bool {
    if a.len() != b.len() {
        return false;
    }
    a.iter()
        .all(|(name, alias)| b.get(name).is_some_and(|other| other.id() == alias.id()))
}

/// The last `\`-separated segment of a (possibly-qualified) name.
fn last_segment(name: &str) -> &str {
    name.rsplit('\\').next().unwrap_or(name)
}

/// Does executing `s` always leave the current block (so its environment never
/// flows past it)? Conservative — only unconditional terminators count.
fn always_terminates(s: &Stmt) -> bool {
    match &s.kind {
        StmtKind::Return(_) | StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Goto(_) => {
            true
        }
        StmtKind::Expr(e) => matches!(&e.kind, ExprKind::Throw(_) | ExprKind::Exit(_)),
        StmtKind::Block(b) => b.last().is_some_and(always_terminates),
        StmtKind::If {
            then,
            elseifs,
            els: Some(els),
            ..
        } => {
            always_terminates(then)
                && elseifs.iter().all(|ei| always_terminates(&ei.body))
                && always_terminates(els)
        }
        _ => false,
    }
}

fn block_always_terminates(stmts: &[Stmt]) -> bool {
    stmts.last().is_some_and(always_terminates)
}

/// Merge several branch environments: a variable's merged type is the union of
/// its type in each branch (absent in a branch ⇒ `mixed`, i.e. possibly unset).
fn merge(envs: Vec<Env>) -> Env {
    if envs.len() == 1 {
        return envs.into_iter().next().unwrap();
    }
    let mut keys: Vec<String> = Vec::new();
    for env in &envs {
        for k in env.keys() {
            if !keys.contains(k) {
                keys.push(k.clone());
            }
        }
    }
    let mut out = Env::new();
    for k in keys {
        let parts: Vec<Type> = envs
            .iter()
            .map(|e| e.get(&k).cloned().unwrap_or(Type::Mixed))
            .collect();
        out.insert(k, Type::union(parts));
    }
    out
}

fn merge_states(states: Vec<FlowState>) -> FlowState {
    if states.len() == 1 {
        return states.into_iter().next().unwrap();
    }
    let vars = merge(states.iter().map(|(vars, _)| vars.clone()).collect());
    let mut callables = CallableEnv::new();
    let Some((_, first)) = states.first() else {
        return (vars, callables);
    };
    for (name, alias) in first {
        if states
            .iter()
            .all(|(_, env)| env.get(name).is_some_and(|other| other.id() == alias.id()))
        {
            callables.insert(name.clone(), alias.clone());
        }
    }
    (vars, callables)
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_reflect::ReflectionIndex;
    use php_resolve::Scope;

    /// Parse a function body, run flow analysis seeded from its params, and
    /// return the end-of-body type of variable `$var`.
    fn var_after(src: &str, var: &str) -> String {
        let full = format!("<?php {src}");
        let r = php_parser::parse(&full);
        assert!(!r.has_errors(), "parse errors in: {src}");
        let mut index = ReflectionIndex::new();
        index.add_file(&r.program, &r.interner);
        let scope = Scope::global();
        let mut ctx = TypeCtx::new(&index, &scope, &r.interner);
        // Find the first function and analyse its body.
        let f = r.program.stmts.iter().find_map(|s| match &s.kind {
            StmtKind::Function(f) => Some(f),
            _ => None,
        });
        match f {
            Some(f) => ctx.analyze_function_body(f),
            None => ctx.exec_block(&r.program.stmts),
        }
        ctx.vars
            .get(var)
            .map(|t| t.to_string())
            .unwrap_or_else(|| "<unset>".into())
    }

    #[test]
    fn simple_assignment_chain() {
        assert_eq!(var_after("$x = 1; $y = $x + 2;", "y"), "int");
        assert_eq!(var_after("$x = 'a' . 'b';", "x"), "string");
        assert_eq!(var_after("$a = $b = 5;", "a"), "5");
        assert_eq!(var_after("$a = $b = 5;", "b"), "5");
    }

    #[test]
    fn reassignment_updates_type() {
        assert_eq!(
            var_after("$x = 1; $x = 'now a string';", "x"),
            "'now a string'"
        );
    }

    #[test]
    fn compound_assignment() {
        assert_eq!(var_after("$x = 1; $x += 2;", "x"), "int");
        assert_eq!(var_after("$s = 'a'; $s .= 'b';", "s"), "string");
    }

    #[test]
    fn params_seed_the_environment() {
        assert_eq!(var_after("function f(int $n) { $m = $n + 1; }", "n"), "int");
        assert_eq!(var_after("function f(int $n) { $m = $n + 1; }", "m"), "int");
        assert_eq!(
            var_after("function f(string $s = 'x') { $t = $s; }", "t"),
            "string"
        );
    }

    #[test]
    fn foreach_value_type_from_typed_array() {
        // Seed via a @param generic so the element type is known.
        let src = r#"
            /** @param array<int, string> $a */
            function f(array $a) {
                foreach ($a as $v) { $last = $v; }
            }
        "#;
        // Inside the loop $v is string; after the loop it merges with "unset"
        // (mixed) because the loop may not run (pre-loop env merged first).
        assert_eq!(var_after(src, "v"), "mixed|string");
        assert_eq!(var_after(src, "last"), "mixed|string");
    }

    #[test]
    fn if_else_merges_branch_types() {
        let src = r#"
            function f(bool $c) {
                if ($c) { $x = 1; } else { $x = 'two'; }
            }
        "#;
        assert_eq!(var_after(src, "x"), "1|'two'");
    }

    // --- M-T9 condition narrowing -----------------------------------------

    #[test]
    fn null_guard_strips_null_on_fall_through() {
        // After an early-return null guard, $x is non-null in the continuation.
        let src = "function f(?int $x) { if ($x === null) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "int");
    }

    #[test]
    fn not_null_guard_strips_null() {
        let src = "function f(?string $x) { if ($x === null) { return; } $z = $x; }";
        assert_eq!(var_after(src, "z"), "string");
    }

    #[test]
    fn truthy_guard_strips_null() {
        let src = "function f(?int $x) { if (!$x) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "int");
    }

    #[test]
    fn is_int_predicate_narrows() {
        let src = "function f($x) { if (!is_int($x)) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "int");
    }

    #[test]
    fn instanceof_guard_narrows_to_class() {
        let src = "function f($x) { if (!($x instanceof Foo)) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "Foo");
    }

    #[test]
    fn instanceof_then_branch_narrows() {
        // No early return: the then-branch sees the narrowed type.
        let src = "function f($x) { $y = 0; if ($x instanceof Foo) { $y = $x; } }";
        // then: $y = Foo; fall-through: $y = int(0). Merged.
        assert_eq!(var_after(src, "y"), "Foo|0");
    }

    #[test]
    fn lower_bound_guard_narrows_to_int_range() {
        // After `if ($n < 2) return;`, `$n` is `int<2, max>`.
        let src = "function f(int $n) { if ($n < 2) { return; } $y = $n; }";
        assert_eq!(var_after(src, "y"), "int<2, max>");
    }

    #[test]
    fn definite_for_loop_makes_body_assignment_definite() {
        // `$n >= 2` ⇒ `for ($i=1; $i<$n; …)` runs ≥1 ⇒ `$x` is the body's value, not
        // merged with the pre-loop `0`.
        let src = "function f(int $n) { if ($n < 2) { return; } $x = 0; for ($i = 1; $i < $n; $i++) { $x = 'str'; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "'str'");
    }

    #[test]
    fn while_loop_literal_flag_widens_to_bool() {
        let src = "function f(bool $c) { $x = false; while ($c) { $x = true; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "bool");
    }

    #[test]
    fn do_while_body_assignment_is_definite() {
        let src = "function f(bool $c) { do { $x = 'ran'; } while ($c); $y = $x; }";
        assert_eq!(var_after(src, "y"), "'ran'");
    }

    #[test]
    fn negative_is_string_subtracts_from_union() {
        // The else-branch of `is_string($x)` removes the `string` arm of a union.
        let src = "function f(string|int $x) { if (is_string($x)) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "int");
    }

    #[test]
    fn negative_is_string_on_mixed_stays_mixed() {
        let src = "function f($x) { if (is_string($x)) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "mixed");
    }

    #[test]
    fn negative_is_array_subtracts_from_union() {
        let src = "function f(string|array $x) { if (is_array($x)) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "string");
    }

    #[test]
    fn negative_instanceof_subtracts_indexed_member() {
        // `A|B` minus `A` (both indexed) ⇒ `B` in the else branch.
        let src = "class A {} class B {} function f(A|B $x) { if ($x instanceof A) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "B");
    }

    #[test]
    fn truthy_guard_strips_false_from_union() {
        // `int|false` after `if (!$x) return;` is `int` (truthy strips false too).
        let src = "function f(int|false $x) { if (!$x) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "int");
    }

    #[test]
    fn false_identity_guard_strips_false() {
        // `string|false` after `if (false === $x) return;` is `string`.
        let src = "function f(string|false $x) { if (false === $x) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "string");
    }

    #[test]
    fn truthy_guard_strips_false_and_null() {
        let src = "function f(string|false|null $x) { if (!$x) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "string");
    }

    #[test]
    fn or_instanceof_chain_narrows_to_union() {
        // `$x instanceof A || $x instanceof B` ⇒ $x is A|B in the guarded body.
        let src =
            "function f($x) { if (!($x instanceof A || $x instanceof B)) { return; } $y = $x; }";
        let got = var_after(src, "y");
        assert!(
            got == "A|B" || got == "B|A",
            "expected A|B union, got {got}"
        );
    }

    #[test]
    fn and_composition_narrows_both() {
        let src = "function f(?int $a, ?int $b) { if ($a === null || $b === null) { return; } $x = $a; $y = $b; }";
        assert_eq!(var_after(src, "x"), "int");
        assert_eq!(var_after(src, "y"), "int");
    }

    #[test]
    fn equals_null_branch_is_null() {
        // `!== null` false on the fall-through ⇒ $x is null there.
        let src = "function f(?int $x) { if ($x !== null) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "null");
    }

    #[test]
    fn no_guard_keeps_nullable() {
        // Sanity: without narrowing the nullable survives.
        let src = "function f(?int $x) { $y = $x; }";
        assert_eq!(var_after(src, "y"), "?int");
    }

    #[test]
    fn try_catch_merges_try_and_catch_exits() {
        let src = "class E extends Exception {} function f() { try { $x = 1; } catch (E $e) { $x = 's'; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "1|'s'");
    }

    #[test]
    fn catch_variable_is_seeded_from_caught_type() {
        let src = "class E extends Exception {} function f() { try { throw new E(); } catch (E $e) { $x = $e; } }";
        assert_eq!(var_after(src, "x"), "E");
    }

    #[test]
    fn finally_assignment_applies_to_surviving_exits() {
        let src = "class E extends Exception {} function f() { try { $x = 1; } catch (E $e) { $x = 's'; } finally { $x = true; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "true");
    }

    #[test]
    fn terminating_finally_does_not_leak_try_assignments() {
        let src = "function f() { try { $x = 1; } finally { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "mixed");
    }

    #[test]
    fn if_without_else_widens_to_possibly_unset() {
        let src = r#"
            function f(bool $c) {
                if ($c) { $x = 1; }
            }
        "#;
        // Assigned in the then-branch, absent on the fall-through path -> int|mixed.
        assert_eq!(var_after(src, "x"), "1|mixed");
    }
}
