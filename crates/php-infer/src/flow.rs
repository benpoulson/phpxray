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
    arg_is_plain_positional, args_are_plain_positional, last_segment, peel_paren, strip_this_vars,
};
use crate::{
    arrays, collection_method, is_first_class_callable,
    refine::{strip_false, strip_falsy, strip_null_strict},
    CallableAlias, TypeCtx,
};
use php_ast::{
    Arg, ArrowFn, BinOp, ClosureExpr, Expr, ExprKind, FunctionDecl, MemberName, Name, Param, Stmt,
    StmtKind, UnOp,
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
        self.autoviv_shapes = !crate::definedness::scope_has_escape_hatch(&f.body, self.interner);
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
                // A stored closure with by-ref captures can rewrite them at
                // any later call site.
                self.widen_closure_ref_captures(rhs);
                let callable = self.callable_alias_from_expr(rhs);
                let bound = if matches!(&peel_paren(rhs).kind, ExprKind::Str(_)) {
                    t
                } else {
                    self.callable_expr_type(rhs).unwrap_or(t)
                };
                // `$x = []` is exactly the empty array: bind the empty sealed
                // shape so subsequent literal-key writes accumulate a precise
                // shape (merged mode only — native arrays are untyped).
                let bound = if !self.native
                    && matches!(&peel_paren(rhs).kind,
                        ExprKind::Array { items, .. } if items.is_empty())
                {
                    Type::Shape {
                        fields: Vec::new(),
                        sealed: true,
                    }
                } else {
                    bound
                };
                self.bind_target_with_callable(target, &bound, callable);
                bound
            }
            ExprKind::AssignOp { op, target, rhs } => {
                let t = self.binary_type(*op, target, rhs);
                self.bind_target(target, &t);
                t
            }
            // A match's result is the union of its arm bodies *with the
            // subject narrowed per arm* — only possible on the mutable flow
            // path (the pure `infer` can't adjust the environment).
            ExprKind::Match { .. } => self.match_type_narrowed(e),
            _ => self.infer(e),
        }
    }

    /// The type of a `match` expression with per-arm subject narrowing:
    /// each singleton-condition arm's body is inferred with the subject pinned
    /// to those conditions (`Suit::Hearts => $s->value` sees `'H'`).
    fn match_type_narrowed(&mut self, e: &Expr) -> Type {
        let ExprKind::Match { subject, arms } = &e.kind else {
            return self.infer(e);
        };
        let place = self.place_key(subject);
        let mut parts = Vec::with_capacity(arms.len());
        for arm in arms {
            match (&place, self.match_arm_narrowing(arm)) {
                (Some(place), Some(t)) => {
                    let saved = self.vars.clone();
                    self.apply_facts(&[(place.clone(), t)]);
                    parts.push(self.infer(&arm.body));
                    self.vars = saved;
                }
                _ => parts.push(self.infer(&arm.body)),
            }
        }
        Type::union(parts)
    }

    /// The union of an arm's conditions when they are all singleton types
    /// (enum cases / scalar literals) — the fact a matching arm implies.
    fn match_arm_narrowing(&self, arm: &php_ast::MatchArm) -> Option<Type> {
        let conds = arm.conds.as_ref()?;
        let tys: Vec<Type> = conds.iter().map(|c| self.infer(c)).collect();
        tys.iter()
            .all(|t| {
                matches!(
                    t,
                    Type::EnumCase { .. }
                        | Type::LiteralInt(_)
                        | Type::LiteralString(_)
                        | Type::True
                        | Type::False
                        | Type::Null
                )
            })
            .then(|| Type::union(tys))
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
            ExprKind::Index { .. } => self.bind_index_target(target, ty),
            _ => {}
        }
    }

    /// An assignment *through* an index chain rooted at a variable — `$v[k] = …`,
    /// `$v[k][] = …`, `$v[] = …`. The root variable is mutated, so a sealed shape
    /// (`array{a: …, b: …}`) must gain the written key, else the new key reads as
    /// "definitely absent" and later `isset($v[k])` / `$v[k][…]` false-report
    /// (notably across loop iterations, where the key is set on one pass and
    /// tested on the next). Best-effort: only variables holding a shape are
    /// widened; anything else is left untouched.
    fn bind_index_target(&mut self, target: &Expr, ty: &Type) {
        // Descend to the root variable, tracking every index level (outer→inner).
        let mut cur = target;
        let mut levels: Vec<Option<&Expr>> = Vec::new();
        let root = loop {
            let ExprKind::Index { base, index } = &cur.kind else {
                return;
            };
            levels.push(index.as_deref());
            match &base.kind {
                ExprKind::Variable(sym) => {
                    let n = self.interner.resolve(*sym);
                    if n == "this" {
                        return;
                    }
                    break n.to_string();
                }
                ExprKind::Index { .. } => cur = base,
                _ => return, // not a plain variable index chain
            }
        };
        // The index applied directly to the root is the last one pushed; the
        // target nests deeper when the chain has more than that single level.
        let nested = levels.len() > 1;
        let key = levels
            .last()
            .copied()
            .flatten()
            .and_then(|e| literal_string_of(&self.infer(e)));
        // A deeper write (`$v[k][…]`) makes `$v[k]` an array; a direct write
        // (`$v[k] = X`) stores X.
        let field_ty = if nested {
            Type::Array(None)
        } else {
            ty.clone()
        };
        match self.vars.get(&root).cloned() {
            // PHP auto-vivification: an index write through an undefined
            // variable creates exactly that array — a fresh sealed shape when
            // the key is a known literal, a bare array otherwise. Sound only
            // when "undefined" is provable, which the scope driver verified
            // (`autoviv_shapes`).
            None if self.autoviv_shapes => {
                self.vars.insert(root, vivified(key.as_deref(), field_ty));
            }
            None => {}
            Some(cur) => {
                if let Some(updated) = widen_shape_for_write(&cur, key.as_deref(), field_ty) {
                    self.vars.insert(root, updated);
                }
            }
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
                BinOp::Identical | BinOp::Eq => {
                    self.null_cmp(lhs, rhs, truthy, out);
                    self.count_eq_facts(lhs, rhs, truthy, out);
                    if matches!(op, BinOp::Identical) {
                        self.fn_result_cmp(lhs, rhs, truthy, out);
                        self.fn_result_cmp(rhs, lhs, truthy, out);
                    }
                }
                BinOp::NotIdentical | BinOp::NotEq => {
                    self.null_cmp(lhs, rhs, !truthy, out);
                    self.count_eq_facts(lhs, rhs, !truthy, out);
                    if matches!(op, BinOp::NotIdentical) {
                        self.fn_result_cmp(lhs, rhs, !truthy, out);
                        self.fn_result_cmp(rhs, lhs, !truthy, out);
                    }
                }
                // Integer-range narrowing: `$x < 2` false ⇒ `$x: int<2, max>`, etc.
                BinOp::Lt | BinOp::LtEq | BinOp::Gt | BinOp::GtEq => {
                    self.int_cmp_facts(*op, lhs, rhs, truthy, out);
                    self.count_cmp_facts(*op, lhs, rhs, truthy, out);
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
                    // A userland function shadowing a builtin name says nothing
                    // about its argument's type.
                    let builtin = self.narrows_as_builtin(n);
                    if let Some(arg0) = args.first().filter(|_| builtin) {
                        if let Some(place) = self.place_key(&arg0.value) {
                            if truthy {
                                if let Some(t) = predicate_type(&fname) {
                                    let cur = self.infer(&arg0.value);
                                    out.push((place, narrow_to_predicate(&cur, &t)));
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
                    if builtin {
                        self.builtin_specifier_facts(&fname, args, truthy, out);
                    }
                    self.assert_facts_fn(n, args, Some(truthy), out);
                }
            }
            ExprKind::StaticCall {
                class,
                method,
                args,
            } => {
                self.assert_facts_static(class, method, args, Some(truthy), out);
                self.bare_truthy_fact(cond, truthy, out);
            }
            ExprKind::MethodCall {
                recv,
                method,
                args,
                nullsafe: false,
                ..
            } => {
                self.assert_facts_method(recv, method, args, Some(truthy), out);
                self.bare_truthy_fact(cond, truthy, out);
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

    /// The catch-all bare-truthy fact (a call expression used as a condition
    /// is non-falsy in the then-branch), shared by the call-shaped arms.
    fn bare_truthy_fact(&self, cond: &Expr, truthy: bool, out: &mut Vec<Fact>) {
        if truthy {
            if let Some(place) = self.place_key(cond) {
                out.push((place, strip_falsy(&self.infer(cond))));
            }
        }
    }

    // -- `@phpstan-assert*` application --------------------------------------
    //
    // A callee's assert declarations narrow the matching argument (or the
    // receiver's `$this->prop` path). `truthy: Some(b)` is a condition site
    // (IfTrue/IfFalse gate on the branch, Always applies to both); `None` is
    // the statement path, where only Always applies.

    /// May a call to `n` be narrowed as the **global builtin** of that name?
    ///
    /// PHP's unqualified-function fallback means a namespaced
    /// `function is_int(): bool` shadows the global one for unqualified calls in
    /// that namespace, with entirely different semantics — narrowing on it would
    /// be unsound (the contract in this module's header: never over-narrow). A
    /// fully-qualified `\is_int` always resolves to the builtin. A name that
    /// resolves to nothing stays permissive: an incomplete index must not
    /// silently switch narrowing off. Same posture as `apply_preg_match_out` /
    /// `rec_builtin_callback_args`, which already guarded this way.
    fn narrows_as_builtin(&self, n: &Name) -> bool {
        !self.function_reflection(n).is_some_and(|f| !f.builtin)
    }

    /// The sole argument of a `count($x)` / `sizeof($x)` call, when it is the
    /// global builtin (a userland `count()` proves nothing about emptiness).
    fn count_call_arg<'e>(&self, e: &'e Expr) -> Option<&'e Expr> {
        let ExprKind::Call { callee, args } = &peel_paren(e).kind else {
            return None;
        };
        let ExprKind::Name(n) = &callee.kind else {
            return None;
        };
        let last = last_segment(&n.text);
        if !last.eq_ignore_ascii_case("count") && !last.eq_ignore_ascii_case("sizeof") {
            return None;
        }
        if !self.narrows_as_builtin(n) {
            return None;
        }
        let arg = args.first()?;
        arg_is_plain_positional(arg).then_some(&arg.value)
    }

    fn assert_facts_fn(&self, n: &Name, args: &[Arg], truthy: Option<bool>, out: &mut Vec<Fact>) {
        let Some(f) = self.function_reflection(n) else {
            return;
        };
        if f.asserts.is_empty() {
            return;
        }
        self.push_assert_facts(&f.asserts, &f.params, args, None, truthy, out);
    }

    fn assert_facts_static(
        &self,
        class: &Expr,
        method: &MemberName,
        args: &[Arg],
        truthy: Option<bool>,
        out: &mut Vec<Fact>,
    ) {
        let Some(name) = self.member_ident(method) else {
            return;
        };
        let Some(fqn) = self.class_type(class).and_then(|t| self.type_class_fqn(&t)) else {
            return;
        };
        let Some(found) = self.index.find_method(&fqn, &name) else {
            return;
        };
        if found.member.asserts.is_empty() {
            return;
        }
        self.push_assert_facts(
            &found.member.asserts,
            &found.member.params,
            args,
            None,
            truthy,
            out,
        );
    }

    fn assert_facts_method(
        &self,
        recv: &Expr,
        method: &MemberName,
        args: &[Arg],
        truthy: Option<bool>,
        out: &mut Vec<Fact>,
    ) {
        let Some(name) = self.member_ident(method) else {
            return;
        };
        let recv_ty = self.infer(recv);
        let Some(fqn) = self.type_class_fqn(&recv_ty) else {
            return;
        };
        let Some(found) = self.find_method_for_receiver(&recv_ty, &fqn, &name) else {
            return;
        };
        if found.member.asserts.is_empty() {
            return;
        }
        let recv_place = self.invalidation_base(recv);
        self.push_assert_facts(
            &found.member.asserts,
            &found.member.params,
            args,
            recv_place.as_deref(),
            truthy,
            out,
        );
    }

    fn push_assert_facts(
        &self,
        asserts: &[php_reflect::AssertReflection],
        params: &[php_reflect::ParamReflection],
        args: &[Arg],
        recv_place: Option<&str>,
        truthy: Option<bool>,
        out: &mut Vec<Fact>,
    ) {
        use php_phpdoc::AssertWhen;
        for a in asserts {
            let applies = match (a.when, truthy) {
                (AssertWhen::Always, _) => true,
                (AssertWhen::IfTrue, Some(t)) => t,
                (AssertWhen::IfFalse, Some(t)) => !t,
                (_, None) => false,
            };
            if !applies {
                continue;
            }
            let (place, cur) = if let Some(path) = a.param.strip_prefix("this->") {
                let Some(base) = recv_place else { continue };
                let place = format!("{base}->{path}");
                let cur = self.vars.get(&place).cloned();
                (place, cur)
            } else {
                let Some(idx) = params.iter().position(|p| p.name == a.param) else {
                    continue;
                };
                // Named/spread args break positional mapping.
                if args
                    .iter()
                    .any(|x| x.name.is_some() || x.spread || x.placeholder)
                {
                    continue;
                }
                let Some(arg) = args.get(idx) else { continue };
                let Some(place) = self.place_key(&arg.value) else {
                    continue;
                };
                let cur = self.infer(&arg.value);
                (place, Some(cur))
            };
            if a.negated {
                let Some(cur) = cur else { continue };
                let narrowed = match &a.ty {
                    Type::Null => strip_null_strict(&cur),
                    Type::False => strip_false(&cur),
                    ty => subtract_union(&cur, |m| confidently_in(self.index, m, ty)),
                };
                if narrowed != cur {
                    out.push((place, narrowed));
                }
            } else {
                out.push((place, a.ty.clone()));
            }
        }
    }

    /// `get_class($x) === C::class` / `gettype($x) === 'string'` narrowing
    /// (strict comparisons only; `eq` is the branch's truth for equality).
    fn fn_result_cmp(&self, call: &Expr, lit: &Expr, eq: bool, out: &mut Vec<Fact>) {
        let ExprKind::Call { callee, args } = &peel_paren(call).kind else {
            return;
        };
        let ExprKind::Name(n) = &callee.kind else {
            return;
        };
        if !self.narrows_as_builtin(n) {
            return;
        }
        let fname = last_segment(&n.text).to_ascii_lowercase();
        let Some(arg0) = args.first() else { return };
        let Some(place) = self.place_key(&arg0.value) else {
            return;
        };
        match fname.as_str() {
            "get_class" => {
                let Some(fqn) = class_name_arg(&self.infer(lit)) else {
                    return;
                };
                let named = Type::Named {
                    fqn: fqn.into(),
                    args: Vec::new(),
                };
                if eq {
                    out.push((place, named));
                } else {
                    // `get_class($x) !== C::class` ⇒ drop the *exact* class from
                    // an explicit union (subclasses have a different get_class).
                    let cur = self.infer(&arg0.value);
                    let narrowed = subtract_union(&cur, |m| *m == named);
                    if narrowed != cur {
                        out.push((place, narrowed));
                    }
                }
            }
            "gettype" => {
                let Type::LiteralString(s) = self.infer(lit) else {
                    return;
                };
                let t = match &*s {
                    "integer" => Type::Int,
                    "string" => Type::String,
                    "boolean" => Type::Bool,
                    "double" => Type::Float,
                    "array" => Type::Array(None),
                    "object" => Type::Object,
                    "NULL" => Type::Null,
                    _ => return,
                };
                let cur = self.infer(&arg0.value);
                if eq {
                    out.push((place, narrow_to_predicate(&cur, &t)));
                } else {
                    let narrowed = subtract_union(&cur, |m| predicate_matches(m, &t));
                    if narrowed != cur {
                        out.push((place, narrowed));
                    }
                }
            }
            _ => {}
        }
    }

    /// Builtin condition specifiers beyond the `is_*` family (phpstan's
    /// TypeSpecifyingExtensions): each is a *sound* refinement the branch
    /// guarantees; anything unprovable stays un-narrowed.
    fn builtin_specifier_facts(
        &self,
        fname: &str,
        args: &[Arg],
        truthy: bool,
        out: &mut Vec<Fact>,
    ) {
        match fname {
            // `in_array($x, $set, true)` (strict): true ⇒ $x is one of the
            // set's values — precise when they are all singletons.
            "in_array" => {
                if args.len() < 3 || !expr_is_true(&args[2].value) {
                    return;
                }
                let Some(place) = self.place_key(&args[0].value) else {
                    return;
                };
                let Some(values) = singleton_values(&self.infer(&args[1].value)) else {
                    return;
                };
                if truthy {
                    out.push((place, Type::union(values)));
                } else {
                    let cur = self.infer(&args[0].value);
                    let narrowed = subtract_union(&cur, |m| values.contains(m));
                    if narrowed != cur {
                        out.push((place, narrowed));
                    }
                }
            }
            // `array_key_exists($k, $arr)` true ⇒ a shape's optional key is
            // definitely present.
            "array_key_exists" | "key_exists" => {
                if !truthy || args.len() < 2 {
                    return;
                }
                let Some(key) = literal_string_of(&self.infer(&args[0].value)) else {
                    return;
                };
                let Some(place) = self.place_key(&args[1].value) else {
                    return;
                };
                let cur = self.infer(&args[1].value);
                if let Type::Shape { fields, sealed } = &cur {
                    let mut fields = fields.clone();
                    let mut changed = false;
                    for f in &mut fields {
                        if f.key.as_deref() == Some(key.as_str()) && f.optional {
                            f.optional = false;
                            changed = true;
                        }
                    }
                    if changed {
                        out.push((
                            place,
                            Type::Shape {
                                fields,
                                sealed: *sealed,
                            },
                        ));
                    }
                }
            }
            // `is_a($x, C::class)` / `is_subclass_of($x, C::class)` true ⇒ an
            // object $x is an instance of C. Only when $x is already known to
            // be an object — both functions also accept class-*strings*.
            "is_a" | "is_subclass_of" => {
                if !truthy || args.len() < 2 {
                    return;
                }
                let Some(place) = self.place_key(&args[0].value) else {
                    return;
                };
                let cur = self.infer(&args[0].value);
                if !definitely_object_type(&cur) {
                    return;
                }
                let Some(fqn) = class_name_arg(&self.infer(&args[1].value)) else {
                    return;
                };
                out.push((
                    place,
                    Type::Named {
                        fqn: fqn.into(),
                        args: Vec::new(),
                    },
                ));
            }
            // `str_contains/starts/ends($h, $n)` true with a provably
            // non-empty needle ⇒ the haystack is non-empty.
            "str_contains" | "str_starts_with" | "str_ends_with" => {
                if !truthy || args.len() < 2 {
                    return;
                }
                let needle_non_empty = match self.infer(&args[1].value) {
                    Type::LiteralString(s) => !s.is_empty(),
                    Type::StringOf(r) => r.implies(php_types::StringRefinement::NonEmpty),
                    _ => false,
                };
                if !needle_non_empty {
                    return;
                }
                let Some(place) = self.place_key(&args[0].value) else {
                    return;
                };
                if matches!(self.infer(&args[0].value), Type::String) {
                    out.push((place, Type::StringOf(php_types::StringRefinement::NonEmpty)));
                }
            }
            // `ctype_digit($s)` true on a string ⇒ digits only ⇒ numeric-string.
            "ctype_digit" => {
                if !truthy {
                    return;
                }
                let Some(arg0) = args.first() else { return };
                let Some(place) = self.place_key(&arg0.value) else {
                    return;
                };
                if matches!(self.infer(&arg0.value), Type::String | Type::StringOf(_)) {
                    out.push((place, Type::StringOf(php_types::StringRefinement::Numeric)));
                }
            }
            // `class_exists($s)` true on a string ⇒ it names a class.
            "class_exists" | "interface_exists" | "enum_exists" => {
                if !truthy {
                    return;
                }
                let Some(arg0) = args.first() else { return };
                let Some(place) = self.place_key(&arg0.value) else {
                    return;
                };
                if matches!(self.infer(&arg0.value), Type::String | Type::StringOf(_)) {
                    out.push((place, Type::ClassString(None)));
                }
            }
            // `function_exists($s)` true on a string ⇒ it names a callable.
            "function_exists" => {
                if !truthy {
                    return;
                }
                let Some(arg0) = args.first() else { return };
                let Some(place) = self.place_key(&arg0.value) else {
                    return;
                };
                if matches!(self.infer(&arg0.value), Type::String) {
                    out.push((place, Type::StringOf(php_types::StringRefinement::Callable)));
                }
            }
            // Truthy `count($x)` / `sizeof($x)` ⇒ at least one element.
            "count" | "sizeof" => {
                if !truthy {
                    return;
                }
                let Some(arg0) = args.first() else { return };
                let Some(place) = self.place_key(&arg0.value) else {
                    return;
                };
                self.push_non_empty(place, &arg0.value, out);
            }
            // `array_is_list($a)` true ⇒ the array is a list.
            "array_is_list" => {
                if !truthy {
                    return;
                }
                let Some(arg0) = args.first() else { return };
                let Some(place) = self.place_key(&arg0.value) else {
                    return;
                };
                match self.infer(&arg0.value) {
                    Type::Array(Some(kv)) => out.push((place, Type::List(Box::new(kv.1.clone())))),
                    Type::Array(None) => out.push((place, Type::List(Box::new(Type::Mixed)))),
                    _ => {}
                }
            }
            _ => {}
        }
    }

    /// `count($x) CMP n` non-emptiness: a branch where the count is provably
    /// >= 1 makes the counted container non-empty.
    fn count_cmp_facts(
        &self,
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        truthy: bool,
        out: &mut Vec<Fact>,
    ) {
        let (call, lit, op) = if let Some(n) = int_lit(rhs) {
            (lhs, n, op)
        } else if let Some(n) = int_lit(lhs) {
            (rhs, n, flip_cmp(op))
        } else {
            return;
        };
        let Some(arg) = self.count_call_arg(call) else {
            return;
        };
        let Some(place) = self.place_key(arg) else {
            return;
        };
        let eff = if truthy { op } else { negate_cmp(op) };
        let min_count = match eff {
            BinOp::Gt => lit.saturating_add(1),
            BinOp::GtEq => lit,
            _ => return, // upper bounds prove nothing about non-emptiness
        };
        if min_count >= 1 {
            self.push_non_empty(place, arg, out);
        }
    }

    /// `count($x) === n` (n >= 1) / `count($x) !== 0` ⇒ non-empty. `eq` is the
    /// branch's truth for the equality.
    fn count_eq_facts(&self, lhs: &Expr, rhs: &Expr, eq: bool, out: &mut Vec<Fact>) {
        let (call, lit) = if let Some(n) = int_lit(rhs) {
            (lhs, n)
        } else if let Some(n) = int_lit(lhs) {
            (rhs, n)
        } else {
            return;
        };
        let Some(arg) = self.count_call_arg(call) else {
            return;
        };
        let Some(place) = self.place_key(arg) else {
            return;
        };
        if (eq && lit >= 1) || (!eq && lit == 0) {
            self.push_non_empty(place, arg, out);
        }
    }

    fn push_non_empty(&self, place: String, arg: &Expr, out: &mut Vec<Fact>) {
        let cur = self.infer(arg);
        let ne = Type::non_empty(cur.clone());
        if ne != cur {
            out.push((place, ne));
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
            // `$x === Suit::Hearts` pins the case; `!==` subtracts it from an
            // explicit union of cases (sound: only narrows, never to empty).
            (lit @ Type::EnumCase { .. }, true) => lit,
            (lit @ Type::EnumCase { .. }, false) => {
                let cur = self.infer(operand);
                let narrowed = subtract_union(&cur, |m| *m == lit);
                if narrowed == cur {
                    return;
                }
                narrowed
            }
            _ => return,
        };
        out.push((place, t));
    }

    /// If `e` is a `null`/`false` literal or an enum case (`Suit::Hearts`),
    /// the corresponding singleton [`Type`].
    fn cmp_lit(&self, e: &Expr) -> Option<Type> {
        match &e.kind {
            ExprKind::Name(n) if n.text.eq_ignore_ascii_case("null") => Some(Type::Null),
            ExprKind::Name(n) if n.text.eq_ignore_ascii_case("false") => Some(Type::False),
            ExprKind::ClassConst { .. } => match self.infer(e) {
                t @ Type::EnumCase { .. } => Some(t),
                _ => None,
            },
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

    // -- Call side-effect invalidation --------------------------------------
    //
    // A narrowed object-state place (`$this->prop`, `$obj->prop`, `$obj->m()`)
    // stays narrowed across a call only when the callee is not known to mutate
    // reachable object state. Mirrors phpstan's `hasSideEffects` semantics:
    // a callee has side effects iff it is explicitly `@phpstan-impure`, returns
    // `void`, or is a fluent setter (returns `$this`-flavoured `static`/`self`);
    // an unmarked value-returning callee keeps narrowing. A fluent callee (not
    // explicitly impure) mutates its receiver but spares its *arguments*, and a
    // constructor spares arguments unless explicitly impure. Built-in functions
    // never invalidate through their arguments (curated — the overwhelming
    // majority are object-transparent); by-ref parameters are widened for every
    // resolved callee, builtin or not.

    /// After `$recv->m(...)`: invalidate the receiver's derived places when the
    /// method has side effects, and object arguments unless it is fluent.
    fn invalidate_after_method_call(&mut self, recv: &Expr, method: &MemberName, args: &[Arg]) {
        if is_first_class_callable(args) {
            return;
        }
        let mut facts = (SE_YES, None);
        let mut self_out: Option<Type> = None;
        if let Some(name) = self.member_ident(method) {
            let recv_ty = self.infer(recv);
            if let Some(fqn) = self.type_class_fqn(&recv_ty) {
                if let Some(found) = self.find_method_for_receiver(&recv_ty, &fqn, &name) {
                    facts = (
                        method_side_effects(&found.member),
                        Some(param_ref_info(&found.member.params)),
                    );
                    // `@phpstan-self-out T` retypes the receiver after the call
                    // (`self`/`static`/`self<…>` bound to the receiver class).
                    self_out = found
                        .member
                        .self_out
                        .clone()
                        .map(|t| self.bind_relative(t, &fqn));
                }
            }
        }
        let (se, params) = facts;
        if se.yes {
            if let Some(base) = self.invalidation_base(recv) {
                self.invalidate_derived_places(&base);
            }
            if !se.fluent {
                self.invalidate_object_args(args);
            }
        }
        self.widen_by_ref_args(params, args);
        // Apply `@phpstan-self-out` to a simple `$var` receiver after widening.
        if let (Some(out), ExprKind::Variable(sym)) = (self_out, &recv.kind) {
            let recv_name = self.interner.resolve(*sym).to_string();
            if recv_name != "this" {
                self.callables.remove(&recv_name);
                self.vars.insert(recv_name, out);
            }
        }
    }

    /// After `f(...)` / `$f(...)`.
    fn invalidate_after_fn_call(&mut self, callee: &Expr, args: &[Arg]) {
        if is_first_class_callable(args) {
            return;
        }
        let facts = match &callee.kind {
            ExprKind::Name(n) => match self.function_reflection(n) {
                Some(f) => {
                    let se = if f.impure {
                        SE_YES
                    } else if f.builtin || f.pure {
                        SE_NO
                    } else if matches!(f.return_type, Type::Void) {
                        SE_YES
                    } else {
                        SE_NO
                    };
                    let mut info = param_ref_info(&f.params);
                    info.builtin = f.builtin;
                    (se, Some(info))
                }
                // Unknown function — assume the worst.
                None => (SE_YES, None),
            },
            // Dynamic callee (`$f(...)`, an inline closure call, …).
            _ => (SE_YES, None),
        };
        let (se, params) = facts;
        if se.yes {
            self.invalidate_object_args(args);
        }
        self.widen_by_ref_args(params, args);
        self.apply_preg_match_out(callee, args);
    }

    /// `preg_match($p, $s, $m)` / `preg_match_all` type their `$matches`
    /// out-parameter precisely: `array<int|string, string>` for `preg_match`
    /// (each capture group is a matched string) and `array<int|string,
    /// list<string>>` for `preg_match_all`. Applied unconditionally after the
    /// call (sound in both branches: on no-match `$matches` is an empty array,
    /// which fits). Only a plain `$var` matches argument is handled; a userland
    /// redefinition of `preg_match` is skipped.
    fn apply_preg_match_out(&mut self, callee: &Expr, args: &[Arg]) {
        let ExprKind::Name(n) = &callee.kind else {
            return;
        };
        // Skip a userland function that shadows the builtin name.
        if self.function_reflection(n).is_some_and(|f| !f.builtin) {
            return;
        }
        let matches_ty = match last_segment(&n.text).to_ascii_lowercase().as_str() {
            "preg_match" => preg_match_array_type(),
            "preg_match_all" => Type::Array(Some(Box::new((
                Type::union(vec![Type::Int, Type::String]),
                Type::List(Box::new(Type::String)),
            )))),
            _ => return,
        };
        let Some(arg) = args.get(2) else {
            return;
        };
        if arg.spread || arg.name.is_some() || arg.placeholder {
            return;
        }
        let ExprKind::Variable(sym) = &arg.value.kind else {
            return;
        };
        let name = self.interner.resolve(*sym).to_string();
        if name == "this" {
            return;
        }
        self.callables.remove(&name);
        self.vars.insert(name, matches_ty);
    }

    /// After `C::m(...)`. A `self::`/`parent::`/`static::` call to an instance
    /// method runs on `$this`, so it invalidates `$this`'s derived places like a
    /// method call would.
    fn invalidate_after_static_call(&mut self, class: &Expr, method: &MemberName, args: &[Arg]) {
        if is_first_class_callable(args) {
            return;
        }
        let this_class = matches!(&class.kind, ExprKind::Name(n)
            if matches!(last_segment(&n.text).to_ascii_lowercase().as_str(), "self" | "parent" | "static"));
        let mut facts = (SE_YES, None);
        let mut on_this = this_class;
        if let Some(name) = self.member_ident(method) {
            if let Some(fqn) = self.class_type(class).and_then(|t| self.type_class_fqn(&t)) {
                if let Some(found) = self.index.find_method(&fqn, &name) {
                    on_this = this_class && !found.member.is_static;
                    facts = (
                        method_side_effects(&found.member),
                        Some(param_ref_info(&found.member.params)),
                    );
                }
            }
        }
        let (se, params) = facts;
        if se.yes {
            if on_this {
                self.invalidate_derived_places("this");
            }
            if !se.fluent {
                self.invalidate_object_args(args);
            }
        }
        self.widen_by_ref_args(params, args);
    }

    /// After `new C(...)`: constructors spare argument narrowing unless
    /// explicitly `@phpstan-impure` (phpstan's `impure-constructor` semantics).
    fn invalidate_after_new(&mut self, class: &Expr, args: &[Arg]) {
        let Some(fqn) = self.class_type(class).and_then(|t| self.type_class_fqn(&t)) else {
            return;
        };
        let Some(found) = self.index.find_method(&fqn, "__construct") else {
            return;
        };
        let impure = found.member.impure;
        let params = Some(param_ref_info(&found.member.params));
        if impure {
            self.invalidate_object_args(args);
        }
        self.widen_by_ref_args(params, args);
    }

    /// The env key whose *derived* places a call through `e` invalidates:
    /// unlike [`place_key`], `$this` itself is a valid base here.
    fn invalidation_base(&self, e: &Expr) -> Option<String> {
        match &e.kind {
            ExprKind::Paren(inner) => self.invalidation_base(inner),
            ExprKind::Variable(sym) => Some(self.interner.resolve(*sym).to_string()),
            _ => self.place_key(e),
        }
    }

    /// Remove narrowed places derived from `base` (`base->prop`, `base->m()`,
    /// and deeper chains). The base itself keeps its type — a call can mutate
    /// the object's state, not rebind the caller's variable.
    fn invalidate_derived_places(&mut self, base: &str) {
        let prefix = format!("{base}->");
        self.vars.retain(|k, _| !k.starts_with(prefix.as_str()));
    }

    /// Invalidate the derived places of every argument that may be an object
    /// (objects travel by handle; scalars/arrays are copied and can't be
    /// mutated by the callee — their narrowing survives).
    fn invalidate_object_args(&mut self, args: &[Arg]) {
        for a in args {
            if a.placeholder {
                continue;
            }
            let Some(base) = self.invalidation_base(&a.value) else {
                continue;
            };
            if !type_may_be_object(&self.infer(&a.value)) {
                continue;
            }
            self.invalidate_derived_places(&base);
        }
    }

    /// Widen every variable captured by reference (`use (&$x)`) by any closure
    /// literal inside `e`: once the closure value exists, an invocation at any
    /// later point may rewrite the capture, so its outer type is no longer
    /// known. (Arrow fns capture by value only — closures are the only case.)
    fn widen_closure_ref_captures(&mut self, e: &Expr) {
        let mut names: Vec<php_intern::Symbol> = Vec::new();
        php_ast::walk::for_each_subexpr(e, &mut |sub| {
            if let ExprKind::Closure(c) = &sub.kind {
                for u in &c.uses {
                    if u.by_ref {
                        names.push(u.name);
                    }
                }
            }
        });
        for sym in names {
            let name = self.interner.resolve(sym).to_string();
            if name != "this" {
                self.callables.remove(&name);
                self.vars.insert(name, Type::Mixed);
            }
        }
    }

    /// A by-ref parameter may rebind its argument entirely: reset the argument
    /// variable to the parameter's declared type (phpstan's virtual-assign).
    /// Builtin exception: when the argument's current type already fits the
    /// declared parameter type, keep it — phpstan regains that precision via
    /// per-function ParameterOut extensions (`usort` keeps `array<string,User>`,
    /// not bare `array`); an in-fit builtin by-ref arg is mutated-in-kind, not
    /// re-typed. An out-of-fit arg (e.g. a string `$matches` before
    /// `preg_match`) still widens to the declared type.
    fn widen_by_ref_args(&mut self, params: Option<ParamRefInfo>, args: &[Arg]) {
        // A closure argument with a `use (&$x)` capture may rewrite `$x` at
        // any later invocation of the closure — widen such captures now,
        // whatever the callee's own signature says.
        for a in args {
            self.widen_closure_ref_captures(&a.value);
        }
        let Some(ParamRefInfo {
            params,
            variadic_last,
            builtin,
        }) = params
        else {
            return;
        };
        for (i, a) in args.iter().enumerate() {
            // Named/spread args break positional mapping; skip (sound: no widening).
            if a.placeholder || a.spread || a.name.is_some() {
                continue;
            }
            let idx = if i < params.len() {
                i
            } else if variadic_last && !params.is_empty() {
                params.len() - 1
            } else {
                continue;
            };
            let (by_ref, ref ty, explicit_out) = params[idx];
            if !by_ref {
                continue;
            }
            let ExprKind::Variable(sym) = &a.value.kind else {
                continue;
            };
            let name = self.interner.resolve(*sym).to_string();
            if name == "this" {
                continue;
            }
            // The builtin keep-current heuristic never overrides an explicit
            // `@param-out` contract.
            if builtin && !explicit_out {
                if let Some(cur) = self.vars.get(&name) {
                    if crate::is_assignable(self.index, cur, ty) {
                        continue;
                    }
                }
            }
            self.invalidate_derived_places(&name);
            self.callables.remove(&name);
            if matches!(ty, Type::Mixed) {
                self.vars.remove(&name);
            } else {
                self.vars.insert(name, ty.clone());
            }
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
                self.invalidate_after_fn_call(callee, args);
                if let ExprKind::Name(n) = &callee.kind {
                    let mut facts = Vec::new();
                    self.assert_facts_fn(n, args, None, &mut facts);
                    self.apply_facts(&facts);
                }
            }
            ExprKind::MethodCall {
                recv, method, args, ..
            } => {
                self.rec_here(recv, map);
                self.rec_member(method, map);
                self.rec_args(args, map);
                self.rec_collection_callback_args(recv, method, args, map);
                self.invalidate_after_method_call(recv, method, args);
                let mut facts = Vec::new();
                self.assert_facts_method(recv, method, args, None, &mut facts);
                self.apply_facts(&facts);
            }
            ExprKind::StaticCall {
                class,
                method,
                args,
            } => {
                self.rec_here(class, map);
                self.rec_member(method, map);
                self.rec_args(args, map);
                self.invalidate_after_static_call(class, method, args);
                let mut facts = Vec::new();
                self.assert_facts_static(class, method, args, None, &mut facts);
                self.apply_facts(&facts);
            }
            ExprKind::New { class, args } => {
                self.rec_here(class, map);
                self.rec_args(args, map);
                self.invalidate_after_new(class, args);
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
                let place = self.place_key(subject);
                for arm in arms {
                    if let Some(conds) = &arm.conds {
                        for c in conds {
                            self.rec_here(c, map);
                        }
                    }
                    // When every arm condition is a singleton (enum case or
                    // scalar literal), the arm body sees the subject narrowed
                    // to their union (`match ($s) { Suit::Hearts => …`).
                    let narrowed = place.as_ref().and_then(|_| self.match_arm_narrowing(arm));
                    match (&place, narrowed) {
                        (Some(place), Some(t)) => {
                            let saved = self.vars.clone();
                            self.apply_facts(&[(place.clone(), t)]);
                            self.rec_here(&arm.body, map);
                            self.vars = saved;
                        }
                        _ => self.rec_here(&arm.body, map),
                    }
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
        let mut child = self.closure_child(c, inferred_params);
        child.autoviv_shapes = !crate::definedness::scope_has_escape_hatch(&c.body, self.interner);
        child.record_block(&c.body, map);
    }

    fn rec_arrow(&self, a: &ArrowFn, inferred_params: &[Type], map: &mut RecMap) {
        self.arrow_child(a, inferred_params).rec_here(&a.body, map);
    }

    fn seed_ast_params(&self, vars: &mut Env, params: &[Param], inferred: &[Type]) {
        for (i, p) in params.iter().enumerate() {
            let name = self.interner.resolve(p.name).to_string();
            let rest = &inferred[i.min(inferred.len())..];
            vars.insert(
                name,
                self.ast_param_type(p, rest, crate::ParamFallback::Inferred),
            );
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
                let generator_send = self.declared_generator_send(expr.return_type.as_ref());
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
                let generator_send = self.declared_generator_send(expr.return_type.as_ref());
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
        let mut child = self.child();
        child.class = class;
        child.vars = vars;
        child.callables = callables;
        child.generator_send = generator_send;
        child.autoviv_shapes = !crate::definedness::scope_has_escape_hatch(body, self.interner);
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
        let mut child = self.child();
        child.class = class;
        child.vars = vars;
        child.callables = callables;
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
        if !last_segment(&n.text).eq_ignore_ascii_case("assert") || !self.narrows_as_builtin(n) {
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
        if !self.always_terminates(then) {
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
            if !self.always_terminates(&ei.body) {
                envs.push(self.take_flow_state());
            }
            else_facts.extend(neg);
        }

        match els {
            Some(e) => {
                self.set_flow_state(base.clone());
                self.apply_facts(&else_facts);
                self.record_stmt(e, map);
                if !self.always_terminates(e) {
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
        // A non-empty subject runs the body at least once: the post-loop state
        // is the post-body state, not merged with the never-ran entry state.
        let definite = matches!(subj_ty, Type::NonEmpty(_));
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
            let next = merge_states(vec![base.clone(), after.clone()]);
            if flow_state_same(&current, &next) {
                self.set_flow_state(if definite { after } else { next });
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
        if !self.block_always_terminates(body) {
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
            if !self.block_always_terminates(&catch.body) {
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
            if self.block_always_terminates(finally) {
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
            php_resolve::Resolution::Fqn(fqn) => Some(Type::Named {
                fqn: fqn.into(),
                args: vec![],
            }),
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
/// The positive-branch fact for `is_*($x)`: keep the parts of the current type
/// that already satisfy the predicate (they are *narrower* than the predicate's
/// broad type — `'a'|'b'` under `is_string` stays `'a'|'b'`, `non-empty-string`
/// is not widened to `string`); fall back to the predicate type otherwise.
fn narrow_to_predicate(cur: &Type, t: &Type) -> Type {
    match cur {
        Type::Union(parts) => {
            let kept: Vec<Type> = parts
                .iter()
                .filter(|m| predicate_matches(m, t))
                .cloned()
                .collect();
            if kept.is_empty() {
                t.clone()
            } else {
                Type::union(kept)
            }
        }
        Type::Nullable(inner) if !matches!(t, Type::Null) => narrow_to_predicate(inner, t),
        _ if predicate_matches(cur, t) => cur.clone(),
        _ => t.clone(),
    }
}

fn predicate_matches(m: &Type, t: &Type) -> bool {
    use Type::*;
    match t {
        String => matches!(m, String | StringOf(_) | LiteralString(_) | ClassString(_)),
        Int => matches!(m, Int | LiteralInt(_)),
        Float => matches!(m, Float),
        Bool => matches!(m, Bool | True | False),
        Array(_) => matches!(m.peel_non_empty(), Array(_) | List(_) | Shape { .. }),
        Object => matches!(
            m,
            Object | Named { .. } | EnumCase { .. } | SelfType | StaticType
        ),
        Iterable(_) => matches!(
            m.peel_non_empty(),
            Iterable(_) | Array(_) | List(_) | Shape { .. }
        ),
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
/// phpstan `hasSideEffects` verdict for one call, plus the fluent-receiver
/// refinement (fluent setters invalidate their receiver but spare arguments).
#[derive(Clone, Copy)]
struct SideEffects {
    yes: bool,
    fluent: bool,
}

const SE_YES: SideEffects = SideEffects {
    yes: true,
    fluent: false,
};
const SE_NO: SideEffects = SideEffects {
    yes: false,
    fluent: false,
};

/// Side-effect classification of a resolved method: explicitly `@phpstan-impure`
/// → yes; explicitly pure → no; `void` return or a fluent `$this`-flavoured
/// return (`static`/`self`) → yes; anything else (unmarked, value-returning)
/// → no, narrowing survives (phpstan's `impure-method` fixture semantics).
fn method_side_effects(m: &php_reflect::MethodReflection) -> SideEffects {
    if m.impure {
        return SE_YES;
    }
    if m.pure {
        return SE_NO;
    }
    let fluent = matches!(m.return_type, Type::StaticType | Type::SelfType);
    if fluent || matches!(m.return_type, Type::Void) {
        SideEffects { yes: true, fluent }
    } else {
        SE_NO
    }
}

/// The minimal owned callee-parameter view [`TypeCtx::widen_by_ref_args`]
/// needs: `(by_ref, declared type)` per positional parameter, whether the last
/// is variadic, and whether the callee is a builtin (`Type` clones are
/// Arc-cheap).
struct ParamRefInfo {
    /// `(by_ref, post-call type, explicit @param-out)` per positional param.
    params: Vec<(bool, Type, bool)>,
    variadic_last: bool,
    builtin: bool,
}

fn param_ref_info(params: &[php_reflect::ParamReflection]) -> ParamRefInfo {
    ParamRefInfo {
        params: params
            .iter()
            .map(|p| match &p.out_ty {
                // An explicit `@param-out` is the post-call contract.
                Some(out) => (p.by_ref, out.clone(), true),
                None => (p.by_ref, p.ty.clone(), false),
            })
            .collect(),
        variadic_last: params.last().is_some_and(|p| p.variadic),
        builtin: false,
    }
}

/// Whether a value of type `t` may be an object (travel by handle, so a
/// side-effecting callee could mutate it). Scalars and arrays are copied;
/// anything unknown/object-flavoured conservatively may.
fn type_may_be_object(t: &Type) -> bool {
    match t {
        Type::Null
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Int
        | Type::IntRange { .. }
        | Type::LiteralInt(_)
        | Type::Float
        | Type::String
        | Type::LiteralString(_)
        | Type::Array(_)
        | Type::List(_)
        | Type::Shape { .. }
        | Type::ClassString(_)
        | Type::Void
        | Type::Never => false,
        Type::NonEmpty(_) => false,
        Type::Nullable(inner) => type_may_be_object(inner),
        Type::Union(ms) => ms.iter().any(type_may_be_object),
        _ => true,
    }
}

fn expr_is_true(e: &Expr) -> bool {
    matches!(&peel_paren(e).kind, ExprKind::Name(n) if n.text.eq_ignore_ascii_case("true"))
}

/// A singleton type — one exact runtime value (`===`-comparable).
fn is_singleton(t: &Type) -> bool {
    matches!(
        t,
        Type::LiteralInt(_)
            | Type::LiteralString(_)
            | Type::EnumCase { .. }
            | Type::True
            | Type::False
            | Type::Null
    )
}

/// The value set of an array-ish type when *every* value is a singleton —
/// what strict `in_array` narrowing needs to be exact.
fn singleton_values(t: &Type) -> Option<Vec<Type>> {
    let value_ty = match t {
        Type::Array(Some(kv)) => kv.1.clone(),
        Type::List(inner) => (**inner).clone(),
        Type::Shape {
            fields,
            sealed: true,
        } => Type::union(fields.iter().map(|f| f.ty.clone()).collect()),
        _ => return None,
    };
    let parts: Vec<Type> = match value_ty {
        Type::Union(p) => p.to_vec(),
        single => vec![single],
    };
    (!parts.is_empty() && parts.iter().all(is_singleton)).then_some(parts)
}

fn literal_string_of(t: &Type) -> Option<String> {
    match t {
        Type::LiteralString(s) => Some(s.to_string()),
        _ => None,
    }
}

/// The array an index write through an undefined/`null` variable creates:
/// exactly `array{key: field_ty}` for a known literal key, a bare array for a
/// dynamic key or append (so a later `$x ?? …` isn't read as "always null").
fn vivified(key: Option<&str>, field_ty: Type) -> Type {
    match key {
        Some(k) => Type::Shape {
            fields: vec![php_types::ShapeField {
                key: Some(k.to_string()),
                optional: false,
                ty: field_ty,
            }],
            sealed: true,
        },
        None => Type::Array(None),
    }
}

/// Widen a variable's type for a write through `$var[key]`. For a shape: a known
/// literal `key` is added (or its type unioned in) as an *optional* field —
/// keeping the shape's key enumeration precise while marking the key possibly
/// present; a dynamic/append write (`key == None`) can't be named, so the shape
/// is unsealed instead. A `null` auto-vivifies ([`vivified`]); a branch-merged
/// *union* distributes the write over its arms (a write after `if`/`else`
/// merges must not be dropped — that manufactured missing-offset false
/// positives). Returns `None` for other types (arrays keep their element
/// types; a string offset write or an `ArrayAccess` object is left unchanged).
fn widen_shape_for_write(cur: &Type, key: Option<&str>, field_ty: Type) -> Option<Type> {
    match cur {
        Type::Null => Some(vivified(key, field_ty)),
        Type::Union(parts) => {
            let mut changed = false;
            let widened: Vec<Type> = parts
                .iter()
                .map(|p| match widen_shape_for_write(p, key, field_ty.clone()) {
                    Some(u) => {
                        changed = true;
                        u
                    }
                    None => p.clone(),
                })
                .collect();
            changed.then(|| Type::union(widened))
        }
        Type::Shape { fields, sealed } => {
            let mut fields = fields.clone();
            match key {
                Some(k) => {
                    match fields.iter_mut().find(|f| f.key.as_deref() == Some(k)) {
                        Some(f) => f.ty = Type::union(vec![f.ty.clone(), field_ty]),
                        None => fields.push(php_types::ShapeField {
                            key: Some(k.to_string()),
                            optional: true,
                            ty: field_ty,
                        }),
                    }
                    Some(Type::Shape {
                        fields,
                        sealed: *sealed,
                    })
                }
                None => Some(Type::Shape {
                    fields,
                    sealed: false,
                }),
            }
        }
        _ => None,
    }
}

/// Definitely an object value (`is_a`-style narrowing is only sound then —
/// those functions also accept class-name strings).
fn definitely_object_type(t: &Type) -> bool {
    match t {
        Type::Named { .. }
        | Type::EnumCase { .. }
        | Type::Object
        | Type::SelfType
        | Type::StaticType
        | Type::Parent => true,
        Type::Union(parts) => !parts.is_empty() && parts.iter().all(definitely_object_type),
        Type::Intersection(parts) => parts.iter().any(definitely_object_type),
        _ => false,
    }
}

/// Whether union member `m` is *confidently* within `ty` — concrete and
/// assignable. Used for negated asserts (`!T`): removing a member requires
/// certainty it is in `T` (the lenient `is_assignable` says yes to `mixed`,
/// which must never be subtracted).
fn confidently_in(index: &php_reflect::ReflectionIndex, m: &Type, ty: &Type) -> bool {
    !matches!(
        m,
        Type::Mixed | Type::ExplicitMixed | Type::Unknown(_) | Type::TemplateVar(_)
    ) && crate::is_assignable(index, m, ty)
}

/// A class name carried by a comparison operand: `C::class`
/// (`class-string<C>`) or a literal class-name string.
fn class_name_arg(t: &Type) -> Option<String> {
    match t {
        Type::ClassString(Some(inner)) => match &**inner {
            Type::Named { fqn, .. } => Some(fqn.to_string()),
            _ => None,
        },
        Type::LiteralString(s) if !s.is_empty() => Some(s.trim_start_matches('\\').to_string()),
        _ => None,
    }
}

/// Does executing `s` always leave the current block (so its environment never
/// flows past it)? Conservative — only unconditional terminators count.
impl TypeCtx<'_> {
    fn always_terminates(&self, s: &Stmt) -> bool {
        match &s.kind {
            StmtKind::Return(_)
            | StmtKind::Break(_)
            | StmtKind::Continue(_)
            | StmtKind::Goto(_) => true,
            StmtKind::Expr(e) => {
                matches!(&e.kind, ExprKind::Throw(_) | ExprKind::Exit(_))
                    || self.terminators.expr_terminates(e, self.interner)
            }
            StmtKind::Block(b) => b.last().is_some_and(|s| self.always_terminates(s)),
            StmtKind::If {
                then,
                elseifs,
                els: Some(els),
                ..
            } => {
                self.always_terminates(then)
                    && elseifs.iter().all(|ei| self.always_terminates(&ei.body))
                    && self.always_terminates(els)
            }
            _ => false,
        }
    }

    fn block_always_terminates(&self, stmts: &[Stmt]) -> bool {
        stmts.last().is_some_and(|s| self.always_terminates(s))
    }
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
        out.insert(k, collapse_shape_union(Type::union(parts)));
    }
    out
}

/// Every branch merge unions a variable's shape variants
/// (`array{a}|array{a,b}|…`), so a scope with many conditional key writes
/// doubles the arms at each merge — exponential without a bound. Above this
/// cap the shape arms collapse into ONE shape: the union of their key sets,
/// each key optional unless present-and-required in every arm, field types
/// unioned. Strictly wider than the exact union (sound) and bounded.
const SHAPE_UNION_ARM_CAP: usize = 6;

fn collapse_shape_union(ty: Type) -> Type {
    let Type::Union(parts) = &ty else { return ty };
    let nshapes = parts
        .iter()
        .filter(|p| matches!(p, Type::Shape { .. }))
        .count();
    if nshapes <= SHAPE_UNION_ARM_CAP {
        return ty;
    }
    let mut order: Vec<String> = Vec::new();
    let mut types: HashMap<String, Vec<Type>> = HashMap::new();
    let mut required: HashMap<String, usize> = HashMap::new();
    let mut sealed = true;
    let mut keyless_tys: Vec<Type> = Vec::new();
    let mut rest: Vec<Type> = Vec::new();
    for p in parts.iter() {
        let Type::Shape { fields, sealed: s } = p else {
            rest.push(p.clone());
            continue;
        };
        sealed &= *s;
        for f in fields {
            let Some(k) = f.key.clone() else {
                keyless_tys.push(f.ty.clone());
                continue;
            };
            if !types.contains_key(&k) {
                order.push(k.clone());
            }
            types.entry(k.clone()).or_default().push(f.ty.clone());
            if !f.optional {
                *required.entry(k).or_default() += 1;
            }
        }
    }
    if !keyless_tys.is_empty() {
        // Positional (tuple) fields don't merge by name; widen to a keyed
        // array of everything written — still bounded.
        let mut vals: Vec<Type> = types.into_values().flatten().collect();
        vals.append(&mut keyless_tys);
        rest.push(Type::Array(Some(Box::new((
            Type::union(vec![Type::Int, Type::String]),
            Type::union(vals),
        )))));
        return Type::union(rest);
    }
    let fields = order
        .into_iter()
        .map(|k| php_types::ShapeField {
            optional: required.get(&k).copied().unwrap_or(0) != nshapes,
            ty: Type::union(types.remove(&k).unwrap_or_default()),
            key: Some(k),
        })
        .collect();
    rest.push(Type::Shape { fields, sealed });
    Type::union(rest)
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

    /// Analyse the method named `method` of the first class in `src` (class
    /// context + `$this` seeded) and return the end-of-body env entry for
    /// `place` (e.g. `this->p`) — `<unset>` when absent/invalidated.
    fn place_after(src: &str, method: &str, place: &str) -> String {
        let full = format!("<?php {src}");
        let r = php_parser::parse(&full);
        assert!(!r.has_errors(), "parse errors in: {src}");
        let mut index = ReflectionIndex::new();
        index.add_file(&r.program, &r.interner);
        let scope = Scope::global();
        // Pick the class that declares `method` (fixtures may list helper
        // classes first).
        let (class_name, body) = r
            .program
            .stmts
            .iter()
            .find_map(|s| {
                let StmtKind::Class(c) = &s.kind else {
                    return None;
                };
                let body = c.members.iter().find_map(|m| match m {
                    php_ast::Member::Method(m)
                        if r.interner.resolve(m.name).eq_ignore_ascii_case(method) =>
                    {
                        m.body.as_deref()
                    }
                    _ => None,
                })?;
                Some((r.interner.resolve(c.name?).to_string(), body))
            })
            .expect("a class declaring the method");
        let mut ctx = TypeCtx::new(&index, &scope, &r.interner);
        ctx.class = Some(class_name.clone());
        ctx.vars.insert(
            "this".into(),
            Type::Named {
                fqn: class_name.into(),
                args: Vec::new(),
            },
        );
        ctx.exec_block(body);
        ctx.vars
            .get(place)
            .map(|t| t.to_string())
            .unwrap_or_else(|| "<unset>".into())
    }

    #[test]
    fn simple_assignment_chain() {
        assert_eq!(var_after("$x = 1; $y = $x + 2;", "y"), "3"); // literal arithmetic folds
        assert_eq!(var_after("$x = 'a' . 'b';", "x"), "'ab'"); // literal concat folds
        assert_eq!(var_after("$a = $b = 5;", "a"), "5");
        assert_eq!(var_after("$a = $b = 5;", "b"), "5");
    }

    #[test]
    fn many_conditional_shape_writes_stay_bounded() {
        // Each conditional key write doubles the shape-union arms at its
        // branch merge; without the collapse cap 24 writes hang the analysis
        // (2^24 arms). Completing at all — with a bounded rendering — is the
        // assertion.
        let mut src = String::from("function f(array $o) { $c = [];");
        for i in 0..24 {
            src.push_str(&format!("if ($o[{i}]) {{ $c['k{i}'] = {i}; }}"));
        }
        src.push_str(" return $c; }");
        let ty = var_after(&src, "c");
        assert!(ty.starts_with("array{") || ty.contains("array{"), "{ty}");
        assert!(ty.len() < 2000, "unbounded rendering: {} chars", ty.len());
        assert!(ty.contains("k0?") && ty.contains("k23?"), "{ty}");
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
        assert_eq!(var_after("$x = 1; $x += 2;", "x"), "3");
        assert_eq!(var_after("$s = 'a'; $s .= 'b';", "s"), "'ab'");
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

    // --- M-P0 call side-effect invalidation --------------------------------

    /// The shared fixture: a nullable property narrowed by an early-return
    /// guard, then one call whose side-effect classification is under test.
    fn guarded_class(call: &str) -> String {
        format!(
            r#"
            class X {{}}
            class C {{
                public ?X $p;
                public function reload(): void {{}}
                public function calc(): int {{ return 1; }}
                /** @phpstan-impure */
                public function calcImpure(): int {{ return 1; }}
                public function fluent(): self {{ return $this; }}
                public function initLegacy(): void {{}}
                public static function svoid(): void {{}}
                public function m() {{
                    if ($this->p === null) {{ return; }}
                    {call}
                }}
            }}
            "#
        )
    }

    #[test]
    fn void_method_on_this_invalidates_property_narrowing() {
        assert_eq!(
            place_after(&guarded_class("$this->reload();"), "m", "this->p"),
            "<unset>"
        );
    }

    #[test]
    fn value_returning_method_keeps_property_narrowing() {
        assert_eq!(
            place_after(&guarded_class("$this->calc();"), "m", "this->p"),
            "X"
        );
    }

    #[test]
    fn impure_tagged_method_invalidates_property_narrowing() {
        assert_eq!(
            place_after(&guarded_class("$this->calcImpure();"), "m", "this->p"),
            "<unset>"
        );
    }

    #[test]
    fn fluent_method_invalidates_receiver_narrowing() {
        assert_eq!(
            place_after(&guarded_class("$this->fluent();"), "m", "this->p"),
            "<unset>"
        );
    }

    #[test]
    fn self_call_to_instance_method_invalidates_this() {
        assert_eq!(
            place_after(&guarded_class("self::initLegacy();"), "m", "this->p"),
            "<unset>"
        );
    }

    #[test]
    fn self_call_to_static_method_keeps_this_narrowing() {
        assert_eq!(
            place_after(&guarded_class("self::svoid();"), "m", "this->p"),
            "X"
        );
    }

    #[test]
    fn void_function_invalidates_object_argument() {
        let src = r#"
            function f(P $p) { if ($p->name === null) { return; } mutate($p); }
            function mutate(P $p): void {}
            class P { public ?string $name; }
        "#;
        assert_eq!(var_after(src, "p->name"), "<unset>");
    }

    #[test]
    fn value_returning_function_keeps_object_argument_narrowing() {
        let src = r#"
            function f(P $p) { if ($p->name === null) { return; } probe($p); }
            function probe(P $p): int { return 1; }
            class P { public ?string $name; }
        "#;
        assert_eq!(var_after(src, "p->name"), "string");
    }

    #[test]
    fn unknown_function_invalidates_object_argument() {
        let src = r#"
            function f(P $p) { if ($p->name === null) { return; } no_such_function($p); }
            class P { public ?string $name; }
        "#;
        assert_eq!(var_after(src, "p->name"), "<unset>");
    }

    #[test]
    fn scalar_argument_narrowing_survives_side_effecting_call() {
        // $n is an int — copied, not mutable by the callee; and $p is not
        // passed, so its narrowing survives too.
        let src = r#"
            function f(P $p, int $n) { if ($p->name === null) { return; } touch1($n); }
            function touch1(int $n): void {}
            class P { public ?string $name; }
        "#;
        assert_eq!(var_after(src, "p->name"), "string");
    }

    #[test]
    fn fluent_call_spares_argument_narrowing() {
        let src = r#"
            function f(B $b, P $p) { if ($p->name === null) { return; } $b->with($p); }
            class B { public function with(P $p): self { return $this; } }
            class P { public ?string $name; }
        "#;
        assert_eq!(var_after(src, "p->name"), "string");
    }

    #[test]
    fn unmarked_constructor_spares_argument_narrowing() {
        let src = r#"
            function f(P $p) { if ($p->name === null) { return; } new H($p); }
            class H { public function __construct(P $p) {} }
            class P { public ?string $name; }
        "#;
        assert_eq!(var_after(src, "p->name"), "string");
    }

    #[test]
    fn impure_constructor_invalidates_argument_narrowing() {
        let src = r#"
            function f(P $p) { if ($p->name === null) { return; } new H($p); }
            class H {
                /** @phpstan-impure */
                public function __construct(P $p) {}
            }
            class P { public ?string $name; }
        "#;
        assert_eq!(var_after(src, "p->name"), "<unset>");
    }

    #[test]
    fn by_ref_argument_widens_to_declared_param_type() {
        let src = r#"
            function f() { $m = 'seed'; fill($m); }
            function fill(array &$out): void {}
        "#;
        assert_eq!(var_after(src, "m"), "array");
    }

    #[test]
    fn self_out_retypes_receiver() {
        // `@phpstan-self-out self<int>` mutates the receiver's generic arg.
        let src = r#"
            /** @template T */
            class Builder {
                /** @phpstan-self-out self<int> */
                public function asInt(): void {}
            }
            function f() {
                $b = new Builder();
                $b->asInt();
                $y = $b;
            }
        "#;
        assert_eq!(var_after(src, "y"), "Builder<int>");

        // A concrete self-out retypes to a different class.
        let src = r#"
            class Draft {}
            class Published {
                /** @phpstan-self-out \Draft */
                public function unpublish(): void {}
            }
            function f() {
                $p = new Published();
                $p->unpublish();
                $y = $p;
            }
        "#;
        assert_eq!(var_after(src, "y"), "Draft");
    }

    #[test]
    fn preg_match_types_matches_out_param() {
        // `$m` is the capture-group array after the call (even in a guard cond,
        // which runs unconditionally).
        let src = r#"
            function f(string $s) {
                if (preg_match('/(\d+)/', $s, $m)) {}
            }
        "#;
        assert_eq!(var_after(src, "m"), "array<int|string, string>");
        // preg_match_all: each group is a list of matches.
        let src = r#"
            function f(string $s) {
                preg_match_all('/(\d+)/', $s, $m);
            }
        "#;
        assert_eq!(var_after(src, "m"), "array<int|string, list<string>>");
        // A userland preg_match is not clobbered.
        let src = r#"
            function preg_match($a, $b, &$c): int { return 0; }
            function f(string $s) {
                preg_match('/x/', $s, $m);
            }
        "#;
        assert_ne!(var_after(src, "m"), "array<int|string, string>");
    }

    #[test]
    fn param_out_sets_post_call_type() {
        // `@param-out` beats the declared param type for the post-call value.
        let src = r#"
            function f() { $m = null; fill($m); }
            /** @param-out list<string> $out */
            function fill(?array &$out): void {}
        "#;
        assert_eq!(var_after(src, "m"), "list<string>");
    }

    #[test]
    fn enum_case_types_and_narrowing() {
        // `Suit::Hearts` is the case type; `->name`/`->value` are per-case
        // literals; `===` pins a union member and `!==` subtracts it.
        let src = r#"
            enum Suit: string {
                case Hearts = 'H';
                case Spades = 'S';
            }
            function f(Suit $s) {
                $a = Suit::Hearts;
                $n = Suit::Hearts->name;
                $v = Suit::Hearts->value;
            }
        "#;
        assert_eq!(var_after(src, "a"), "Suit::Hearts");
        assert_eq!(var_after(src, "n"), "'Hearts'");
        assert_eq!(var_after(src, "v"), "'H'");

        let src = r#"
            enum Suit {
                case Hearts;
                case Spades;
            }
            function f(Suit $s) {
                if ($s === Suit::Hearts) { $x = $s; }
                if ($s !== Suit::Hearts) { return; }
                $y = $s;
            }
        "#;
        assert_eq!(var_after(src, "x"), "Suit::Hearts|mixed");
        // The `!==` guard's fall-through pins the case too.
        assert_eq!(var_after(src, "y"), "Suit::Hearts");
    }

    // --- M-P2 non-empty arrays + count() ------------------------------------

    #[test]
    fn count_comparisons_narrow_to_non_empty() {
        let probe = |guard: &str| {
            format!(
                "/** @param array<int, string> $a */\nfunction f(array $a) {{ if ({guard}) {{ $y = $a; }} }}"
            )
        };
        for guard in [
            "count($a) > 0",
            "count($a) >= 1",
            "count($a) !== 0",
            "count($a) === 2",
            "sizeof($a) > 0",
            "count($a)",
        ] {
            assert_eq!(
                var_after(&probe(guard), "y"),
                "non-empty-array<int, string>|mixed",
                "{guard}"
            );
        }
        // Upper bounds and == 0 prove nothing about (non-)emptiness there.
        assert_eq!(
            var_after(&probe("count($a) < 5"), "y"),
            "array<int, string>|mixed"
        );
        // The falsy branch of `count($a) === 0` is non-empty.
        let src = r#"
            /** @param array<int, string> $a */
            function f(array $a) {
                if (count($a) === 0) { return; }
                $y = $a;
            }
        "#;
        assert_eq!(var_after(src, "y"), "non-empty-array<int, string>");
    }

    #[test]
    fn non_empty_doc_types_resolve_and_flow() {
        let src = r#"
            /** @param non-empty-list<string> $a */
            function f(array $a) { $y = $a; }
        "#;
        assert_eq!(var_after(src, "y"), "non-empty-list<string>");
    }

    #[test]
    fn foreach_over_non_empty_runs_at_least_once() {
        // Over a plain array the loop may not run ($last stays maybe-unset);
        // over a non-empty one the body ran, so $last is definite.
        let plain = r#"
            /** @param array<int, string> $a */
            function f(array $a) {
                foreach ($a as $v) { $last = $v; }
            }
        "#;
        assert_eq!(var_after(plain, "last"), "mixed|string");
        let non_empty = r#"
            /** @param non-empty-list<string> $a */
            function f(array $a) {
                foreach ($a as $v) { $last = $v; }
            }
        "#;
        assert_eq!(var_after(non_empty, "last"), "string");
    }

    // --- M-P2 @phpstan-assert ----------------------------------------------

    #[test]
    fn assert_tag_narrows_after_statement_call() {
        // webmozart-style: a statement-level assertion helper narrows its arg.
        let src = r#"
            function f(mixed $x) {
                assertString($x);
                $y = $x;
            }
            /** @phpstan-assert string $value */
            function assertString(mixed $value): void {}
        "#;
        assert_eq!(var_after(src, "y"), "string");
    }

    #[test]
    fn assert_if_true_narrows_condition_branch() {
        let src = r#"
            function f(?string $x) {
                if (notNull($x)) { $y = $x; }
            }
            /** @phpstan-assert-if-true !null $value */
            function notNull(mixed $value): bool { return $value !== null; }
        "#;
        assert_eq!(var_after(src, "y"), "string|mixed");
    }

    #[test]
    fn assert_if_false_narrows_else_path() {
        let src = r#"
            function f(?int $x) {
                if (hasValue($x)) { return; }
                $y = $x;
            }
            /** @phpstan-assert-if-false null $value */
            function hasValue(?int $value): bool { return $value !== null; }
        "#;
        assert_eq!(var_after(src, "y"), "null");
    }

    #[test]
    fn static_method_assert_narrows() {
        // The webmozart/assert shape: static Assert::string().
        let src = r#"
            class Assert {
                /** @phpstan-assert string $value */
                public static function string(mixed $value): void {}
            }
            function f(mixed $x) {
                Assert::string($x);
                $y = $x;
            }
        "#;
        assert_eq!(var_after(src, "y"), "string");
    }

    #[test]
    fn negated_assert_subtracts_from_union() {
        let src = r#"
            /** @param int|string $x */
            function f($x) {
                notString($x);
                $y = $x;
            }
            /** @phpstan-assert !string $value */
            function notString(mixed $value): void {}
        "#;
        assert_eq!(var_after(src, "y"), "int");
    }

    // --- M-P2 condition specifiers ------------------------------------------

    #[test]
    fn in_array_strict_narrows_to_value_set() {
        let src = r#"
            function f(string $x) {
                if (in_array($x, ['a', 'b'], true)) { $y = $x; }
            }
        "#;
        assert_eq!(var_after(src, "y"), "'a'|'b'|mixed");
        // Negative branch subtracts from an explicit union.
        let src = r#"
            /** @param 'a'|'b'|'c' $x */
            function f(string $x) {
                if (in_array($x, ['a', 'b'], true)) { return; }
                $y = $x;
            }
        "#;
        assert_eq!(var_after(src, "y"), "'c'");
        // Loose (no strict flag) narrows nothing.
        let src = r#"
            function f(string $x) {
                if (in_array($x, ['a', 'b'])) { $y = $x; }
            }
        "#;
        assert_eq!(var_after(src, "y"), "string|mixed");
    }

    #[test]
    fn array_key_exists_pins_optional_shape_key() {
        let src = r#"
            /** @param array{id: int, name?: string} $a */
            function f(array $a) {
                if (array_key_exists('name', $a)) { $y = $a; }
            }
        "#;
        assert_eq!(var_after(src, "y"), "array{id: int, name: string}|mixed");
    }

    #[test]
    fn get_class_comparison_narrows() {
        let src = r#"
            class A {}
            class B {}
            function f(object $o) {
                if (get_class($o) === A::class) { $y = $o; }
            }
        "#;
        assert_eq!(var_after(src, "y"), "A|mixed");
    }

    #[test]
    fn gettype_comparison_narrows() {
        let src = r#"
            function f(int|string $x) {
                if (gettype($x) === 'string') { $y = $x; }
                if (gettype($x) !== 'integer') { return; }
                $z = $x;
            }
        "#;
        assert_eq!(var_after(src, "y"), "string|mixed");
        assert_eq!(var_after(src, "z"), "int");
    }

    #[test]
    fn is_a_narrows_known_objects_only() {
        let src = r#"
            class A {}
            function f(object $o) {
                if (is_a($o, A::class)) { $y = $o; }
            }
        "#;
        assert_eq!(var_after(src, "y"), "A|mixed");
        // A string operand could be a class name — not narrowed to an object.
        let src = r#"
            class A {}
            function f(string $s) {
                if (is_a($s, A::class, true)) { $y = $s; }
            }
        "#;
        assert_eq!(var_after(src, "y"), "string|mixed");
    }

    #[test]
    fn string_refinement_specifiers() {
        let probe =
            |guard: &str| format!("function f(string $s) {{ if ({guard}) {{ $y = $s; }} }}");
        assert_eq!(
            var_after(&probe("str_contains($s, '@')"), "y"),
            "non-empty-string|mixed"
        );
        assert_eq!(
            var_after(&probe("ctype_digit($s)"), "y"),
            "numeric-string|mixed"
        );
        assert_eq!(
            var_after(&probe("class_exists($s)"), "y"),
            "class-string|mixed"
        );
        assert_eq!(
            var_after(&probe("function_exists($s)"), "y"),
            "callable-string|mixed"
        );
        // An empty-able needle proves nothing.
        assert_eq!(
            var_after(&probe("str_contains($s, '')"), "y"),
            "string|mixed"
        );
    }

    #[test]
    fn array_is_list_narrows_bare_array() {
        // A bare `array` gains list-ness; a typed `array<K,V>` keeps its more
        // precise element info (narrow_to prefers the finer side — sound).
        let src = r#"
            function f(array $a) {
                if (array_is_list($a)) { $y = $a; }
            }
        "#;
        assert_eq!(var_after(src, "y"), "list<mixed>|mixed");
    }

    #[test]
    fn match_arm_bodies_see_narrowed_subject() {
        // Inside an arm, the subject is the matched case — `->value` is the
        // per-case literal, not the whole backing type.
        let src = r#"
            enum Suit: string {
                case Hearts = 'H';
                case Spades = 'S';
            }
            function f(Suit $s) {
                $v = match ($s) {
                    Suit::Hearts => $s->value,
                    Suit::Spades => 'other',
                };
            }
        "#;
        assert_eq!(var_after(src, "v"), "'H'|'other'");
    }

    #[test]
    fn range_arithmetic_propagates_bounds() {
        // Guard gives $n: int<2, max>; +1 shifts to int<3, max>.
        let src = "function f(int $n) { if ($n < 2) { return; } $m = $n + 1; }";
        assert_eq!(var_after(src, "m"), "int<3, max>");
        // Doc range + literal: int<0,10> * 2 = int<0,20>.
        let src = r#"
            /** @param int<0, 10> $n */
            function f(int $n) { $m = $n * 2; }
        "#;
        assert_eq!(var_after(src, "m"), "int<0, 20>");
        // Subtraction flips the bound pairing.
        let src = r#"
            /** @param int<0, 10> $n */
            function f(int $n) { $m = 5 - $n; }
        "#;
        assert_eq!(var_after(src, "m"), "int<-5, 5>");
    }

    #[test]
    fn is_string_guard_keeps_string_refinement() {
        // `is_string` must not widen an already-refined string place.
        let src = r#"
            /** @param non-empty-string|int $x */
            function f($x) { if (is_string($x)) { $y = $x; } }
        "#;
        assert_eq!(var_after(src, "y"), "non-empty-string|mixed");
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
        // A truthy string is additionally non-falsy (not "" and not "0").
        let src = "function f(string|false|null $x) { if (!$x) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "non-falsy-string");
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
