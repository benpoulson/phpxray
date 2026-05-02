//! M-T5: **flow-sensitive statement analysis**.
//!
//! Expression inference ([`crate::TypeCtx::infer`]) reads variable types from an
//! environment but never populates it. This module walks statements and *builds*
//! that environment: assignments record the assigned type, `foreach` binds its
//! key/value variables, function parameters seed from their reflected types, and
//! conditional branches merge by unioning each variable's type across paths.
//!
//! It is a single forward pass — loop bodies are analysed once (no fixpoint) and
//! a variable assigned on only some paths widens to include its prior/`mixed`
//! value. This is the approximation phpstan-style linters use; it is sound enough
//! to drive diagnostics and never panics.

use crate::TypeCtx;
use php_ast::{BinOp, Expr, ExprKind, FunctionDecl, Stmt, StmtKind, UnOp};
use php_types::Type;
use std::collections::HashMap;

/// A variable environment: name (without `$`) → type.
type Env = HashMap<String, Type>;

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
            ExprKind::Assign { target, rhs } | ExprKind::AssignRef { target, rhs } => {
                let t = self.apply_expr(rhs);
                self.bind_target(target, &t);
                t
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
                    self.vars.insert(name, ty.clone());
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

    /// Collect the narrowing facts implied by `cond` evaluating to `truthy`.
    fn narrow_facts(&self, cond: &Expr, truthy: bool) -> Vec<Fact> {
        let mut out = Vec::new();
        self.collect_facts(cond, truthy, &mut out);
        out
    }

    fn collect_facts(&self, cond: &Expr, truthy: bool, out: &mut Vec<Fact>) {
        match &cond.kind {
            ExprKind::Paren(inner) => self.collect_facts(inner, truthy, out),
            ExprKind::Unary { op: UnOp::Not, expr } => self.collect_facts(expr, !truthy, out),
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
                        let narrowed = subtract_union(&cur, |m| confident_subclass(m, &t, self.index));
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
                                out.push((place, strip_null(&self.infer(&arg0.value))));
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
        let Some(place) = self.place_key(operand) else { return };
        let t = match (lit, eq) {
            (Type::Null, true) => Type::Null,
            (Type::Null, false) => strip_null(&self.infer(operand)),
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
            ExprKind::Prop { base, name: php_ast::MemberName::Ident(p), nullsafe: false } => {
                let ExprKind::Variable(b) = &base.kind else { return None };
                Some(format!("{}->{}", self.interner.resolve(*b), self.interner.resolve(*p)))
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
            ExprKind::Clone(x) | ExprKind::Print(x) | ExprKind::Throw(x) | ExprKind::ErrorSuppress(x)
            | ExprKind::YieldFrom(x) | ExprKind::Eval(x) | ExprKind::Empty(x)
            | ExprKind::PreInc(x) | ExprKind::PreDec(x) | ExprKind::PostInc(x) | ExprKind::PostDec(x) => {
                self.rec_here(x, map)
            }
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
            ExprKind::Binary { op: BinOp::BoolAnd | BinOp::LogicalAnd, lhs, rhs } => {
                self.rec_here(lhs, map);
                self.rec_under(lhs, true, rhs, map);
            }
            ExprKind::Binary { op: BinOp::BoolOr | BinOp::LogicalOr, lhs, rhs } => {
                self.rec_here(lhs, map);
                self.rec_under(lhs, false, rhs, map);
            }
            ExprKind::Binary { lhs, rhs, .. }
            | ExprKind::Assign { target: lhs, rhs }
            | ExprKind::AssignOp { target: lhs, rhs, .. }
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
            }
            ExprKind::MethodCall { recv, method, args, .. } => {
                self.rec_here(recv, map);
                self.rec_member(method, map);
                self.rec_args(args, map);
            }
            ExprKind::StaticCall { class, method, args } => {
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
            // Leaves and own-scope forms (closures/arrow-fns/yield) — nothing more
            // to record at this scope (`e` itself is already recorded above).
            _ => {}
        }
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
            let (Some(name), Some(dt)) = (v.name, v.ty) else { continue };
            let t = php_reflect::resolve_doc_type(self.scope, &[], &dt);
            let cur = self.vars.get(&name).cloned().unwrap_or(Type::Mixed);
            let narrowed = narrow_to(&cur, &t, self.index);
            self.vars.insert(name, narrowed);
        }
    }

    fn record_stmt(&mut self, s: &Stmt, map: &mut RecMap) {
        self.apply_inline_var(s);
        match &s.kind {
            StmtKind::Expr(e) => {
                self.rec_here(e, map);
                self.apply_expr(e);
            }
            StmtKind::Echo(es) => {
                for e in es {
                    self.rec_here(e, map);
                    self.apply_expr(e);
                }
            }
            StmtKind::Return(Some(e)) => {
                self.rec_here(e, map);
                self.apply_expr(e);
            }
            StmtKind::Block(b) => self.record_block(b, map),
            StmtKind::If { cond, then, elseifs, els } => {
                self.rec_here(cond, map);
                self.apply_expr(cond);
                self.record_if(cond, then, elseifs, els.as_deref(), map);
            }
            StmtKind::While { cond, body } => {
                self.rec_here(cond, map);
                self.apply_expr(cond);
                self.record_maybe(body, map);
            }
            StmtKind::DoWhile { body, cond } => {
                self.record_stmt(body, map);
                self.rec_here(cond, map);
                self.apply_expr(cond);
            }
            StmtKind::For { init, cond, update, body } => {
                for e in init {
                    self.rec_here(e, map);
                    self.apply_expr(e);
                }
                for e in cond.iter().chain(update) {
                    self.rec_here(e, map);
                    self.apply_expr(e);
                }
                self.record_maybe(body, map);
            }
            StmtKind::Foreach { subject, key, value, body, .. } => {
                self.record_foreach(subject, key.as_ref(), value, body, map);
            }
            StmtKind::Switch { subject, cases } => {
                self.rec_here(subject, map);
                self.apply_expr(subject);
                let base = self.vars.clone();
                let mut envs = vec![base.clone()];
                for case in cases {
                    self.vars = base.clone();
                    if let Some(t) = &case.test {
                        self.rec_here(t, map);
                    }
                    self.record_block(&case.body, map);
                    envs.push(std::mem::take(&mut self.vars));
                }
                self.vars = merge(envs);
            }
            StmtKind::Try { body, catches, finally } => {
                self.record_block(body, map);
                for c in catches {
                    self.record_block(&c.body, map);
                }
                if let Some(f) = finally {
                    self.record_block(f, map);
                }
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

    fn record_if(
        &mut self,
        cond: &Expr,
        then: &Stmt,
        elseifs: &[php_ast::ElseIf],
        els: Option<&Stmt>,
        map: &mut RecMap,
    ) {
        let base = self.vars.clone();
        let mut envs: Vec<Env> = Vec::new();

        // Facts resolve against the branch-entry env (`base`); compute before the
        // then-branch mutates `self.vars`. (Mirrors `exec_if`.)
        let then_facts = self.narrow_facts(cond, true);
        let mut else_facts = self.narrow_facts(cond, false);

        self.vars = base.clone();
        self.apply_facts(&then_facts);
        self.record_stmt(then, map);
        if !always_terminates(then) {
            envs.push(std::mem::take(&mut self.vars));
        }

        for ei in elseifs {
            self.vars = base.clone();
            self.apply_facts(&else_facts);
            let pos = self.narrow_facts(&ei.cond, true);
            let neg = self.narrow_facts(&ei.cond, false);
            self.rec_here(&ei.cond, map);
            self.apply_facts(&pos);
            self.apply_expr(&ei.cond);
            self.record_stmt(&ei.body, map);
            if !always_terminates(&ei.body) {
                envs.push(std::mem::take(&mut self.vars));
            }
            else_facts.extend(neg);
        }

        match els {
            Some(e) => {
                self.vars = base.clone();
                self.apply_facts(&else_facts);
                self.record_stmt(e, map);
                if !always_terminates(e) {
                    envs.push(std::mem::take(&mut self.vars));
                }
            }
            None => {
                let mut fall = base.clone();
                apply_facts_to(&mut fall, &else_facts, self.index);
                envs.push(fall);
            }
        }

        self.vars = if envs.is_empty() { base } else { merge(envs) };
    }

    fn record_maybe(&mut self, body: &Stmt, map: &mut RecMap) {
        self.widen_loop_assignments(body);
        let base = self.vars.clone();
        self.record_stmt(body, map);
        let after = std::mem::take(&mut self.vars);
        self.vars = merge(vec![base, after]);
    }

    /// Before recording a loop body, generalize the *literal* type of any simple
    /// variable assigned inside it. A flag set `false` before the loop and `true`
    /// (or vice-versa) within it is loop-carried, so a use earlier in source order
    /// may see either value across iterations — treating it as the constant literal
    /// `false` would yield spurious `if.alwaysFalse`. We don't iterate to fixpoint,
    /// so this single widening stands in for it (only literal scalars are touched).
    fn widen_loop_assignments(&mut self, body: &Stmt) {
        let interner = self.interner;
        let mut assigned: std::collections::HashSet<String> = std::collections::HashSet::new();
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
                    self.vars.insert(name, g);
                }
            }
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
        let (k, v) = iter_kv(&subj_ty);
        self.widen_loop_assignments(body);
        let base = self.vars.clone();
        if let Some(key) = key {
            self.bind_target(key, &k);
            self.rec_here(key, map);
        }
        self.bind_target(value, &v);
        self.rec_here(value, map);
        self.record_stmt(body, map);
        let after = std::mem::take(&mut self.vars);
        self.vars = merge(vec![base, after]);
    }
}

/// Span key for the type map: an expression's `(start, end)` byte range.
fn span_key(e: &Expr) -> (u32, u32) {
    let r = e.span.range();
    (r.start as u32, r.end as u32)
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

/// Remove `null` from a type. `?T` → `T`; a union drops its `null` arm; a bare
/// `null` becomes `never` (the branch is unreachable).
fn strip_null(t: &Type) -> Type {
    match t {
        Type::Nullable(inner) => (**inner).clone(),
        Type::Null => Type::Never,
        Type::Union(parts) => {
            let kept: Vec<Type> = parts.iter().filter(|p| !matches!(p, Type::Null)).cloned().collect();
            Type::union(kept)
        }
        other => other.clone(),
    }
}

/// Remove the always-falsy members (`null`, `false`) from a type — the refinement
/// a truthy `if ($x)` guarantees. `string|false` → `string`, `?T` → `T`,
/// `bool` → `true`. Conservative: other types keep their value (a truthy `int`
/// is still `int`; we don't introduce non-zero-int types).
fn strip_falsy(t: &Type) -> Type {
    match t {
        Type::Nullable(inner) => strip_falsy(inner),
        Type::Null | Type::False => Type::Never,
        Type::Bool => Type::True,
        Type::Union(parts) => {
            let kept: Vec<Type> = parts
                .iter()
                .filter(|p| !matches!(p, Type::Null | Type::False))
                .cloned()
                .collect();
            Type::union(kept)
        }
        other => other.clone(),
    }
}

/// Remove `false` from a type (a `$x !== false` guard). `bool` → `true`; a union
/// drops its `false` arm; bare `false` → `never`. `null` is preserved.
fn strip_false(t: &Type) -> Type {
    match t {
        Type::False => Type::Never,
        Type::Bool => Type::True,
        Type::Union(parts) => {
            let kept: Vec<Type> = parts.iter().filter(|p| !matches!(p, Type::False)).cloned().collect();
            Type::union(kept)
        }
        Type::Nullable(inner) => Type::Nullable(Box::new(strip_false(inner))),
        other => other.clone(),
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
    let Type::Union(parts) = cur else { return cur.clone() };
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
    let (Type::Named { fqn: mf, .. }, Type::Named { fqn: tf, .. }) = (m, t) else { return false };
    if mf.eq_ignore_ascii_case(tf) {
        return true;
    }
    index.class(mf).is_some() && index.class(tf).is_some() && index.is_subclass_of(mf, tf)
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

/// The last `\`-separated segment of a (possibly-qualified) name.
fn last_segment(name: &str) -> &str {
    name.rsplit('\\').next().unwrap_or(name)
}

/// Does executing `s` always leave the current block (so its environment never
/// flows past it)? Conservative — only unconditional terminators count.
fn always_terminates(s: &Stmt) -> bool {
    match &s.kind {
        StmtKind::Return(_) | StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Goto(_) => true,
        StmtKind::Expr(e) => matches!(&e.kind, ExprKind::Throw(_) | ExprKind::Exit(_)),
        StmtKind::Block(b) => b.last().is_some_and(always_terminates),
        StmtKind::If { then, elseifs, els: Some(els), .. } => {
            always_terminates(then)
                && elseifs.iter().all(|ei| always_terminates(&ei.body))
                && always_terminates(els)
        }
        _ => false,
    }
}

/// The (key, value) element types yielded when iterating a type.
fn iter_kv(t: &Type) -> (Type, Type) {
    match t {
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => (kv.0.clone(), kv.1.clone()),
        Type::List(v) => (Type::Int, (**v).clone()),
        _ => (Type::Mixed, Type::Mixed),
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
        let parts: Vec<Type> = envs.iter().map(|e| e.get(&k).cloned().unwrap_or(Type::Mixed)).collect();
        out.insert(k, Type::union(parts));
    }
    out
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
        ctx.vars.get(var).map(|t| t.to_string()).unwrap_or_else(|| "<unset>".into())
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
        assert_eq!(var_after("$x = 1; $x = 'now a string';", "x"), "'now a string'");
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
    fn negative_is_string_subtracts_from_union() {
        // The else-branch of `is_string($x)` removes the `string` arm of a union.
        let src = "function f(string|int $x) { if (is_string($x)) { return; } $y = $x; }";
        assert_eq!(var_after(src, "y"), "int");
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
        let src = "function f($x) { if (!($x instanceof A || $x instanceof B)) { return; } $y = $x; }";
        let got = var_after(src, "y");
        assert!(got == "A|B" || got == "B|A", "expected A|B union, got {got}");
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
