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

/// A flow-narrowing fact about a single variable, deduced from a condition.
/// Only *sound* refinements are produced (the branch guarantees them), so
/// under-narrowing is safe and over-narrowing — which would cause false
/// positives in rules reading the type map — never happens.
enum Narrow {
    /// The variable definitely has this type in the branch (e.g. `instanceof`,
    /// `is_int($x)`, `$x === null`).
    To(Type),
    /// `null` is removed from the variable's type (e.g. `$x !== null`, a truthy
    /// `if ($x)`, `!is_null($x)`).
    StripNull,
}

impl TypeCtx<'_> {
    /// Seed parameters from a function/method's reflected signature, then analyse
    /// its body, leaving `self.vars` reflecting the end-of-body environment.
    pub fn analyze_function_body(&mut self, f: &FunctionDecl) {
        let refl = php_reflect::reflect_function(self.scope, self.interner, f);
        for p in &refl.params {
            self.vars.insert(p.name.clone(), p.ty.clone());
        }
        self.exec_block(&f.body);
    }

    /// Analyse a sequence of statements, updating `self.vars`.
    pub fn exec_block(&mut self, stmts: &[Stmt]) {
        for s in stmts {
            self.exec_stmt(s);
        }
    }

    /// Analyse one statement, updating `self.vars`.
    pub fn exec_stmt(&mut self, s: &Stmt) {
        match &s.kind {
            StmtKind::Expr(e) => {
                self.apply_expr(e);
            }
            StmtKind::Echo(es) => {
                for e in es {
                    self.apply_expr(e);
                }
            }
            StmtKind::Return(Some(e)) => {
                self.apply_expr(e);
            }
            StmtKind::Block(b) => self.exec_block(b),
            StmtKind::If { cond, then, elseifs, els } => {
                self.apply_expr(cond);
                self.exec_if(cond, then, elseifs, els.as_deref());
            }
            // A loop body may run zero or more times: merge the pre-loop env with
            // the post-body env.
            StmtKind::While { cond, body } => {
                self.apply_expr(cond);
                self.exec_maybe(body);
            }
            StmtKind::DoWhile { body, cond } => {
                // The body always runs at least once.
                self.exec_stmt(body);
                self.apply_expr(cond);
            }
            StmtKind::For { init, cond, update, body } => {
                for e in init {
                    self.apply_expr(e);
                }
                for e in cond.iter().chain(update) {
                    self.apply_expr(e);
                }
                self.exec_maybe(body);
            }
            StmtKind::Foreach { subject, key, value, body, .. } => {
                self.exec_foreach(subject, key.as_ref(), value, body);
            }
            StmtKind::Switch { subject, cases } => {
                self.apply_expr(subject);
                let base = self.vars.clone();
                let mut envs = vec![base.clone()];
                for case in cases {
                    self.vars = base.clone();
                    self.exec_block(&case.body);
                    envs.push(std::mem::take(&mut self.vars));
                }
                self.vars = merge(envs);
            }
            StmtKind::Try { body, catches, finally } => {
                self.exec_block(body);
                for c in catches {
                    self.exec_block(&c.body);
                }
                if let Some(f) = finally {
                    self.exec_block(f);
                }
            }
            // Declarations / non-binding statements: nothing to record here.
            _ => {}
        }
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

    /// Analyse an `if`/`elseif`/`else` chain, applying condition **narrowing** to
    /// each branch's entry environment and merging the branch exits.
    ///
    /// Only the environments of branches that can *fall through* (don't
    /// unconditionally `return`/`throw`/`break`/…) flow past the `if`. This is
    /// what makes a guard clause narrow: after `if ($x === null) { return; }` the
    /// continuation sees `$x` with `null` stripped.
    fn exec_if(&mut self, cond: &Expr, then: &Stmt, elseifs: &[php_ast::ElseIf], els: Option<&Stmt>) {
        let base = self.vars.clone();
        let mut envs: Vec<Env> = Vec::new();

        // then-branch: the condition is truthy here.
        let then_facts = self.narrow_facts(cond, true);
        self.vars = base.clone();
        self.apply_facts(&then_facts);
        self.exec_stmt(then);
        if !always_terminates(then) {
            envs.push(std::mem::take(&mut self.vars));
        }

        // Facts that hold once every preceding condition is false.
        let mut else_facts = self.narrow_facts(cond, false);

        for ei in elseifs {
            self.vars = base.clone();
            self.apply_facts(&else_facts);
            self.apply_expr(&ei.cond);
            let pos = self.narrow_facts(&ei.cond, true);
            self.apply_facts(&pos);
            self.exec_stmt(&ei.body);
            if !always_terminates(&ei.body) {
                envs.push(std::mem::take(&mut self.vars));
            }
            // Subsequent branches additionally know this elseif was false.
            else_facts.extend(self.narrow_facts(&ei.cond, false));
        }

        match els {
            Some(e) => {
                self.vars = base.clone();
                self.apply_facts(&else_facts);
                self.exec_stmt(e);
                if !always_terminates(e) {
                    envs.push(std::mem::take(&mut self.vars));
                }
            }
            // No `else`: the fall-through path took no branch, so every condition
            // is false there — apply the accumulated negative facts.
            None => {
                let mut fall = base.clone();
                apply_facts_to(&mut fall, &else_facts, self.index);
                envs.push(fall);
            }
        }

        // If every branch terminated (and there was an `else`), code after the
        // `if` is unreachable; keep the base env rather than panicking on empty.
        self.vars = if envs.is_empty() { base } else { merge(envs) };
    }

    /// Collect the narrowing facts implied by `cond` evaluating to `truthy`.
    fn narrow_facts(&self, cond: &Expr, truthy: bool) -> Vec<(String, Narrow)> {
        let mut out = Vec::new();
        self.collect_facts(cond, truthy, &mut out);
        out
    }

    fn collect_facts(&self, cond: &Expr, truthy: bool, out: &mut Vec<(String, Narrow)>) {
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
                // `a || b` true ⇒ at least one holds. A variable can only be
                // asserted if *both* operands constrain it — then it is the *union*
                // of the two narrowings (`$n instanceof A || $n instanceof B`
                // ⇒ `$n: A|B`). Variables constrained by only one side are dropped.
                BinOp::BoolOr | BinOp::LogicalOr if truthy => {
                    let l = self.narrow_facts(lhs, true);
                    let r = self.narrow_facts(rhs, true);
                    for (name, ln) in &l {
                        let Some((_, rn)) = r.iter().find(|(n, _)| n == name) else { continue };
                        match (ln, rn) {
                            (Narrow::To(lt), Narrow::To(rt)) => out.push((
                                name.clone(),
                                Narrow::To(Type::union(vec![lt.clone(), rt.clone()])),
                            )),
                            (Narrow::StripNull, Narrow::StripNull) => {
                                out.push((name.clone(), Narrow::StripNull))
                            }
                            _ => {}
                        }
                    }
                }
                // `$x === null` true ⇒ $x is null; false ⇒ null stripped.
                BinOp::Identical | BinOp::Eq => self.null_cmp(lhs, rhs, truthy, out),
                BinOp::NotIdentical | BinOp::NotEq => self.null_cmp(lhs, rhs, !truthy, out),
                _ => {}
            },
            ExprKind::Instanceof { expr, class } if truthy => {
                if let (Some(name), Some(t)) = (self.var_name(expr), self.class_type(class)) {
                    out.push((name, Narrow::To(t)));
                }
            }
            ExprKind::Call { callee, args } => {
                if let ExprKind::Name(n) = &callee.kind {
                    let fname = last_segment(&n.text).to_ascii_lowercase();
                    if let Some(arg0) = args.first() {
                        if let Some(name) = self.var_name(&arg0.value) {
                            if truthy {
                                if let Some(t) = predicate_type(&fname) {
                                    out.push((name, Narrow::To(t)));
                                }
                            } else if fname == "is_null" {
                                out.push((name, Narrow::StripNull));
                            }
                        }
                    }
                }
            }
            // A bare truthy variable (`if ($x)`) is non-null in the then-branch.
            _ if truthy => {
                if let Some(name) = self.var_name(cond) {
                    out.push((name, Narrow::StripNull));
                }
            }
            _ => {}
        }
    }

    /// `$x <cmp> null` / `null <cmp> $x`. `is_null` = whether the comparison
    /// asserts the variable *is* null in this branch.
    fn null_cmp(&self, lhs: &Expr, rhs: &Expr, is_null: bool, out: &mut Vec<(String, Narrow)>) {
        let var = if self.is_null_lit(rhs) {
            self.var_name(lhs)
        } else if self.is_null_lit(lhs) {
            self.var_name(rhs)
        } else {
            None
        };
        if let Some(name) = var {
            out.push((name, if is_null { Narrow::To(Type::Null) } else { Narrow::StripNull }));
        }
    }

    fn apply_facts(&mut self, facts: &[(String, Narrow)]) {
        let idx = self.index;
        let mut vars = std::mem::take(&mut self.vars);
        apply_facts_to(&mut vars, facts, idx);
        self.vars = vars;
    }

    /// The simple variable name (without `$`) of `e`, or `None` (`$this` is never
    /// narrowed).
    fn var_name(&self, e: &Expr) -> Option<String> {
        match &e.kind {
            ExprKind::Variable(sym) => {
                let n = self.interner.resolve(*sym);
                (n != "this").then(|| n.to_string())
            }
            _ => None,
        }
    }

    fn is_null_lit(&self, e: &Expr) -> bool {
        matches!(&e.kind, ExprKind::Name(n) if n.text.eq_ignore_ascii_case("null"))
    }

    /// Analyse a body that may or may not run (a loop), merging with the env from
    /// before it.
    fn exec_maybe(&mut self, body: &Stmt) {
        let base = self.vars.clone();
        self.exec_stmt(body);
        let after = std::mem::take(&mut self.vars);
        self.vars = merge(vec![base, after]);
    }

    fn exec_foreach(&mut self, subject: &Expr, key: Option<&Expr>, value: &Expr, body: &Stmt) {
        let subj_ty = self.apply_expr(subject);
        let (k, v) = iter_kv(&subj_ty);
        let base = self.vars.clone();
        // Bind key/value for the body's scope.
        if let Some(key) = key {
            self.bind_target(key, &k);
        }
        self.bind_target(value, &v);
        self.exec_stmt(body);
        let after = std::mem::take(&mut self.vars);
        // The loop may not run, so merge with the pre-loop env.
        self.vars = merge(vec![base, after]);
    }

    // -- Recording pass (builds the type map) ------------------------------
    //
    // These mirror the `exec_*` methods above but additionally record each
    // expression's inferred type into `map` at its *current* (narrowed) flow
    // point. Splitting it this way is what makes expressions inside
    // `if`/`elseif`/`else`/loop bodies typed against the narrowed environment
    // (e.g. `$node->name` after `if ($node instanceof Stmt\Namespace_)`), which a
    // single up-front walk over the statement could not do. The environment
    // transitions (narrowing, merging, termination) are identical to `exec_*`.

    /// [`exec_block`], recording every expression's type into `map`.
    pub fn record_block(&mut self, stmts: &[Stmt], map: &mut RecMap) {
        for s in stmts {
            self.record_stmt(s, map);
        }
    }

    /// Record every sub-expression of `e` at the current environment.
    fn rec_here(&self, e: &Expr, map: &mut RecMap) {
        php_ast::walk::for_each_subexpr(e, &mut |x| {
            map.insert(span_key(x), self.infer(x));
        });
    }

    fn record_stmt(&mut self, s: &Stmt, map: &mut RecMap) {
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
            // Other statements (global/unset/static/declare/const/…) carry no
            // narrowing-sensitive branch bodies: record their expressions flatly
            // and let `exec_stmt` advance the environment as before.
            _ => {
                php_ast::walk::for_each_expr_in_scope(s, &mut |e| {
                    map.insert(span_key(e), self.infer(e));
                });
                self.exec_stmt(s);
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

        let then_facts = self.narrow_facts(cond, true);
        self.vars = base.clone();
        self.apply_facts(&then_facts);
        self.record_stmt(then, map);
        if !always_terminates(then) {
            envs.push(std::mem::take(&mut self.vars));
        }

        let mut else_facts = self.narrow_facts(cond, false);
        for ei in elseifs {
            self.vars = base.clone();
            self.apply_facts(&else_facts);
            self.rec_here(&ei.cond, map);
            self.apply_expr(&ei.cond);
            let pos = self.narrow_facts(&ei.cond, true);
            self.apply_facts(&pos);
            self.record_stmt(&ei.body, map);
            if !always_terminates(&ei.body) {
                envs.push(std::mem::take(&mut self.vars));
            }
            else_facts.extend(self.narrow_facts(&ei.cond, false));
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
        let base = self.vars.clone();
        self.record_stmt(body, map);
        let after = std::mem::take(&mut self.vars);
        self.vars = merge(vec![base, after]);
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
fn apply_facts_to(vars: &mut Env, facts: &[(String, Narrow)], index: &php_reflect::ReflectionIndex) {
    for (name, n) in facts {
        let cur = vars.get(name).cloned().unwrap_or(Type::Mixed);
        let nt = match n {
            Narrow::To(t) => narrow_to(&cur, t, index),
            Narrow::StripNull => strip_null(&cur),
        };
        vars.insert(name.clone(), nt);
    }
}

/// Refine `cur` to `t`, keeping `cur` when it is already a (more precise) subtype
/// of `t`. `mixed`/`Unknown` always adopt `t` (that's the point of `instanceof`/
/// `is_*` narrowing). Sound: the branch guarantees the value is a `t`.
fn narrow_to(cur: &Type, t: &Type, index: &php_reflect::ReflectionIndex) -> Type {
    match cur {
        Type::Mixed | Type::Unknown(_) => t.clone(),
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
        assert_eq!(var_after("$a = $b = 5;", "a"), "int");
        assert_eq!(var_after("$a = $b = 5;", "b"), "int");
    }

    #[test]
    fn reassignment_updates_type() {
        assert_eq!(var_after("$x = 1; $x = 'now a string';", "x"), "string");
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
        assert_eq!(var_after(src, "x"), "int|string");
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
        assert_eq!(var_after(src, "y"), "Foo|int");
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
        assert_eq!(var_after(src, "x"), "int|mixed");
    }
}
