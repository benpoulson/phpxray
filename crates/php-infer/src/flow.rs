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
use php_ast::{Expr, ExprKind, FunctionDecl, Stmt, StmtKind};
use php_types::Type;
use std::collections::HashMap;

/// A variable environment: name (without `$`) → type.
type Env = HashMap<String, Type>;

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
                self.exec_if(then, elseifs, els.as_deref());
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

    /// Analyse an `if`/`elseif`/`else` chain, merging the branch environments.
    fn exec_if(&mut self, then: &Stmt, elseifs: &[php_ast::ElseIf], els: Option<&Stmt>) {
        let base = self.vars.clone();
        let mut envs = Vec::new();

        self.vars = base.clone();
        self.exec_stmt(then);
        envs.push(std::mem::take(&mut self.vars));

        for ei in elseifs {
            self.vars = base.clone();
            self.apply_expr(&ei.cond);
            self.exec_stmt(&ei.body);
            envs.push(std::mem::take(&mut self.vars));
        }

        match els {
            Some(e) => {
                self.vars = base.clone();
                self.exec_stmt(e);
                envs.push(std::mem::take(&mut self.vars));
            }
            // No `else`: the "no branch taken" path keeps the base env.
            None => envs.push(base),
        }
        self.vars = merge(envs);
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
