//! M-T7: the **return-type rule** — flag a `return $e;` whose inferred type is
//! not assignable to the function/method's declared return type.
//!
//! This is the first rule built on the type system (inference + assignability).
//! It walks each function/method body with flow analysis so a returned local
//! variable carries the type it was assigned, then checks every `return <expr>`
//! against the declared return (PHPDoc `@return` refining the native hint).
//!
//! Conservative by design: it leans on [`php_infer::is_assignable`], which is
//! lenient about unknowns, and it skips declared returns of `mixed`/`void`/`never`
//! (nothing to prove) and bare `return;` (would need generator awareness — a
//! later refinement). False positives are the thing to avoid in a linter.

use php_ast::{ClassDecl, Expr, FunctionDecl, Member, Program, Stmt, StmtKind};
use php_diagnostics::Diagnostic;
use php_infer::{is_assignable, TypeCtx};
use php_intern::Interner;
use php_reflect::{reflect_class, reflect_function, ReflectionIndex};
use php_resolve::{for_each_region, Scope};
use php_types::Type;

/// The declared return type of the function/method currently being checked, with
/// a human label for diagnostics.
struct Ret {
    declared: Type,
    label: String,
}

/// Report `return` statements that don't match their declared return type.
pub fn return_type_errors(index: &ReflectionIndex, program: &Program, interner: &Interner) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&program.stmts, interner, |scope, region| {
        collect(index, scope, interner, region, &mut out);
    });
    out
}

/// Walk statements for function/class declarations (including nested/conditional
/// ones) and check each.
fn collect(index: &ReflectionIndex, scope: &Scope, interner: &Interner, stmts: &[Stmt], out: &mut Vec<Diagnostic>) {
    for st in stmts {
        match &st.kind {
            StmtKind::Function(f) => check_function(index, scope, interner, f, out),
            StmtKind::Class(c) => check_class(index, scope, interner, c, out),
            StmtKind::Block(b) => collect(index, scope, interner, b, out),
            StmtKind::If { then, elseifs, els, .. } => {
                collect(index, scope, interner, std::slice::from_ref(then), out);
                for e in elseifs {
                    collect(index, scope, interner, std::slice::from_ref(&e.body), out);
                }
                if let Some(e) = els {
                    collect(index, scope, interner, std::slice::from_ref(e), out);
                }
            }
            StmtKind::While { body, .. }
            | StmtKind::DoWhile { body, .. }
            | StmtKind::For { body, .. }
            | StmtKind::Foreach { body, .. } => collect(index, scope, interner, std::slice::from_ref(body), out),
            StmtKind::Try { body, catches, finally } => {
                collect(index, scope, interner, body, out);
                for c in catches {
                    collect(index, scope, interner, &c.body, out);
                }
                if let Some(f) = finally {
                    collect(index, scope, interner, f, out);
                }
            }
            StmtKind::Switch { cases, .. } => {
                for case in cases {
                    collect(index, scope, interner, &case.body, out);
                }
            }
            StmtKind::Declare { body: Some(b), .. } => collect(index, scope, interner, std::slice::from_ref(b), out),
            _ => {}
        }
    }
}

fn check_function(index: &ReflectionIndex, scope: &Scope, interner: &Interner, f: &FunctionDecl, out: &mut Vec<Diagnostic>) {
    let refl = reflect_function(scope, interner, f);
    if !skip_return(&refl.return_type) {
        let mut ctx = TypeCtx::new(index, scope, interner);
        for p in &refl.params {
            ctx.vars.insert(p.name.clone(), p.ty.clone());
        }
        let ret = Ret { declared: refl.return_type.clone(), label: format!("function {}()", refl.fqn) };
        check_body(&mut ctx, &f.body, &ret, out);
    }
    // Nested declarations inside the body.
    collect(index, scope, interner, &f.body, out);
}

fn check_class(index: &ReflectionIndex, scope: &Scope, interner: &Interner, c: &ClassDecl, out: &mut Vec<Diagnostic>) {
    let Some(name) = c.name else { return }; // anonymous classes carry no FQN
    let fqn = scope.qualify(interner.resolve(name));
    let refl = reflect_class(scope, interner, &fqn, c);
    for m in &c.members {
        let Member::Method(md) = m else { continue };
        let Some(body) = &md.body else { continue };
        let mname = interner.resolve(md.name);
        let Some(mr) = refl.methods.iter().find(|x| !x.magic && x.name.eq_ignore_ascii_case(mname)) else {
            continue;
        };
        if !skip_return(&mr.return_type) {
            let mut ctx = TypeCtx::new(index, scope, interner);
            ctx.class = Some(fqn.clone());
            for p in &mr.params {
                ctx.vars.insert(p.name.clone(), p.ty.clone());
            }
            let ret = Ret { declared: mr.return_type.clone(), label: format!("{}::{}()", fqn, mr.name) };
            check_body(&mut ctx, body, &ret, out);
        }
        collect(index, scope, interner, body, out);
    }
}

/// Check a sequence of statements, threading the variable environment so a
/// returned local has the type it was assigned.
fn check_body(ctx: &mut TypeCtx, stmts: &[Stmt], ret: &Ret, out: &mut Vec<Diagnostic>) {
    for st in stmts {
        check_stmt(ctx, st, ret, out);
    }
}

fn check_stmt(ctx: &mut TypeCtx, st: &Stmt, ret: &Ret, out: &mut Vec<Diagnostic>) {
    match &st.kind {
        StmtKind::Return(Some(e)) => check_return(ctx, e, ret, out),
        // `return;` (no value) needs generator awareness to check safely — defer.
        StmtKind::Return(None) => {}
        StmtKind::Expr(e) => {
            ctx.apply_expr(e);
        }
        StmtKind::Echo(es) => {
            for e in es {
                ctx.apply_expr(e);
            }
        }
        StmtKind::Block(b) => check_body(ctx, b, ret, out),
        StmtKind::If { cond, then, elseifs, els } => {
            ctx.apply_expr(cond);
            let base = ctx.vars.clone();
            // Check each branch from the same entry env; restore between them.
            check_stmt(ctx, then, ret, out);
            for ei in elseifs {
                ctx.vars = base.clone();
                ctx.apply_expr(&ei.cond);
                check_stmt(ctx, &ei.body, ret, out);
            }
            if let Some(e) = els {
                ctx.vars = base.clone();
                check_stmt(ctx, e, ret, out);
            }
            // Advance the env past the whole `if` with proper branch merging.
            ctx.vars = base;
            ctx.exec_stmt(st);
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => {
            let base = ctx.vars.clone();
            check_stmt(ctx, body, ret, out);
            ctx.vars = base;
            ctx.exec_stmt(st);
        }
        StmtKind::Switch { cases, .. } => {
            let base = ctx.vars.clone();
            for case in cases {
                ctx.vars = base.clone();
                check_body(ctx, &case.body, ret, out);
            }
            ctx.vars = base;
            ctx.exec_stmt(st);
        }
        StmtKind::Try { body, catches, finally } => {
            let base = ctx.vars.clone();
            check_body(ctx, body, ret, out);
            for c in catches {
                ctx.vars = base.clone();
                check_body(ctx, &c.body, ret, out);
            }
            ctx.vars = base.clone();
            if let Some(f) = finally {
                check_body(ctx, f, ret, out);
            }
            ctx.vars = base;
            ctx.exec_stmt(st);
        }
        // Declarations and other statements: advance the env, don't recurse for
        // returns (nested decls are handled separately by `collect`).
        _ => {
            ctx.exec_stmt(st);
        }
    }
}

fn check_return(ctx: &mut TypeCtx, e: &Expr, ret: &Ret, out: &mut Vec<Diagnostic>) {
    let actual = ctx.infer(e);
    if !is_assignable(ctx.index, &actual, &ret.declared) {
        out.push(
            Diagnostic::error(
                e.span,
                format!("{} should return {} but returns {}", ret.label, ret.declared, actual),
            )
            .with_code("return.type"),
        );
    }
}

/// Declared return types not worth checking: `mixed` (everything fits), `void`
/// and `never` (no value is returned to check against).
fn skip_return(t: &Type) -> bool {
    matches!(t, Type::Mixed | Type::Void | Type::Never)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Parse `src`, index it, run the rule; return diagnostic messages.
    fn check(src: &str) -> Vec<String> {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors in test source");
        let mut index = ReflectionIndex::new();
        index.add_file(&r.program, &r.interner);
        return_type_errors(&index, &r.program, &r.interner).into_iter().map(|d| d.message).collect()
    }

    #[test]
    fn good_returns_are_silent() {
        assert!(check(r#"<?php function f(): int { return 1; }"#).is_empty());
        assert!(check(r#"<?php function f(): string { return 'x'; }"#).is_empty());
        assert!(check(r#"<?php function f(): float { return 1; }"#).is_empty()); // int widens
        assert!(check(r#"<?php function f(): ?int { return null; }"#).is_empty());
        assert!(check(r#"<?php function f(): int|string { return 'x'; }"#).is_empty());
    }

    #[test]
    fn bad_scalar_return_is_flagged() {
        let d = check(r#"<?php function f(): int { return 'nope'; }"#);
        assert_eq!(d, ["function f() should return int but returns string"]);
    }

    #[test]
    fn return_of_local_variable_uses_flow() {
        let d = check(r#"<?php function f(): int { $x = 'a string'; return $x; }"#);
        assert_eq!(d, ["function f() should return int but returns string"]);
        // A correctly-typed local is silent.
        assert!(check(r#"<?php function f(): int { $x = 5; return $x; }"#).is_empty());
    }

    #[test]
    fn param_typed_return() {
        assert!(check(r#"<?php function f(int $n): int { return $n; }"#).is_empty());
        let d = check(r#"<?php function f(string $s): int { return $s; }"#);
        assert_eq!(d, ["function f() should return int but returns string"]);
    }

    #[test]
    fn phpdoc_return_refines_native() {
        // @return list<int> is the declared type; returning a string is wrong.
        let d = check(
            r#"<?php
            /** @return list<int> */
            function f(): array { return 'x'; }"#,
        );
        assert_eq!(d, ["function f() should return list<int> but returns string"]);
    }

    #[test]
    fn method_returns_checked_with_class_context() {
        let d = check(
            r#"<?php
            class C {
                public function good(): int { return 1; }
                public function bad(): string { return 42; }
            }"#,
        );
        assert_eq!(d, ["C::bad() should return string but returns int"]);
    }

    #[test]
    fn self_and_this_returns_are_lenient() {
        assert!(check(
            r#"<?php
            class C {
                public function self_(): self { return $this; }
                public function new_(): static { return new static(); }
            }"#
        )
        .is_empty());
    }

    #[test]
    fn class_return_uses_hierarchy() {
        // Returning a subclass where the parent is declared is fine; an unrelated
        // class is flagged.
        assert!(check(
            r#"<?php
            class Animal {}
            class Dog extends Animal {}
            function make(): Animal { return new Dog(); }"#
        )
        .is_empty());
        let d = check(
            r#"<?php
            class Animal {}
            class Widget {}
            function make(): Animal { return new Widget(); }"#,
        );
        assert_eq!(d, ["function make() should return Animal but returns Widget"]);
    }

    #[test]
    fn mixed_void_never_are_skipped() {
        assert!(check(r#"<?php function f() { return 'anything'; }"#).is_empty()); // no declared type
        assert!(check(r#"<?php function f(): mixed { return 1; }"#).is_empty());
        assert!(check(r#"<?php function f(): void { return; }"#).is_empty());
    }

    #[test]
    fn return_in_branch_is_checked() {
        let d = check(
            r#"<?php
            function f(bool $c): int {
                if ($c) { return 'bad'; }
                return 0;
            }"#,
        );
        assert_eq!(d, ["function f() should return int but returns string"]);
    }

    #[test]
    fn unknown_classes_are_lenient() {
        // Both the declared type and the returned value are built-in classes the
        // reflection index doesn't know — assume compatible, don't flag.
        assert!(check(
            r#"<?php function f(): \DateTimeInterface { return new \DateTimeImmutable(); }"#
        )
        .is_empty());
    }
}
