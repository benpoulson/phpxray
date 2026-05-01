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
use php_infer::{assignable_certain, TypeMap};
use php_intern::Interner;
use php_reflect::{reflect_class, reflect_function, ReflectionIndex};
use php_resolve::{for_each_region, Scope};
use php_types::Type;

/// The type-map key (byte span) of an expression.
fn key(e: &Expr) -> (u32, u32) {
    let r = e.span.range();
    (r.start as u32, r.end as u32)
}

/// The declared return type of the function/method currently being checked, with
/// a human label for diagnostics.
struct Ret {
    declared: Type,
    label: String,
}

/// Report `return` statements that don't match their declared return type.
///
/// Types are read from the file's flow-sensitive [`TypeMap`] (`types`), so a
/// returned expression carries its *narrowed* type — `return $x;` after
/// `if ($x instanceof Foo) {…}` is checked as `Foo`, etc. We only walk the AST to
/// pair each `return` with its enclosing function/method's declared return type.
pub fn return_type_errors(
    index: &ReflectionIndex,
    program: &Program,
    interner: &Interner,
    types: &TypeMap,
    treat_phpdoc_certain: bool,
) -> Vec<Diagnostic> {
    let cx = Cx { index, interner, types, treat_phpdoc_certain };
    let mut out = Vec::new();
    for_each_region(&program.stmts, interner, |scope, region| {
        cx.collect(scope, region, &mut out);
    });
    out
}

/// The constant context for a return-type check pass (everything but the
/// per-region `scope`, which varies). Bundled so the recursive walk isn't threaded
/// through five parameters.
struct Cx<'a> {
    index: &'a ReflectionIndex,
    interner: &'a Interner,
    types: &'a TypeMap,
    treat_phpdoc_certain: bool,
}

impl Cx<'_> {
    /// Walk statements for function/class declarations (including nested/conditional
    /// ones) and check each.
    fn collect(&self, scope: &Scope, stmts: &[Stmt], out: &mut Vec<Diagnostic>) {
        for st in stmts {
            match &st.kind {
                StmtKind::Function(f) => self.check_function(scope, f, out),
                StmtKind::Class(c) => self.check_class(scope, c, out),
                StmtKind::Block(b) => self.collect(scope, b, out),
                StmtKind::If { then, elseifs, els, .. } => {
                    self.collect(scope, std::slice::from_ref(then), out);
                    for e in elseifs {
                        self.collect(scope, std::slice::from_ref(&e.body), out);
                    }
                    if let Some(e) = els {
                        self.collect(scope, std::slice::from_ref(e), out);
                    }
                }
                StmtKind::While { body, .. }
                | StmtKind::DoWhile { body, .. }
                | StmtKind::For { body, .. }
                | StmtKind::Foreach { body, .. } => self.collect(scope, std::slice::from_ref(body), out),
                StmtKind::Try { body, catches, finally } => {
                    self.collect(scope, body, out);
                    for c in catches {
                        self.collect(scope, &c.body, out);
                    }
                    if let Some(f) = finally {
                        self.collect(scope, f, out);
                    }
                }
                StmtKind::Switch { cases, .. } => {
                    for case in cases {
                        self.collect(scope, &case.body, out);
                    }
                }
                StmtKind::Declare { body: Some(b), .. } => self.collect(scope, std::slice::from_ref(b), out),
                _ => {}
            }
        }
    }

    fn check_function(&self, scope: &Scope, f: &FunctionDecl, out: &mut Vec<Diagnostic>) {
        let refl = reflect_function(scope, self.interner, f);
        if !skip_return(&refl.return_type) {
            let ret = Ret { declared: refl.return_type.clone(), label: format!("function {}()", refl.fqn) };
            self.check_returns_in(&f.body, &ret, out);
        }
        // Nested declarations inside the body.
        self.collect(scope, &f.body, out);
    }

    fn check_class(&self, scope: &Scope, c: &ClassDecl, out: &mut Vec<Diagnostic>) {
        let Some(name) = c.name else { return }; // anonymous classes carry no FQN
        let fqn = scope.qualify(self.interner.resolve(name));
        let refl = reflect_class(scope, self.interner, &fqn, c);
        for m in &c.members {
            let Member::Method(md) = m else { continue };
            let Some(body) = &md.body else { continue };
            let mname = self.interner.resolve(md.name);
            let Some(mr) = refl.methods.iter().find(|x| !x.magic && x.name.eq_ignore_ascii_case(mname)) else {
                continue;
            };
            if !skip_return(&mr.return_type) {
                let ret = Ret { declared: mr.return_type.clone(), label: format!("{}::{}()", fqn, mr.name) };
                self.check_returns_in(body, &ret, out);
            }
            self.collect(scope, body, out);
        }
    }

    /// Find every `return <expr>;` in `stmts` — descending control flow but NOT into
    /// nested function/class declarations or closures, which carry their own return
    /// types — and check each against `ret` using the flow-narrowed type map.
    fn check_returns_in(&self, stmts: &[Stmt], ret: &Ret, out: &mut Vec<Diagnostic>) {
        for st in stmts {
            match &st.kind {
                StmtKind::Return(Some(e)) => self.check_return_expr(e, ret, out),
                StmtKind::Return(None) => {} // bare `return;` — needs generator awareness.
                StmtKind::Block(b) => self.check_returns_in(b, ret, out),
                StmtKind::If { then, elseifs, els, .. } => {
                    self.check_returns_in(std::slice::from_ref(then), ret, out);
                    for ei in elseifs {
                        self.check_returns_in(std::slice::from_ref(&ei.body), ret, out);
                    }
                    if let Some(e) = els {
                        self.check_returns_in(std::slice::from_ref(e), ret, out);
                    }
                }
                StmtKind::While { body, .. }
                | StmtKind::DoWhile { body, .. }
                | StmtKind::For { body, .. }
                | StmtKind::Foreach { body, .. } => self.check_returns_in(std::slice::from_ref(body), ret, out),
                StmtKind::Switch { cases, .. } => {
                    for c in cases {
                        self.check_returns_in(&c.body, ret, out);
                    }
                }
                StmtKind::Try { body, catches, finally } => {
                    self.check_returns_in(body, ret, out);
                    for c in catches {
                        self.check_returns_in(&c.body, ret, out);
                    }
                    if let Some(f) = finally {
                        self.check_returns_in(f, ret, out);
                    }
                }
                StmtKind::Declare { body: Some(b), .. } => self.check_returns_in(std::slice::from_ref(b), ret, out),
                // Nested function/class declarations have their own return types and
                // are checked separately (by `collect`); don't descend here.
                _ => {}
            }
        }
    }

    fn check_return_expr(&self, e: &Expr, ret: &Ret, out: &mut Vec<Diagnostic>) {
        // Unmapped (e.g. inside a closure the map leaves opaque) → `mixed` → lenient.
        let actual = self.types.get(&key(e)).cloned().unwrap_or(Type::Mixed);
        if !assignable_certain(self.index, &actual, &ret.declared, self.treat_phpdoc_certain) {
            out.push(
                Diagnostic::error(
                    e.span,
                    format!("{} should return {} but returns {}", ret.label, ret.declared, actual),
                )
                .with_code("return.type"),
            );
        }
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
        let types = php_infer::type_map(&index, &r.program, &r.interner);
        return_type_errors(&index, &r.program, &r.interner, &types, true).into_iter().map(|d| d.message).collect()
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
        assert_eq!(d, ["function f() should return int but returns 'nope'"]);
    }

    #[test]
    fn return_of_local_variable_uses_flow() {
        let d = check(r#"<?php function f(): int { $x = 'a string'; return $x; }"#);
        assert_eq!(d, ["function f() should return int but returns 'a string'"]);
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
        assert_eq!(d, ["function f() should return list<int> but returns 'x'"]);
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
        assert_eq!(d, ["C::bad() should return string but returns 42"]);
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
        assert_eq!(d, ["function f() should return int but returns 'bad'"]);
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
