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

use crate::{decls, function_like};
use php_ast::{ClassDecl, Expr, FunctionDecl, Member, Program, Stmt};
use php_diagnostics::Diagnostic;
use php_infer::TypeMap;
use php_intern::Interner;
use php_reflect::{reflect_class, reflect_function, ReflectionIndex};
use php_resolve::Scope;
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
    /// Native-only declared return (for treatPhpDocTypesAsCertain=false checking).
    native_declared: Type,
    label: String,
    /// `--fix`: one shared repair for a provably-wrong doc narrowing — every
    /// finding of this function-like carries the identical replacement (the
    /// applier dedups them).
    fix: Option<php_diagnostics::ReplaceFix>,
}

/// Report `return` statements that don't match their declared return type.
///
/// Types are read from the file's flow-sensitive [`TypeMap`] (`types`), so a
/// returned expression carries its *narrowed* type — `return $x;` after
/// `if ($x instanceof Foo) {…}` is checked as `Foo`, etc. We only walk the AST to
/// pair each `return` with its enclosing function/method's declared return type.
#[allow(clippy::too_many_arguments)]
pub fn return_type_errors(
    index: &ReflectionIndex,
    program: &Program,
    interner: &Interner,
    types: &TypeMap,
    treat_phpdoc_certain: bool,
    check_nullables: bool,
    report_maybes: bool,
    fix_source: Option<&str>,
) -> Vec<Diagnostic> {
    let cx = Cx {
        index,
        interner,
        types,
        treat_phpdoc_certain,
        check_nullables,
        report_maybes,
        fix_source,
    };
    let mut out = Vec::new();
    decls::for_each_named_function_in(program, interner, &mut |scope, function| {
        cx.check_function(scope, function, &mut out);
    });
    decls::for_each_class_like_in(program, interner, &mut |scope, fqn, class| {
        cx.check_class(scope, fqn, class, &mut out);
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
    /// phpstan's `checkNullables` (level 8+). When `false`, `null` is stripped from
    /// the returned value's type before checking — a nullable value satisfies a
    /// non-null declared return below level 8.
    check_nullables: bool,
    /// phpstan's `checkUnionTypes` / `reportMaybes` (level 7+).
    report_maybes: bool,
    /// `--fix`: the analyzed source, enabling the wrong-doc-narrowing repair.
    fix_source: Option<&'a str>,
}

impl Cx<'_> {
    fn check_function(&self, scope: &Scope, f: &FunctionDecl, out: &mut Vec<Diagnostic>) {
        let refl = reflect_function(scope, self.interner, f);
        if !skip_return(&refl.return_type) {
            let ret = Ret {
                fix: self.fix_source.and_then(|source| {
                    crate::fix::return_narrowing_fix(
                        self.index,
                        self.types,
                        source,
                        scope,
                        &refl.return_type,
                        &refl.native_return,
                        f.doc.as_deref(),
                        crate::fix::first_attr_span(&f.attrs).unwrap_or(f.name_span),
                        &f.body,
                    )
                }),
                declared: refl.return_type.clone(),
                native_declared: refl.native_return.clone(),
                label: format!("function {}()", refl.fqn),
            };
            self.check_returns_in(&f.body, &ret, out);
        }
    }

    fn check_class(&self, scope: &Scope, fqn: &str, c: &ClassDecl, out: &mut Vec<Diagnostic>) {
        let refl = reflect_class(scope, self.interner, fqn, c);
        for m in &c.members {
            let Member::Method(md) = m else { continue };
            let Some(body) = &md.body else { continue };
            let mname = self.interner.resolve(md.name);
            let Some(mr) = refl
                .methods
                .iter()
                .find(|x| !x.magic && x.name.eq_ignore_ascii_case(mname))
            else {
                continue;
            };
            if !skip_return(&mr.return_type) {
                let ret = Ret {
                    fix: self.fix_source.and_then(|source| {
                        crate::fix::return_narrowing_fix(
                            self.index,
                            self.types,
                            source,
                            scope,
                            &mr.return_type,
                            &mr.native_return,
                            md.doc.as_deref(),
                            crate::fix::first_attr_span(&md.attrs).unwrap_or(md.name_span),
                            body,
                        )
                    }),
                    declared: mr.return_type.clone(),
                    native_declared: mr.native_return.clone(),
                    label: format!("{}::{}()", fqn, mr.name),
                };
                self.check_returns_in(body, &ret, out);
            }
        }
    }

    /// Find every `return <expr>;` in `stmts` — descending control flow but NOT into
    /// nested function/class declarations or closures, which carry their own return
    /// types — and check each against `ret` using the flow-narrowed type map.
    fn check_returns_in(&self, stmts: &[Stmt], ret: &Ret, out: &mut Vec<Diagnostic>) {
        function_like::collect_returns(stmts, |expr| {
            if let Some(e) = expr {
                self.check_return_expr(e, ret, out);
            }
        });
    }

    fn check_return_expr(&self, e: &Expr, ret: &Ret, out: &mut Vec<Diagnostic>) {
        // Unmapped (rare) → `mixed` → lenient.
        let actual = self
            .types
            .get(&key(e))
            .map(|f| f.merged.clone())
            .unwrap_or(Type::Mixed);
        // checkNullables gate (level < 8): strip `null` from the returned value.
        if !function_like::type_mismatch_reportable(
            self.index,
            &actual,
            &ret.declared,
            self.check_nullables,
            self.report_maybes,
        ) {
            return;
        }
        // treatPhpDocTypesAsCertain=false: suppress if the *native* types agree.
        if !self.treat_phpdoc_certain {
            let native = self
                .types
                .get(&key(e))
                .map(|f| f.native().clone())
                .unwrap_or(Type::Mixed);
            if !function_like::type_mismatch_reportable(
                self.index,
                &native,
                &ret.native_declared,
                self.check_nullables,
                self.report_maybes,
            ) {
                return;
            }
        }
        function_like::push_return_type_error(out, e, &ret.label, &ret.declared, &actual);
        if let (Some(fix), Some(d)) = (&ret.fix, out.last_mut()) {
            d.fix = Some(php_diagnostics::Fix::Replace(fix.clone()));
        }
    }
}

/// Declared return types not worth checking: `mixed` (everything fits), `void`
/// and `never` (no value is returned to check against).
fn skip_return(t: &Type) -> bool {
    matches!(
        t,
        Type::Mixed | Type::ExplicitMixed | Type::Void | Type::Never
    )
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
        let types = php_infer::type_map(&index, &r.program, &r.interner, true);
        return_type_errors(
            &index,
            &r.program,
            &r.interner,
            &types,
            true,
            true,
            true,
            None,
        )
        .into_iter()
        .map(|d| d.message)
        .collect()
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
        assert_eq!(
            d,
            ["function make() should return Animal but returns Widget"]
        );
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
