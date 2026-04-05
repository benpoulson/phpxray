//! phpstan category **Types** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Types/` — 1 rule(s) at level(s) 0.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented (level 0, purely syntactic — no inference):
//! - `unionType.<type>` / `nullableType.<type>` (`InvalidTypesInUnionRule`) — a
//!   native union/nullable typehint that contains one of the "standalone-only"
//!   types (`mixed`, `never`, `void`), which may not appear as a *member* of a
//!   union or nullable type declaration. Every native type annotation is
//!   visited: function/method params + returns, typed properties, closures,
//!   arrow functions, and property-hook params (incl. promoted ctor params).

#![allow(unused_imports)]
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{
    ArrowFn, ClassDecl, ClosureExpr, ExprKind, FunctionDecl, Member, MethodDecl, Param,
    PropertyHook, StmtKind, Type, TypeKind,
};
use php_diagnostics::Diagnostic;

/// The reserved keywords that may only appear *standalone*, never as a member of
/// a union or nullable type. Mirrors phpstan's `ONLY_STANDALONE_TYPES`.
const ONLY_STANDALONE_TYPES: &[&str] = &["mixed", "never", "void"];

/// If `t` is a bare type name (phpstan's `Identifier`) that is one of the
/// standalone-only keywords, return `(original_spelling, lowercased)`; else
/// `None`. phpstan reports the original spelling in the message and the
/// lowercased form in the identifier.
fn standalone_name(t: &Type) -> Option<(String, String)> {
    if let TypeKind::Simple(name) = &t.kind {
        let lower = name.text.to_ascii_lowercase();
        if ONLY_STANDALONE_TYPES.contains(&lower.as_str()) {
            return Some((name.text.clone(), lower));
        }
    }
    None
}

/// Inspect a single (outermost) type annotation. phpstan only looks at the
/// outermost `ComplexType` — a `UnionType` or a `NullableType` — and reports at
/// most one error per annotation (it returns on the first offending member).
fn check_type(t: &Type, out: &mut Vec<Diagnostic>) {
    match &t.kind {
        TypeKind::Union(members) => {
            for m in members {
                if let Some((orig, lower)) = standalone_name(m) {
                    out.push(
                        Diagnostic::error(
                            t.span,
                            format!("Type {orig} cannot be part of a union type declaration."),
                        )
                        .with_code(union_code(&lower)),
                    );
                    return;
                }
            }
        }
        TypeKind::Nullable(inner) => {
            if let Some((orig, lower)) = standalone_name(inner) {
                out.push(
                    Diagnostic::error(
                        t.span,
                        format!("Type {orig} cannot be part of a nullable type declaration."),
                    )
                    .with_code(nullable_code(&lower)),
                );
            }
        }
        // A bare `Simple` type or an `Intersection` is not flagged by this rule
        // (phpstan only inspects UnionType / NullableType).
        _ => {}
    }
}

/// `unionType.mixed` / `unionType.never` / `unionType.void`.
fn union_code(lower: &str) -> &'static str {
    match lower {
        "mixed" => "unionType.mixed",
        "never" => "unionType.never",
        "void" => "unionType.void",
        _ => "unionType",
    }
}

/// `nullableType.mixed` / `nullableType.never` / `nullableType.void`.
fn nullable_code(lower: &str) -> &'static str {
    match lower {
        "mixed" => "nullableType.mixed",
        "never" => "nullableType.never",
        "void" => "nullableType.void",
        _ => "nullableType",
    }
}

fn check_params(params: &[Param], out: &mut Vec<Diagnostic>) {
    for p in params {
        if let Some(ty) = &p.ty {
            check_type(ty, out);
        }
        // Hooks on a promoted property param carry their own param lists.
        for h in &p.hooks {
            check_hook(h, out);
        }
    }
}

fn check_hook(h: &PropertyHook, out: &mut Vec<Diagnostic>) {
    if let Some(params) = &h.params {
        check_params(params, out);
    }
}

fn check_function(f: &FunctionDecl, out: &mut Vec<Diagnostic>) {
    check_params(&f.params, out);
    if let Some(rt) = &f.return_type {
        check_type(rt, out);
    }
}

fn check_method(m: &MethodDecl, out: &mut Vec<Diagnostic>) {
    check_params(&m.params, out);
    if let Some(rt) = &m.return_type {
        check_type(rt, out);
    }
}

fn check_closure(c: &ClosureExpr, out: &mut Vec<Diagnostic>) {
    check_params(&c.params, out);
    if let Some(rt) = &c.return_type {
        check_type(rt, out);
    }
}

fn check_arrow(a: &ArrowFn, out: &mut Vec<Diagnostic>) {
    check_params(&a.params, out);
    if let Some(rt) = &a.return_type {
        check_type(rt, out);
    }
}

fn check_class(c: &ClassDecl, out: &mut Vec<Diagnostic>) {
    for m in &c.members {
        match m {
            Member::Method(md) => check_method(md, out),
            Member::Property(pd) => {
                if let Some(ty) = &pd.ty {
                    check_type(ty, out);
                }
                for el in &pd.props {
                    if let Some(hooks) = &el.hooks {
                        for h in hooks {
                            check_hook(h, out);
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// `InvalidTypesInUnionRule` — `mixed`/`never`/`void` used inside a union or
/// nullable native type declaration.
fn run_invalid_types_in_union(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();

    // Named function and class declarations (incl. nested ones — `for_each_stmt`
    // visits every statement in the file).
    walk::for_each_stmt(fa.program, &mut |s| match &s.kind {
        StmtKind::Function(f) => check_function(f, &mut out),
        StmtKind::Class(c) => check_class(c, &mut out),
        _ => {}
    });

    // Closures, arrow functions, and anonymous classes live in expression
    // position.
    walk::for_each_expr(fa.program, &mut |e| match &e.kind {
        ExprKind::Closure(c) => check_closure(c, &mut out),
        ExprKind::ArrowFn(a) => check_arrow(a, &mut out),
        ExprKind::NewAnon { class, .. } => check_class(class, &mut out),
        _ => {}
    });

    out
}

pub(crate) static RULES: &[RuleEntry] = &[RuleEntry {
    name: "types.invalidTypesInUnion",
    level: 0,
    run: run_invalid_types_in_union,
}];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- union types ---------------------------------------------------------

    #[test]
    fn void_in_union_return_is_flagged() {
        assert_eq!(
            codes("<?php function f(): int|void {}", run_invalid_types_in_union),
            ["unionType.void"]
        );
    }

    #[test]
    fn never_in_union_param_is_flagged() {
        assert_eq!(
            codes("<?php function f(int|never $x) {}", run_invalid_types_in_union),
            ["unionType.never"]
        );
    }

    #[test]
    fn mixed_in_union_is_flagged() {
        assert_eq!(
            codes("<?php function f(): int|mixed {}", run_invalid_types_in_union),
            ["unionType.mixed"]
        );
    }

    // --- nullable types ------------------------------------------------------

    #[test]
    fn nullable_void_is_flagged() {
        assert_eq!(
            codes("<?php function f(): ?void {}", run_invalid_types_in_union),
            ["nullableType.void"]
        );
    }

    #[test]
    fn nullable_never_is_flagged() {
        assert_eq!(
            codes("<?php function f(?never $x) {}", run_invalid_types_in_union),
            ["nullableType.never"]
        );
    }

    // --- negatives -----------------------------------------------------------

    #[test]
    fn standalone_void_return_is_ok() {
        assert!(codes("<?php function f(): void {}", run_invalid_types_in_union).is_empty());
    }

    #[test]
    fn standalone_never_return_is_ok() {
        assert!(codes(
            "<?php function f(): never { throw new E(); }",
            run_invalid_types_in_union
        )
        .is_empty());
    }

    #[test]
    fn ordinary_union_is_ok() {
        assert!(codes("<?php function f(): int|string|null {}", run_invalid_types_in_union).is_empty());
    }

    #[test]
    fn ordinary_nullable_is_ok() {
        assert!(codes("<?php function f(): ?int {}", run_invalid_types_in_union).is_empty());
    }

    #[test]
    fn case_insensitive() {
        assert_eq!(
            codes("<?php function f(): int|VOID {}", run_invalid_types_in_union),
            ["unionType.void"]
        );
    }

    // --- coverage of every declaration site ----------------------------------

    #[test]
    fn method_return_in_union_is_flagged() {
        assert_eq!(
            codes("<?php class C { function m(): int|void {} }", run_invalid_types_in_union),
            ["unionType.void"]
        );
    }

    #[test]
    fn typed_property_in_union_is_flagged() {
        assert_eq!(
            codes("<?php class C { public int|void $p; }", run_invalid_types_in_union),
            ["unionType.void"]
        );
    }

    #[test]
    fn closure_param_in_union_is_flagged() {
        assert_eq!(
            codes("<?php $f = function (int|never $x) {};", run_invalid_types_in_union),
            ["unionType.never"]
        );
    }

    #[test]
    fn arrow_fn_return_in_union_is_flagged() {
        assert_eq!(
            codes("<?php $f = fn (): int|void => 1;", run_invalid_types_in_union),
            ["unionType.void"]
        );
    }

    #[test]
    fn anon_class_method_in_union_is_flagged() {
        assert_eq!(
            codes(
                "<?php $o = new class { function m(): int|void {} };",
                run_invalid_types_in_union
            ),
            ["unionType.void"]
        );
    }

    #[test]
    fn nested_function_is_flagged() {
        assert_eq!(
            codes(
                "<?php function outer() { function inner(): int|void {} }",
                run_invalid_types_in_union
            ),
            ["unionType.void"]
        );
    }

    #[test]
    fn promoted_ctor_param_in_union_is_flagged() {
        assert_eq!(
            codes(
                "<?php class C { public function __construct(public int|void $x) {} }",
                run_invalid_types_in_union
            ),
            ["unionType.void"]
        );
    }

    #[test]
    fn no_types_no_diagnostics() {
        assert!(codes("<?php function f($a) { return $a; }", run_invalid_types_in_union).is_empty());
    }
}
