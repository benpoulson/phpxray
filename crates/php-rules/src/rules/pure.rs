//! phpstan category **Pure** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Pure/` — 2 rule(s) at level(s) 2.
//! The rule set's coverage truth is `cargo run -p xtask -- rule-manifest`; for phpstan's behaviour read `phpstan-src/src/Rules/` directly. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).

use crate::{decls, FileAnalysis, RuleEntry};
use php_ast::{FunctionDecl, MethodDecl};
use php_diagnostics::Diagnostic;
use php_intern::Interner;
use php_reflect::FunctionReflection;
use php_resolve::Scope;
use php_span::Span;
use php_types::Type;

// ---------------------------------------------------------------------------
// PureFunctionRule / PureMethodRule — reflection-level purity checks
// ---------------------------------------------------------------------------

/// `PureFunctionRule`: deterministic reflection checks from phpstan's
/// `FunctionPurityCheck` for declarations explicitly marked `@pure`.
///
/// We intentionally do not guess body impure-points yet (`impure.functionCall`,
/// etc.). This rule only reports the phpstan cases that are already explicit in
/// the signature/docblock: by-reference parameters and pure-void declarations.
fn run_pure_function(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_function(fa, |scope, f| {
        let refl = fa.reflect_function(scope, f);
        if !is_marked_pure(f.doc.as_deref()) {
            return;
        }
        check_pure_params(
            &mut out,
            &format!("Function {}()", display_function(&refl)),
            "pureFunction.parameterByRef",
            &refl.params,
            function_span(f),
        );
        if is_void_without_throw_or_assert(&refl.return_type, f.doc.as_deref()) {
            out.push(
                Diagnostic::error(
                    function_span(f),
                    format!(
                        "Function {}() is marked as pure but returns void.",
                        display_function(&refl)
                    ),
                )
                .with_code("pureFunction.void"),
            );
        }
    });
    out
}

/// `PureMethodRule`: same deterministic subset as [`run_pure_function`], but
/// for class methods. Constructors are exempt from the pure-void branch, just as
/// in phpstan's `FunctionPurityCheck`.
fn run_pure_method(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    decls::for_each_method(fa, |scope, fqn, c, m| {
        let class = fa.reflect_class(scope, fqn, c);
        let Some(refl) = class
            .methods
            .iter()
            .find(|r| !r.magic && r.name.eq_ignore_ascii_case(fa.interner.resolve(m.name)))
        else {
            return;
        };
        if !is_marked_pure(m.doc.as_deref()) {
            return;
        }
        let desc = format!("Method {}::{}()", display_class(fqn), refl.name);
        check_pure_params(
            &mut out,
            &desc,
            "pureMethod.parameterByRef",
            &refl.params,
            m.name_span,
        );
        if !is_constructor(fa.interner, m)
            && is_void_without_throw_or_assert(&refl.return_type, m.doc.as_deref())
        {
            out.push(
                Diagnostic::error(
                    m.name_span,
                    format!("{desc} is marked as pure but returns void."),
                )
                .with_code("pureMethod.void"),
            );
        }
    });
    out
}

fn check_pure_params(
    out: &mut Vec<Diagnostic>,
    desc: &str,
    code: &'static str,
    params: &[php_reflect::ParamReflection],
    span: Span,
) {
    for p in params {
        if p.by_ref {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "{desc} is marked as pure but parameter ${} is passed by reference.",
                        p.name
                    ),
                )
                .with_code(code),
            );
        }
    }
}

fn is_void_without_throw_or_assert(return_type: &Type, doc: Option<&str>) -> bool {
    matches!(return_type, Type::Void) && !doc_has_throw_or_assert(doc)
}

fn is_marked_pure(doc: Option<&str>) -> bool {
    doc_has_base_tag(doc, &["pure"]) && !doc_has_base_tag(doc, &["impure"])
}

fn doc_has_throw_or_assert(doc: Option<&str>) -> bool {
    doc_has_base_tag(
        doc,
        &["throws", "assert", "assert-if-true", "assert-if-false"],
    )
}

fn doc_has_base_tag(doc: Option<&str>, names: &[&str]) -> bool {
    php_phpdoc::query::has_base_tag(doc, names)
}

fn display_function(f: &FunctionReflection) -> &str {
    f.fqn.trim_start_matches('\\')
}

fn display_class(fqn: &str) -> &str {
    fqn.trim_start_matches('\\')
}

fn is_constructor(interner: &Interner, m: &MethodDecl) -> bool {
    interner.resolve(m.name).eq_ignore_ascii_case("__construct")
}

fn for_each_function(fa: &FileAnalysis, mut f: impl FnMut(&Scope, &FunctionDecl)) {
    decls::for_each_named_function(fa, &mut f);
}

fn function_span(f: &FunctionDecl) -> Span {
    f.name_span
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "pure.function",
        level: 2,
        run: run_pure_function,
    },
    RuleEntry {
        name: "pure.method",
        level: 2,
        run: run_pure_method,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    #[test]
    fn pure_function_by_ref_parameter_is_flagged() {
        let src = "<?php /** @pure */ function f(int &$x): int { return $x; }";
        assert_eq!(
            codes(src, run_pure_function),
            ["pureFunction.parameterByRef"]
        );
    }

    #[test]
    fn pure_function_returning_void_is_flagged() {
        let src = "<?php /** @pure */ function f(): void {}";
        assert_eq!(codes(src, run_pure_function), ["pureFunction.void"]);
    }

    #[test]
    fn pure_function_void_with_throws_doc_is_clean() {
        let src = "<?php /** @pure @throws RuntimeException */ function f(): void {}";
        assert!(codes(src, run_pure_function).is_empty());
    }

    #[test]
    fn impure_tag_suppresses_pure_function_checks() {
        let src = "<?php /** @pure @phpstan-impure */ function f(int &$x): void {}";
        assert!(codes(src, run_pure_function).is_empty());
    }

    #[test]
    fn pure_method_by_ref_parameter_is_flagged() {
        let src = "<?php class C { /** @pure */ function m(string &$s): string { return $s; } }";
        assert_eq!(codes(src, run_pure_method), ["pureMethod.parameterByRef"]);
    }

    #[test]
    fn pure_method_returning_void_is_flagged() {
        let src = "<?php class C { /** @pure */ function m(): void {} }";
        assert_eq!(codes(src, run_pure_method), ["pureMethod.void"]);
    }

    #[test]
    fn pure_constructor_void_doc_is_clean() {
        let src = "<?php class C { /** @pure @return void */ function __construct() {} }";
        assert!(codes(src, run_pure_method).is_empty());
    }

    #[test]
    fn non_pure_void_method_is_clean() {
        let src = "<?php class C { function m(): void {} }";
        assert!(codes(src, run_pure_method).is_empty());
    }
}
