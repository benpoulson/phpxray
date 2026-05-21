//! phpstan category **Pure** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Pure/` — 2 rule(s) at level(s) 2.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).

use crate::{FileAnalysis, RuleEntry};
use php_ast::{ClassDecl, FunctionDecl, Member, MethodDecl, Stmt, StmtKind};
use php_diagnostics::Diagnostic;
use php_intern::Interner;
use php_phpdoc::parse_block;
use php_reflect::{reflect_class, reflect_function, FunctionReflection};
use php_resolve::{for_each_region, Scope};
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
        let refl = reflect_function(scope, fa.interner, f);
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
    for_each_class(fa, |scope, fqn, c| {
        let class = reflect_class(scope, fa.interner, fqn, c);
        for m in methods(c) {
            let Some(refl) = class
                .methods
                .iter()
                .find(|r| !r.magic && r.name.eq_ignore_ascii_case(fa.interner.resolve(m.name)))
            else {
                continue;
            };
            if !is_marked_pure(m.doc.as_deref()) {
                continue;
            }
            let desc = format!("Method {}::{}()", display_class(fqn), refl.name);
            check_pure_params(
                &mut out,
                &desc,
                "pureMethod.parameterByRef",
                &refl.params,
                method_span(m),
            );
            if !is_constructor(fa.interner, m)
                && is_void_without_throw_or_assert(&refl.return_type, m.doc.as_deref())
            {
                out.push(
                    Diagnostic::error(
                        method_span(m),
                        format!("{desc} is marked as pure but returns void."),
                    )
                    .with_code("pureMethod.void"),
                );
            }
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
    let Some(doc) = doc else { return false };
    parse_block(doc).tags.iter().any(|tag| {
        tag_matches(&tag.name, names)
            || value_tag_names(&tag.value).any(|inner| tag_matches(inner, names))
    })
}

fn tag_matches(tag: &str, names: &[&str]) -> bool {
    let base = tag
        .strip_prefix("phpstan-")
        .or_else(|| tag.strip_prefix("psalm-"))
        .unwrap_or(tag);
    names.contains(&base)
}

fn value_tag_names(value: &str) -> impl Iterator<Item = &str> {
    value.match_indices('@').filter_map(|(idx, _)| {
        let rest = &value[idx + 1..];
        let end = rest
            .char_indices()
            .find(|(_, ch)| !(ch.is_ascii_alphanumeric() || *ch == '-'))
            .map(|(i, _)| i)
            .unwrap_or(rest.len());
        (end > 0).then_some(&rest[..end])
    })
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

fn methods(c: &ClassDecl) -> impl Iterator<Item = &MethodDecl> {
    c.members.iter().filter_map(|m| match m {
        Member::Method(md) => Some(md),
        _ => None,
    })
}

fn for_each_function(fa: &FileAnalysis, mut f: impl FnMut(&Scope, &FunctionDecl)) {
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            walk_function_stmt(st, scope, &mut f);
        }
    });
}

fn walk_function_stmt(st: &Stmt, scope: &Scope, f: &mut impl FnMut(&Scope, &FunctionDecl)) {
    match &st.kind {
        StmtKind::Function(fd) => {
            f(scope, fd);
            fd.body.iter().for_each(|s| walk_function_stmt(s, scope, f));
        }
        StmtKind::Class(c) => {
            for m in methods(c) {
                if let Some(body) = &m.body {
                    body.iter().for_each(|s| walk_function_stmt(s, scope, f));
                }
            }
        }
        StmtKind::Block(b) => b.iter().for_each(|s| walk_function_stmt(s, scope, f)),
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            walk_function_stmt(then, scope, f);
            for e in elseifs {
                walk_function_stmt(&e.body, scope, f);
            }
            if let Some(e) = els {
                walk_function_stmt(e, scope, f);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => walk_function_stmt(body, scope, f),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter().for_each(|s| walk_function_stmt(s, scope, f));
            for c in catches {
                c.body.iter().for_each(|s| walk_function_stmt(s, scope, f));
            }
            if let Some(fin) = finally {
                fin.iter().for_each(|s| walk_function_stmt(s, scope, f));
            }
        }
        StmtKind::Switch { cases, .. } => {
            for case in cases {
                case.body
                    .iter()
                    .for_each(|s| walk_function_stmt(s, scope, f));
            }
        }
        StmtKind::Declare { body: Some(b), .. } => walk_function_stmt(b, scope, f),
        StmtKind::Namespace { body: Some(b), .. } => {
            b.iter().for_each(|s| walk_function_stmt(s, scope, f));
        }
        _ => {}
    }
}

fn for_each_class(fa: &FileAnalysis, mut f: impl FnMut(&Scope, &str, &ClassDecl)) {
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            walk_class_stmt(st, scope, fa.interner, &mut f);
        }
    });
}

fn walk_class_stmt(
    st: &Stmt,
    scope: &Scope,
    interner: &Interner,
    f: &mut impl FnMut(&Scope, &str, &ClassDecl),
) {
    match &st.kind {
        StmtKind::Class(c) => {
            if let Some(name) = c.name {
                let fqn = scope.qualify(interner.resolve(name));
                f(scope, &fqn, c);
            }
        }
        StmtKind::Block(b) => b
            .iter()
            .for_each(|s| walk_class_stmt(s, scope, interner, f)),
        StmtKind::Function(fd) => fd
            .body
            .iter()
            .for_each(|s| walk_class_stmt(s, scope, interner, f)),
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            walk_class_stmt(then, scope, interner, f);
            for e in elseifs {
                walk_class_stmt(&e.body, scope, interner, f);
            }
            if let Some(e) = els {
                walk_class_stmt(e, scope, interner, f);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => walk_class_stmt(body, scope, interner, f),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter()
                .for_each(|s| walk_class_stmt(s, scope, interner, f));
            for c in catches {
                c.body
                    .iter()
                    .for_each(|s| walk_class_stmt(s, scope, interner, f));
            }
            if let Some(fin) = finally {
                fin.iter()
                    .for_each(|s| walk_class_stmt(s, scope, interner, f));
            }
        }
        StmtKind::Switch { cases, .. } => {
            for case in cases {
                case.body
                    .iter()
                    .for_each(|s| walk_class_stmt(s, scope, interner, f));
            }
        }
        StmtKind::Declare { body: Some(b), .. } => walk_class_stmt(b, scope, interner, f),
        StmtKind::Namespace { body: Some(b), .. } => {
            b.iter()
                .for_each(|s| walk_class_stmt(s, scope, interner, f));
        }
        _ => {}
    }
}

fn function_span(f: &FunctionDecl) -> Span {
    for p in &f.params {
        if let Some(t) = &p.ty {
            return t.span;
        }
        if let Some(d) = &p.default {
            return d.span;
        }
    }
    if let Some(t) = &f.return_type {
        return t.span;
    }
    if let Some(first) = f.body.first() {
        return first.span;
    }
    f.attrs
        .first()
        .and_then(|g| g.attrs.first())
        .map(|a| a.name.span)
        .unwrap_or_else(|| Span::new(0, 0))
}

fn method_span(m: &MethodDecl) -> Span {
    for p in &m.params {
        if let Some(t) = &p.ty {
            return t.span;
        }
        if let Some(d) = &p.default {
            return d.span;
        }
    }
    if let Some(t) = &m.return_type {
        return t.span;
    }
    if let Some(body) = &m.body {
        if let Some(first) = body.first() {
            return first.span;
        }
    }
    m.attrs
        .first()
        .and_then(|g| g.attrs.first())
        .map(|a| a.name.span)
        .unwrap_or_else(|| Span::new(0, 0))
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
