//! phpstan category **EnumCases** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/EnumCases/` — 2 rule(s) at level(s) 0.
//! The rule set's coverage truth is `cargo run -p xtask -- rule-manifest`; for phpstan's behaviour read `phpstan-src/src/Rules/` directly. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented:
//! - `enum.caseOutsideOfEnum` (`EnumCaseOutsideEnumRule`, level 0) — an
//!   `case Foo;` enum-case declaration appearing inside a class/interface (i.e.
//!   any class-like that is NOT an enum). Purely structural.
//!
//! Deferred:
//! - `EnumCaseAttributesRule` (`attribute.*`) — checks that attributes placed on
//!   an enum case target `Attribute::TARGET_CLASS_CONSTANT`. This needs the
//!   attribute-target reflection of the *referenced* attribute class together
//!   with the bit-flag arithmetic of phpstan's generic `AttributesCheck`; it is
//!   a thin wrapper around that shared check rather than an EnumCases-specific
//!   rule, so it belongs with the attribute rules — deferred here.

#![allow(unused_imports)]
use crate::{FileAnalysis, RuleEntry};
use php_ast::{ClassDecl, ClassKind, Member, Stmt, StmtKind};
use php_diagnostics::Diagnostic;
use php_span::Span;

/// `EnumCaseOutsideEnumRule` (level 0): an enum-case declaration (`case Foo;`)
/// is only valid inside an `enum`. phpstan treats a `case` inside a *trait* as
/// allowed (a trait has no class kind of its own — it is checked where it is
/// used); everywhere else (class, interface) it is an error.
fn run_enum_case_outside_enum(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for stmt in &fa.program.stmts {
        visit_stmt(stmt, &mut out);
    }
    out
}

/// Descend the statement tree looking for class-like declarations. We cannot use
/// `crate::walk` here because it does not surface `Member`s (enum cases are not
/// statements) and we need each member's *enclosing* class kind.
fn visit_stmt(stmt: &Stmt, out: &mut Vec<Diagnostic>) {
    match &stmt.kind {
        StmtKind::Class(class) => visit_class(class, stmt.span, out),

        // Containers that can hold further declarations.
        StmtKind::Block(stmts) => stmts.iter().for_each(|s| visit_stmt(s, out)),
        StmtKind::Namespace {
            body: Some(body), ..
        } => body.iter().for_each(|s| visit_stmt(s, out)),
        StmtKind::Declare {
            body: Some(body), ..
        } => visit_stmt(body, out),

        // Conditional / nested declarations (PHP allows declaring a class inside
        // an `if`, a loop, a try, etc.).
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            visit_stmt(then, out);
            for ei in elseifs {
                visit_stmt(&ei.body, out);
            }
            if let Some(e) = els {
                visit_stmt(e, out);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => visit_stmt(body, out),
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                c.body.iter().for_each(|s| visit_stmt(s, out));
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter().for_each(|s| visit_stmt(s, out));
            for c in catches {
                c.body.iter().for_each(|s| visit_stmt(s, out));
            }
            if let Some(f) = finally {
                f.iter().for_each(|s| visit_stmt(s, out));
            }
        }

        // A function body can also declare a class.
        StmtKind::Function(fd) => fd.body.iter().for_each(|s| visit_stmt(s, out)),
        _ => {}
    }
}

/// Inspect a class-like declaration: flag enum cases unless it is an `enum`.
/// (Also descends into method bodies, which may declare further classes.)
/// `class_span` is the span of the wrapping statement — our AST gives enum-case
/// declarations no span of their own, so we report at the case value's span when
/// present (`case A = 1;`) and otherwise at the declaring class.
fn visit_class(class: &ClassDecl, class_span: Span, out: &mut Vec<Diagnostic>) {
    let is_enum = class.kind == ClassKind::Enum;
    // A trait's members are checked at the using site, not here (phpstan skips
    // enum cases inside traits via `!$scope->isInTrait()`).
    let is_trait = class.kind == ClassKind::Trait;

    for member in &class.members {
        match member {
            Member::EnumCase(case) if !is_enum && !is_trait => {
                let span = case.value.as_ref().map(|v| v.span).unwrap_or(class_span);
                out.push(
                    Diagnostic::error(span, "Enum case can only be used in enums.")
                        .with_code("enum.caseOutsideOfEnum"),
                );
            }
            // Method bodies can contain nested class declarations.
            Member::Method(m) => {
                if let Some(body) = &m.body {
                    body.iter().for_each(|s| visit_stmt(s, out));
                }
            }
            _ => {}
        }
    }
}

pub(crate) static RULES: &[RuleEntry] = &[RuleEntry {
    name: "enum.caseOutsideOfEnum",
    level: 0,
    run: run_enum_case_outside_enum,
}];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    #[test]
    fn case_in_plain_class_is_flagged() {
        let src = "<?php class C { case Foo; }";
        assert_eq!(
            codes(src, run_enum_case_outside_enum),
            ["enum.caseOutsideOfEnum"]
        );
    }

    #[test]
    fn case_in_interface_is_flagged() {
        let src = "<?php interface I { case Foo; }";
        assert_eq!(
            codes(src, run_enum_case_outside_enum),
            ["enum.caseOutsideOfEnum"]
        );
    }

    #[test]
    fn multiple_cases_each_flagged() {
        let src = "<?php class C { case A; case B; }";
        assert_eq!(
            codes(src, run_enum_case_outside_enum),
            ["enum.caseOutsideOfEnum", "enum.caseOutsideOfEnum"]
        );
    }

    #[test]
    fn case_in_enum_is_ok() {
        let src = "<?php enum E { case A; case B; }";
        assert!(codes(src, run_enum_case_outside_enum).is_empty());
    }

    #[test]
    fn backed_enum_case_is_ok() {
        let src = "<?php enum E: int { case A = 1; case B = 2; }";
        assert!(codes(src, run_enum_case_outside_enum).is_empty());
    }

    #[test]
    fn case_in_trait_is_not_flagged() {
        // phpstan skips enum cases inside traits (`!$scope->isInTrait()`).
        let src = "<?php trait T { case Foo; }";
        assert!(codes(src, run_enum_case_outside_enum).is_empty());
    }

    #[test]
    fn ordinary_members_are_not_flagged() {
        let src = "<?php class C { const X = 1; public int $p = 0; public function m() {} }";
        assert!(codes(src, run_enum_case_outside_enum).is_empty());
    }

    #[test]
    fn case_in_namespaced_class_is_flagged() {
        let src = "<?php namespace App; class C { case Foo; }";
        assert_eq!(
            codes(src, run_enum_case_outside_enum),
            ["enum.caseOutsideOfEnum"]
        );
    }

    #[test]
    fn case_in_class_inside_function_is_flagged() {
        let src = "<?php function f() { class C { case Foo; } }";
        assert_eq!(
            codes(src, run_enum_case_outside_enum),
            ["enum.caseOutsideOfEnum"]
        );
    }
}
