//! phpstan category **Cast** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Cast/` — 7 rule(s) at level(s) 0,2.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to `RULES`
//! (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented (level 0, purely syntactic):
//! - `cast.unset` — the `(unset)` cast (removed in PHP 8.0).
//! - `cast.void` — a `(void)` cast used inside an expression (only valid as a
//!   statement-level discard).
//!
//! Deferred: `DeprecatedCastRule` (`cast.deprecated`) flags the non-standard
//! spellings `(integer)`/`(boolean)`/`(double)`/`(binary)`, but our lexer
//! normalizes those to the canonical `CastKind`, so the spelling isn't in the
//! AST. The level-2 Cast rules (`InvalidCastRule`, `EchoRule`, `PrintRule`, …)
//! need type inference and belong with the type rules.

use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{CastKind, ExprKind, StmtKind};
use php_diagnostics::Diagnostic;
use std::collections::HashSet;

/// `(unset)` cast — no longer supported since PHP 8.0.
fn run_unset_cast(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        if let ExprKind::Cast { kind: CastKind::Unset, .. } = &e.kind {
            out.push(
                Diagnostic::error(e.span, "The (unset) cast is no longer supported in PHP 8.0 and later.")
                    .with_code("cast.unset"),
            );
        }
    });
    out
}

/// `(void)` cast used within an expression. A `(void)` cast is only valid as a
/// statement-level discard (`(void) foo();`); anywhere else it's an error.
fn run_void_cast(fa: &FileAnalysis) -> Vec<Diagnostic> {
    // Collect void casts that ARE a statement expression (the allowed position).
    let mut allowed: HashSet<(u32, u32)> = HashSet::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::Expr(e) = &s.kind {
            if let ExprKind::Cast { kind: CastKind::Void, .. } = &e.kind {
                let r = e.span.range();
                allowed.insert((r.start as u32, r.end as u32));
            }
        }
    });

    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        if let ExprKind::Cast { kind: CastKind::Void, .. } = &e.kind {
            let r = e.span.range();
            if !allowed.contains(&(r.start as u32, r.end as u32)) {
                out.push(
                    Diagnostic::error(e.span, "The (void) cast cannot be used within an expression.")
                        .with_code("cast.void"),
                );
            }
        }
    });
    out
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "cast.unset", level: 0, run: run_unset_cast },
    RuleEntry { name: "cast.void", level: 0, run: run_void_cast },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    #[test]
    fn unset_cast_is_flagged() {
        assert_eq!(codes("<?php $x = (unset) $y;", run_unset_cast), ["cast.unset"]);
    }

    #[test]
    fn unset_cast_found_anywhere_in_the_tree() {
        // Nested inside a function body + an argument — the walker reaches it.
        let src = "<?php function f($a) { g((unset) $a); }";
        assert_eq!(codes(src, run_unset_cast), ["cast.unset"]);
    }

    #[test]
    fn other_casts_are_not_unset() {
        assert!(codes("<?php $x = (int) $y; $z = (string) $y;", run_unset_cast).is_empty());
    }

    #[test]
    fn void_cast_as_statement_is_allowed() {
        // A bare `(void) expr;` statement is the one valid position.
        assert!(codes("<?php (void) foo();", run_void_cast).is_empty());
    }

    #[test]
    fn void_cast_within_expression_is_flagged() {
        assert_eq!(codes("<?php $x = (void) foo();", run_void_cast), ["cast.void"]);
        assert_eq!(codes("<?php bar((void) foo());", run_void_cast), ["cast.void"]);
        assert_eq!(codes("<?php echo (void) foo();", run_void_cast), ["cast.void"]);
    }

    #[test]
    fn void_cast_statement_inside_a_function_is_allowed() {
        assert!(codes("<?php function f() { (void) foo(); }", run_void_cast).is_empty());
    }

    #[test]
    fn no_cast_no_diagnostics() {
        assert!(codes("<?php $x = 1 + 2; echo $x;", run_unset_cast).is_empty());
        assert!(codes("<?php $x = 1 + 2; echo $x;", run_void_cast).is_empty());
    }
}
