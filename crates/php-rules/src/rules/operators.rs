//! phpstan category **Operators** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Operators/` — 7 rule(s) at level(s) 0,2.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented (purely syntactic / structural — no type inference):
//! - `assign.invalidExpr` / `nullsafe.assign` / `nullsafe.byRef`
//!   (`InvalidAssignVarRule`, level 0) — the left side of an assignment must be
//!   an assignable expression, and the nullsafe operator `?->` may not appear on
//!   the left side of an assignment (nor the right side of a by-ref assignment).
//! - `preInc.expr` / `postInc.expr` / `preDec.expr` / `postDec.expr`
//!   (`InvalidIncDecOperationRule`, level 0, the *non-variable* half) — `++`/`--`
//!   can only be applied to a variable-like expression.
//! - `backtick.deprecated` (`BacktickRule`, level 0) — the backtick shell-exec
//!   operator is deprecated (PHP 8.5+); our target is 8.6-dev so it always fires.
//!
//! Deferred (need the type system — operand TYPES drive these):
//! - DEFERRED: `InvalidBinaryOperationRule` — needs type system (operand types).
//! - DEFERRED: `InvalidComparisonOperationRule` — needs type system.
//! - DEFERRED: `InvalidUnaryOperationRule` — needs type system.
//! - DEFERRED: `InvalidIncDecOperationRule` (the `*.type` half — "Cannot use ++
//!   on <type>") — needs type system. Only the non-variable `*.expr` half is
//!   syntactic and implemented above.
//! - DEFERRED: `PipeOperatorRule` (`pipe.byRef`) — needs the callable type of the
//!   right operand (whether its first parameter is by-reference).

use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{Expr, ExprKind};
use php_diagnostics::Diagnostic;

/// Strip a single layer of `( … )`. phpstan's parser produces no parenthesis
/// nodes, so structural checks should look through ours to stay faithful.
fn unparen(e: &Expr) -> &Expr {
    match &e.kind {
        ExprKind::Paren(inner) => unparen(inner),
        _ => e,
    }
}

/// Mirror of phpstan's `NullsafeCheck::containsNullSafe`: walk only the *chain
/// spine* (the receiver / array-base / class operand), not arbitrary
/// subexpressions, looking for a nullsafe property fetch or method call.
fn contains_nullsafe(e: &Expr) -> bool {
    match &unparen(e).kind {
        ExprKind::Prop { nullsafe: true, .. } => true,
        ExprKind::MethodCall { nullsafe: true, .. } => true,
        ExprKind::Prop { base, .. } => contains_nullsafe(base),
        ExprKind::MethodCall { recv, .. } => contains_nullsafe(recv),
        ExprKind::Index { base, .. } => contains_nullsafe(base),
        ExprKind::StaticProp { class, .. } => contains_nullsafe(class),
        ExprKind::StaticCall { class, .. } => contains_nullsafe(class),
        // List / array destructuring: check each element's key and value.
        ExprKind::Array { items, .. } => items.iter().any(|it| {
            it.key.as_ref().is_some_and(contains_nullsafe)
                || it.value.as_ref().is_some_and(contains_nullsafe)
        }),
        _ => false,
    }
}

/// phpstan's `containsNonAssignableExpression`: returns `true` when `expr` is NOT
/// a valid assignment target. Variables, property/array/static-property fetches
/// are assignable; a `list()`/`[…]` destructuring target is assignable iff each
/// of its element values is.
fn contains_non_assignable(e: &Expr) -> bool {
    match &unparen(e).kind {
        ExprKind::Variable(_)
        | ExprKind::VariableVariable(_)
        | ExprKind::DollarBrace(_)
        | ExprKind::Prop { .. }
        | ExprKind::Index { .. }
        | ExprKind::StaticProp { .. } => false,
        ExprKind::Array { items, .. } => items.iter().any(|it| {
            // Elision (`[, $b]`) has no value and is skipped.
            it.value.as_ref().is_some_and(contains_non_assignable)
        }),
        _ => true,
    }
}

/// `InvalidAssignVarRule` (level 0): the left side of an assignment must be
/// assignable, and the nullsafe operator cannot appear on the left side of an
/// assignment (nor the right side of an assignment by reference).
fn run_invalid_assign_var(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let (target, byref_rhs) = match &e.kind {
            ExprKind::Assign { target, .. } | ExprKind::AssignOp { target, .. } => (target, None),
            ExprKind::AssignRef { target, rhs } => (target, Some(rhs)),
            _ => return,
        };

        if contains_nullsafe(target) {
            out.push(
                Diagnostic::error(e.span, "Nullsafe operator cannot be on left side of assignment.")
                    .with_code("nullsafe.assign"),
            );
            return;
        }

        if let Some(rhs) = byref_rhs {
            if contains_nullsafe(rhs) {
                out.push(
                    Diagnostic::error(
                        e.span,
                        "Nullsafe operator cannot be on right side of assignment by reference.",
                    )
                    .with_code("nullsafe.byRef"),
                );
                return;
            }
        }

        if contains_non_assignable(target) {
            out.push(
                Diagnostic::error(e.span, "Expression on left side of assignment is not assignable.")
                    .with_code("assign.invalidExpr"),
            );
        }
    });
    out
}

/// Is `target` a valid `++`/`--` operand (a variable-like expression)?
fn is_inc_dec_variable(e: &Expr) -> bool {
    matches!(
        &unparen(e).kind,
        ExprKind::Variable(_)
            | ExprKind::VariableVariable(_)
            | ExprKind::DollarBrace(_)
            | ExprKind::Index { .. }
            | ExprKind::Prop { .. }
            | ExprKind::StaticProp { .. }
    )
}

/// `InvalidIncDecOperationRule` (level 0, the non-variable half): `++`/`--` can
/// only be applied to a variable-like expression. (The `*.type` half — applying
/// the operator to an invalid *type* — needs the type system and is deferred.)
fn run_invalid_inc_dec(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let (var, op_str, ident) = match &e.kind {
            ExprKind::PreInc(v) => (v, "++", "preInc.expr"),
            ExprKind::PostInc(v) => (v, "++", "postInc.expr"),
            ExprKind::PreDec(v) => (v, "--", "preDec.expr"),
            ExprKind::PostDec(v) => (v, "--", "postDec.expr"),
            _ => return,
        };
        if !is_inc_dec_variable(var) {
            out.push(
                Diagnostic::error(var.span, format!("Cannot use {op_str} on a non-variable."))
                    .with_code(ident),
            );
        }
    });
    out
}

/// `BacktickRule` (level 0): the backtick shell-exec operator `` `…` `` is
/// deprecated. Our target PHP version (8.6-dev) deprecates it, so it always
/// fires; use a `shell_exec()` call instead.
fn run_backtick(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        if let ExprKind::ShellExec(_) = &e.kind {
            out.push(
                Diagnostic::error(
                    e.span,
                    "Backtick operator is deprecated in PHP 8.5. Use shell_exec() function call instead.",
                )
                .with_code("backtick.deprecated"),
            );
        }
    });
    out
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "operators.invalidAssignVar", level: 0, run: run_invalid_assign_var },
    RuleEntry { name: "operators.invalidIncDec", level: 0, run: run_invalid_inc_dec },
    RuleEntry { name: "operators.backtick", level: 0, run: run_backtick },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- InvalidAssignVarRule -------------------------------------------------

    #[test]
    fn plain_variable_assign_is_ok() {
        assert!(codes("<?php $x = 1;", run_invalid_assign_var).is_empty());
        assert!(codes("<?php $x += 1;", run_invalid_assign_var).is_empty());
    }

    #[test]
    fn assignable_targets_are_ok() {
        assert!(codes("<?php $a->b = 1;", run_invalid_assign_var).is_empty());
        assert!(codes("<?php $a[0] = 1;", run_invalid_assign_var).is_empty());
        assert!(codes("<?php A::$b = 1;", run_invalid_assign_var).is_empty());
        assert!(codes("<?php [$a, $b] = $c;", run_invalid_assign_var).is_empty());
        assert!(codes("<?php list($a, $b) = $c;", run_invalid_assign_var).is_empty());
        assert!(codes("<?php $$x = 1;", run_invalid_assign_var).is_empty());
    }

    #[test]
    fn non_assignable_left_side_is_flagged() {
        assert_eq!(codes("<?php 1 = 1;", run_invalid_assign_var), ["assign.invalidExpr"]);
        assert_eq!(codes("<?php foo() = 1;", run_invalid_assign_var), ["assign.invalidExpr"]);
    }

    #[test]
    fn non_assignable_inside_destructuring_is_flagged() {
        assert_eq!(codes("<?php [foo()] = $c;", run_invalid_assign_var), ["assign.invalidExpr"]);
    }

    #[test]
    fn nullsafe_on_left_side_is_flagged() {
        assert_eq!(codes("<?php $a?->b = 1;", run_invalid_assign_var), ["nullsafe.assign"]);
        // Nullsafe deeper in the chain spine is still flagged.
        assert_eq!(codes("<?php $a?->b->c = 1;", run_invalid_assign_var), ["nullsafe.assign"]);
        assert_eq!(codes("<?php $a?->b[0] = 1;", run_invalid_assign_var), ["nullsafe.assign"]);
    }

    #[test]
    fn nullsafe_on_right_of_byref_assign_is_flagged() {
        assert_eq!(codes("<?php $a = &$b?->c;", run_invalid_assign_var), ["nullsafe.byRef"]);
    }

    #[test]
    fn nullsafe_on_right_of_plain_assign_is_ok() {
        assert!(codes("<?php $a = $b?->c;", run_invalid_assign_var).is_empty());
    }

    // --- InvalidIncDecOperationRule (non-variable half) -----------------------

    #[test]
    fn inc_dec_on_variable_is_ok() {
        assert!(codes("<?php $x++;", run_invalid_inc_dec).is_empty());
        assert!(codes("<?php ++$x;", run_invalid_inc_dec).is_empty());
        assert!(codes("<?php $a->b--;", run_invalid_inc_dec).is_empty());
        assert!(codes("<?php $a[0]++;", run_invalid_inc_dec).is_empty());
        assert!(codes("<?php A::$b--;", run_invalid_inc_dec).is_empty());
    }

    #[test]
    fn inc_dec_on_non_variable_is_flagged() {
        assert_eq!(codes("<?php 1++;", run_invalid_inc_dec), ["postInc.expr"]);
        assert_eq!(codes("<?php ++foo();", run_invalid_inc_dec), ["preInc.expr"]);
        assert_eq!(codes("<?php foo()--;", run_invalid_inc_dec), ["postDec.expr"]);
        assert_eq!(codes("<?php --foo();", run_invalid_inc_dec), ["preDec.expr"]);
    }

    // --- BacktickRule ---------------------------------------------------------

    #[test]
    fn backtick_is_flagged() {
        assert_eq!(codes("<?php `ls -la`;", run_backtick), ["backtick.deprecated"]);
        assert_eq!(codes("<?php $x = `whoami`;", run_backtick), ["backtick.deprecated"]);
    }

    #[test]
    fn no_backtick_no_diagnostic() {
        assert!(codes("<?php shell_exec('ls');", run_backtick).is_empty());
    }
}
