//! phpstan category **Comparison** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Comparison/`. Checklist: docs/phpstan-rules.md.
//! Add each rule as a `RuleEntry` to `RULES` (with a phpstan-style identifier on
//! its diagnostics).
//!
//! These rules report *constant conditions* — boolean expressions / comparisons
//! whose result is statically known — and strict comparisons between provably
//! disjoint types. phpstan computes these via full type narrowing; we only have a
//! flow-sensitive type map (`fa.type_of`) plus the literal AST. To keep **zero
//! false positives** we fire a constant-condition rule only when truthiness is
//! *provable*:
//!   - a literal `true`/`false`/`null`/int/float/string AST node, or
//!   - an expression the type map resolved to `Type::True`/`False`/`Null` (e.g.
//!     `$x = false; if ($x)`),
//!
//! and a strict-comparison rule only when **both** operands have concrete, known,
//! mutually-disjoint scalar/null categories (e.g. `int` vs `string`).
//!
//! Implemented (all level 4):
//! - `if.alwaysTrue` / `if.alwaysFalse` (`IfConstantConditionRule`) — incl. elseif:
//!   `elseif.alwaysTrue` / `elseif.alwaysFalse` (`ElseIfConstantConditionRule`).
//! - `ternary.alwaysTrue` / `ternary.alwaysFalse` (`TernaryOperatorConstantConditionRule`).
//! - `while.alwaysTrue` / `while.alwaysFalse` (`WhileLoopAlwaysTrueConditionRule` /
//!   `WhileLoopAlwaysFalseConditionRule`). We don't model loop exit points, so the
//!   always-true report is limited to a literal `true`/non-zero-int condition
//!   (the canonical `while (true)` case phpstan also flags).
//! - `doWhile.alwaysTrue` / `doWhile.alwaysFalse` (`DoWhileLoopConstantConditionRule`).
//! - `booleanNot.alwaysTrue` / `booleanNot.alwaysFalse` (`BooleanNotConstantConditionRule`).
//! - `booleanAnd.leftAlways*` / `.rightAlways*` (`BooleanAndConstantConditionRule`).
//! - `booleanOr.leftAlways*` / `.rightAlways*` (`BooleanOrConstantConditionRule`).
//! - `logicalXor.leftAlways*` / `.rightAlways*` (`LogicalXorConstantConditionRule`).
//! - `identical.alwaysTrue`/`.alwaysFalse` / `notIdentical.alwaysTrue`/`.alwaysFalse`
//!   (`StrictComparisonOfDifferentTypesRule`) — disjoint *types* via the type map,
//!   plus same-category *constant* operands folded by `php_infer::eval_const`.
//! - `equal.*`/`notEqual.*` (`ConstantLooseComparisonRule`) and
//!   `greater.*`/`smaller.*`/`greaterOrEqual.*`/`smallerOrEqual.*`
//!   (`NumberComparisonOperatorsConstantConditionRule`) — constant operands folded.
//!
//! - `match.alwaysFalse` / `match.alwaysTrue` (`MatchExpressionRule`, partial) —
//!   a `match` arm whose `subject === armCondition` folds to a compile-time
//!   constant: a constant-false comparison is a dead arm (`match.alwaysFalse`);
//!   a constant-true comparison with arms still following it makes those dead
//!   (`match.alwaysTrue`). Both operands must fold via `eval_const` (FP-safe).
//! - `match.void` (`UsageOfVoidMatchExpressionRule`) — a `match` expression whose
//!   inferred type is `void` used in a value position (not a bare statement).
//!
//! Deferred (need machinery we don't have):
//! - `ImpossibleCheckTypeFunctionCall/MethodCall/StaticMethodCallRule`
//!   (`function.impossibleType`, …) — needs evaluating a type-predicate against
//!   the (now narrowable) type map; a follow-up rule, not a capability gap.
//! - `MatchExpressionRule`'s `match.unhandled` — needs enum-case exhaustiveness,
//!   and enum cases are not yet reflected (`php-reflect` skips `EnumCase`).
//! - `ConstantConditionInTraitRule` — trait-instantiation aware; out of scope.

use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{BinOp, ElseIf, Expr, ExprKind, StmtKind, UnOp};
use php_diagnostics::Diagnostic;
use php_infer::{eval_const, ConstVal};
use php_span::Span;
use php_types::Type;

// ---------------------------------------------------------------------------
// Provable truthiness
// ---------------------------------------------------------------------------

/// The last `\`-separated segment of a name, lowercased (for matching the magic
/// constants `true`/`false`/`null`, which may appear bare or fully-qualified).
fn name_keyword(text: &str) -> String {
    text.rsplit('\\').next().unwrap_or(text).to_ascii_lowercase()
}

/// The statically-known truthiness of `e`, or `None` when it can't be proven.
///
/// Provable cases (conservative — no narrowing, no constant folding):
///   - literal AST nodes: `true`/`false`/`null`, int, float, non-empty string;
///   - an expression the type map resolved to `Type::True`/`False`/`Null` (e.g.
///     `$x = false`).
///
/// We deliberately do *not* try to prove truthiness for general expressions
/// (calls, variables of a non-literal type, comparisons, …) — that's where false
/// positives live.
fn const_bool(fa: &FileAnalysis, e: &Expr) -> Option<bool> {
    // Peel parentheses (the AST keeps them as `Paren`).
    if let ExprKind::Paren(inner) = &e.kind {
        return const_bool(fa, inner);
    }

    // Literal AST nodes carry their value directly — the most reliable source.
    match &e.kind {
        ExprKind::Int(n) => return Some(*n != 0),
        // Truthy unless the value is zero (`-0.0 == 0.0` in IEEE 754, so this
        // covers both). Comparing against the 0.0 literal is allowed by clippy.
        ExprKind::Float(f) => return Some(*f != 0.0),
        ExprKind::Str(bytes) => {
            // PHP falsy strings: "" and "0".
            let falsy = bytes.is_empty() || (bytes.len() == 1 && bytes[0] == b'0');
            return Some(!falsy);
        }
        ExprKind::Name(name) => match name_keyword(&name.text).as_str() {
            "true" => return Some(true),
            "false" | "null" => return Some(false),
            _ => {}
        },
        _ => {}
    }

    // Constant-fold operators over literals (`1 === 1`, `5 > 3`, `A && false`).
    if let Some(v) = eval_const(e) {
        return Some(v.truthy());
    }

    // Otherwise trust the type map only for the three constant-boolean types.
    match fa.type_of(e) {
        Type::True => Some(true),
        Type::False | Type::Null => Some(false),
        _ => None,
    }
}

/// Whether `e` is a literal `true` / non-zero int (peeling parens). Gates the
/// always-true loop reports (we don't track loop exit points / `break`).
fn is_literal_true(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Paren(inner) => is_literal_true(inner),
        ExprKind::Name(name) => name_keyword(&name.text) == "true",
        ExprKind::Int(n) => *n != 0,
        _ => false,
    }
}

fn diag(span: Span, msg: impl Into<String>, code: &'static str) -> Diagnostic {
    Diagnostic::error(span, msg).with_code(code)
}

// ---------------------------------------------------------------------------
// `if` / `elseif`  (IfConstantConditionRule / ElseIfConstantConditionRule)
// ---------------------------------------------------------------------------

fn run_if_condition(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::If { cond, elseifs, .. } = &s.kind {
            if let Some(v) = const_bool(fa, cond) {
                out.push(diag(
                    cond.span,
                    format!("If condition is always {v}."),
                    if v { "if.alwaysTrue" } else { "if.alwaysFalse" },
                ));
            }
            for ei in elseifs {
                push_elseif(fa, ei, &mut out);
            }
        }
    });
    out
}

fn push_elseif(fa: &FileAnalysis, ei: &ElseIf, out: &mut Vec<Diagnostic>) {
    if let Some(v) = const_bool(fa, &ei.cond) {
        out.push(diag(
            ei.cond.span,
            format!("Elseif condition is always {v}."),
            if v { "elseif.alwaysTrue" } else { "elseif.alwaysFalse" },
        ));
    }
}

// ---------------------------------------------------------------------------
// Ternary  (TernaryOperatorConstantConditionRule)
// ---------------------------------------------------------------------------

fn run_ternary_condition(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        if let ExprKind::Ternary { cond, .. } = &e.kind {
            if let Some(v) = const_bool(fa, cond) {
                out.push(diag(
                    cond.span,
                    format!("Ternary operator condition is always {v}."),
                    if v { "ternary.alwaysTrue" } else { "ternary.alwaysFalse" },
                ));
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// while / do-while
// ---------------------------------------------------------------------------

/// `WhileLoopAlwaysFalseConditionRule` + the literal-`true` subset of
/// `WhileLoopAlwaysTrueConditionRule`.
fn run_while_condition(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::While { cond, .. } = &s.kind {
            match const_bool(fa, cond) {
                Some(false) => {
                    out.push(diag(cond.span, "While loop condition is always false.", "while.alwaysFalse"))
                }
                Some(true) if is_literal_true(cond) => {
                    out.push(diag(cond.span, "While loop condition is always true.", "while.alwaysTrue"))
                }
                _ => {}
            }
        }
    });
    out
}

/// `DoWhileLoopConstantConditionRule`. Same exit-point caveat as `while`.
fn run_do_while_condition(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::DoWhile { cond, .. } = &s.kind {
            match const_bool(fa, cond) {
                Some(false) => out.push(diag(
                    cond.span,
                    "Do-while loop condition is always false.",
                    "doWhile.alwaysFalse",
                )),
                Some(true) if is_literal_true(cond) => out.push(diag(
                    cond.span,
                    "Do-while loop condition is always true.",
                    "doWhile.alwaysTrue",
                )),
                _ => {}
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// !  (BooleanNotConstantConditionRule)
// ---------------------------------------------------------------------------

fn run_boolean_not(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        if let ExprKind::Unary { op: UnOp::Not, expr } = &e.kind {
            if let Some(v) = const_bool(fa, expr) {
                // `!` flips: a constantly-true operand makes the negation false.
                let result = !v;
                out.push(diag(
                    expr.span,
                    format!("Negated boolean expression is always {result}."),
                    if result { "booleanNot.alwaysTrue" } else { "booleanNot.alwaysFalse" },
                ));
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// &&  ||  xor  (left/right side constant condition)
// ---------------------------------------------------------------------------

/// Shared body for `&&`/`||`/`xor`: report each side that is provably constant.
/// `prefix` is the phpstan identifier prefix; `sigil` the operator text shown.
fn binary_sides(
    fa: &FileAnalysis,
    matches_op: fn(BinOp) -> bool,
    prefix: &str,
    sigil: &str,
    out: &mut Vec<Diagnostic>,
) {
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Binary { op, lhs, rhs } = &e.kind else { return };
        if !matches_op(*op) {
            return;
        }
        if let Some(v) = const_bool(fa, lhs) {
            out.push(diag(
                lhs.span,
                format!("Left side of {sigil} is always {v}."),
                side_code(prefix, true, v),
            ));
        }
        if let Some(v) = const_bool(fa, rhs) {
            out.push(diag(
                rhs.span,
                format!("Right side of {sigil} is always {v}."),
                side_code(prefix, false, v),
            ));
        }
    });
}

/// Map (identifier prefix, is-left, value) → the static phpstan identifier.
fn side_code(prefix: &str, left: bool, v: bool) -> &'static str {
    match (prefix, left, v) {
        ("booleanAnd", true, true) => "booleanAnd.leftAlwaysTrue",
        ("booleanAnd", true, false) => "booleanAnd.leftAlwaysFalse",
        ("booleanAnd", false, true) => "booleanAnd.rightAlwaysTrue",
        ("booleanAnd", false, false) => "booleanAnd.rightAlwaysFalse",
        ("booleanOr", true, true) => "booleanOr.leftAlwaysTrue",
        ("booleanOr", true, false) => "booleanOr.leftAlwaysFalse",
        ("booleanOr", false, true) => "booleanOr.rightAlwaysTrue",
        ("booleanOr", false, false) => "booleanOr.rightAlwaysFalse",
        ("logicalXor", true, true) => "logicalXor.leftAlwaysTrue",
        ("logicalXor", true, false) => "logicalXor.leftAlwaysFalse",
        ("logicalXor", false, true) => "logicalXor.rightAlwaysTrue",
        ("logicalXor", false, false) => "logicalXor.rightAlwaysFalse",
        _ => "comparison.constantCondition",
    }
}

fn run_boolean_and(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    binary_sides(fa, |op| matches!(op, BinOp::BoolAnd), "booleanAnd", "&&", &mut out);
    binary_sides(fa, |op| matches!(op, BinOp::LogicalAnd), "booleanAnd", "and", &mut out);
    out
}

fn run_boolean_or(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    binary_sides(fa, |op| matches!(op, BinOp::BoolOr), "booleanOr", "||", &mut out);
    binary_sides(fa, |op| matches!(op, BinOp::LogicalOr), "booleanOr", "or", &mut out);
    out
}

fn run_logical_xor(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    binary_sides(fa, |op| matches!(op, BinOp::LogicalXor), "logicalXor", "xor", &mut out);
    out
}

// ---------------------------------------------------------------------------
// Strict comparison of disjoint types  (StrictComparisonOfDifferentTypesRule)
// ---------------------------------------------------------------------------

/// A coarse "scalar category" for disjointness. Two values can only be `===` if
/// they share a category (PHP `===` requires identical type). We assign a
/// category only to concrete, fully-known scalar/null types; anything that could
/// overlap (mixed/unknown/union/nullable/bool/object/array) yields `None`, so we
/// never claim disjointness we can't prove.
#[derive(PartialEq, Eq, Clone, Copy)]
enum Cat {
    Null,
    BoolTrue,
    BoolFalse,
    Int,
    Float,
    Str,
}

fn category(t: &Type) -> Option<Cat> {
    match t {
        Type::Null => Some(Cat::Null),
        Type::True => Some(Cat::BoolTrue),
        Type::False => Some(Cat::BoolFalse),
        Type::Int | Type::LiteralInt(_) => Some(Cat::Int),
        Type::Float => Some(Cat::Float),
        Type::String | Type::LiteralString(_) => Some(Cat::Str),
        // `bool` (non-constant), arrays, objects, unions, mixed, unknown, etc.
        // could overlap with the other side — not provably disjoint.
        _ => None,
    }
}

/// `true` when `a` and `b` can never be `===` because their concrete categories
/// differ. Two `Int`s (or `Int` vs `LiteralInt`) are *not* disjoint — their
/// values might match — so we only report *across* categories.
fn disjoint(a: &Type, b: &Type) -> bool {
    matches!((category(a), category(b)), (Some(ca), Some(cb)) if ca != cb)
}

fn run_strict_comparison(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Binary { op, lhs, rhs } = &e.kind else { return };
        let (sigil, always_false) = match op {
            BinOp::Identical => ("===", true),
            BinOp::NotIdentical => ("!==", false),
            _ => return,
        };
        let lt = fa.type_of(lhs);
        let rt = fa.type_of(rhs);
        // 1. Disjoint *types* — provably never/always equal, even for non-constant
        //    typed operands (`int $a === string $b`).
        if disjoint(&lt, &rt) {
            let (verb, code) = if always_false {
                ("false", "identical.alwaysFalse")
            } else {
                ("true", "notIdentical.alwaysTrue")
            };
            out.push(diag(
                e.span,
                format!("Strict comparison using {sigil} between {lt} and {rt} will always evaluate to {verb}."),
                code,
            ));
            return;
        }
        // 2. Same-category but constant-foldable (`1 === 1`, `1 === 2`).
        if let (Some(ConstVal::Bool(result)), Some(l), Some(r)) =
            (eval_const(e), eval_const(lhs), eval_const(rhs))
        {
            let code = match (op, result) {
                (BinOp::Identical, true) => "identical.alwaysTrue",
                (BinOp::Identical, false) => "identical.alwaysFalse",
                (BinOp::NotIdentical, true) => "notIdentical.alwaysTrue",
                (BinOp::NotIdentical, false) => "notIdentical.alwaysFalse",
                _ => return,
            };
            out.push(diag(
                e.span,
                format!(
                    "Strict comparison using {sigil} between {} and {} will always evaluate to {result}.",
                    l.describe(),
                    r.describe()
                ),
                code,
            ));
        }
    });
    out
}

// ---------------------------------------------------------------------------
// Constant loose (`==`/`!=`) and number (`<`/`>`/`<=`/`>=`) comparisons
// (ConstantLooseComparisonRule / NumberComparisonOperatorsConstantConditionRule)
// ---------------------------------------------------------------------------

fn run_constant_comparison(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Binary { op, lhs, rhs } = &e.kind else { return };
        // (sigil, node-type for `<` family, loose flag)
        let (sigil, ntype, loose) = match op {
            BinOp::Eq => ("==", "equal", true),
            BinOp::NotEq => ("!=", "notEqual", true),
            BinOp::Lt => ("<", "smaller", false),
            BinOp::Gt => (">", "greater", false),
            BinOp::LtEq => ("<=", "smallerOrEqual", false),
            BinOp::GtEq => (">=", "greaterOrEqual", false),
            _ => return,
        };
        let (Some(ConstVal::Bool(result)), Some(l), Some(r)) =
            (eval_const(e), eval_const(lhs), eval_const(rhs))
        else {
            return;
        };
        // The registry needs a `&'static str` code; enumerate the variants.
        let code = match (ntype, result) {
            ("equal", true) => "equal.alwaysTrue",
            ("equal", false) => "equal.alwaysFalse",
            ("notEqual", true) => "notEqual.alwaysTrue",
            ("notEqual", false) => "notEqual.alwaysFalse",
            ("smaller", true) => "smaller.alwaysTrue",
            ("smaller", false) => "smaller.alwaysFalse",
            ("greater", true) => "greater.alwaysTrue",
            ("greater", false) => "greater.alwaysFalse",
            ("smallerOrEqual", true) => "smallerOrEqual.alwaysTrue",
            ("smallerOrEqual", false) => "smallerOrEqual.alwaysFalse",
            ("greaterOrEqual", true) => "greaterOrEqual.alwaysTrue",
            ("greaterOrEqual", false) => "greaterOrEqual.alwaysFalse",
            _ => return,
        };
        let msg = if loose {
            format!(
                "Loose comparison using {sigil} between {} and {} will always evaluate to {result}.",
                l.describe(),
                r.describe()
            )
        } else {
            format!(
                "Comparison operation \"{sigil}\" between {} and {} is always {result}.",
                l.describe(),
                r.describe()
            )
        };
        out.push(diag(e.span, msg, code));
    });
    out
}

// ---------------------------------------------------------------------------
// Match arm constant conditions  (MatchExpressionRule, partial)
// ---------------------------------------------------------------------------

/// Report `match` arms whose `subject === armCondition` is a compile-time
/// constant. Mirrors the constant-folding subset of phpstan's
/// `MatchExpressionRule`: a constant-false arm is unreachable
/// (`match.alwaysFalse`); a constant-true arm makes the arms below it
/// unreachable (`match.alwaysTrue`, unless it's the last condition). We require
/// both the subject and the arm condition to fold via `eval_const`, so we never
/// flag anything whose runtime value we can't prove.
fn run_match_arms(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Match { subject, arms } = &e.kind else { return };
        let Some(subj) = eval_const(subject) else { return };

        // Every condition must fold to a constant; otherwise we can't reason about
        // any arm safely (a non-constant arm could match the subject).
        let mut folded: Vec<Vec<(Span, ConstVal)>> = Vec::with_capacity(arms.len());
        for arm in arms {
            let mut arm_vals = Vec::new();
            if let Some(arm_conds) = &arm.conds {
                for c in arm_conds {
                    let Some(v) = eval_const(c) else { return };
                    arm_vals.push((c.span, v));
                }
            }
            folded.push(arm_vals);
        }

        let arms_count = arms.len();
        let mut already_matched = false;
        for (arm_idx, arm_vals) in folded.iter().enumerate() {
            for (span, v) in arm_vals {
                if already_matched {
                    // A prior arm already always-matched → this arm is dead.
                    // phpstan reports the always-true arm once, not every dead
                    // arm that follows, so we don't emit here.
                    continue;
                }
                // PHP `match` uses `===`; `ConstVal`'s structural equality matches
                // strict-identity for these literal kinds (int ≠ float ≠ string).
                if *v == subj {
                    // Always-true: dead arms follow only if this isn't the last arm.
                    if arm_idx != arms_count - 1 {
                        out.push(diag(
                            *span,
                            format!(
                                "Match arm comparison between {} and {} is always true.",
                                subj.describe(),
                                v.describe()
                            ),
                            "match.alwaysTrue",
                        ));
                    }
                    already_matched = true;
                } else {
                    out.push(diag(
                        *span,
                        format!(
                            "Match arm comparison between {} and {} is always false.",
                            subj.describe(),
                            v.describe()
                        ),
                        "match.alwaysFalse",
                    ));
                }
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// Void match used in a value position  (UsageOfVoidMatchExpressionRule)
// ---------------------------------------------------------------------------

/// Report a `match` expression whose inferred type is `void` used where a value
/// is expected (anything other than a bare expression statement). Mirrors
/// phpstan's `UsageOfVoidMatchExpressionRule` (`!isInFirstLevelStatement()`).
fn run_void_match(fa: &FileAnalysis) -> Vec<Diagnostic> {
    // Spans of `match` expressions that ARE a bare statement (first-level) — those
    // are allowed to be void.
    let mut statement_matches = std::collections::HashSet::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::Expr(e) = &s.kind {
            if matches!(e.kind, ExprKind::Match { .. }) {
                statement_matches.insert((e.span.start, e.span.end));
            }
        }
    });

    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        if !matches!(e.kind, ExprKind::Match { .. }) {
            return;
        }
        if statement_matches.contains(&(e.span.start, e.span.end)) {
            return; // bare statement — its void result isn't "used"
        }
        if matches!(fa.type_of(e), Type::Void) {
            out.push(diag(
                e.span,
                "Result of match expression (void) is used.",
                "match.void",
            ));
        }
    });
    out
}

// ---------------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------------

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "comparison.if", level: 4, run: run_if_condition },
    RuleEntry { name: "comparison.ternary", level: 4, run: run_ternary_condition },
    RuleEntry { name: "comparison.while", level: 4, run: run_while_condition },
    RuleEntry { name: "comparison.doWhile", level: 4, run: run_do_while_condition },
    RuleEntry { name: "comparison.booleanNot", level: 4, run: run_boolean_not },
    RuleEntry { name: "comparison.booleanAnd", level: 4, run: run_boolean_and },
    RuleEntry { name: "comparison.booleanOr", level: 4, run: run_boolean_or },
    RuleEntry { name: "comparison.logicalXor", level: 4, run: run_logical_xor },
    RuleEntry { name: "comparison.strict", level: 4, run: run_strict_comparison },
    RuleEntry { name: "comparison.constant", level: 4, run: run_constant_comparison },
    RuleEntry { name: "comparison.matchArms", level: 4, run: run_match_arms },
    RuleEntry { name: "comparison.voidMatch", level: 2, run: run_void_match },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- if / elseif ---

    #[test]
    fn if_always_true_and_false() {
        assert_eq!(codes("<?php if (true) { echo 1; }", run_if_condition), ["if.alwaysTrue"]);
        assert_eq!(codes("<?php if (false) { echo 1; }", run_if_condition), ["if.alwaysFalse"]);
    }

    #[test]
    fn if_on_literal_int_and_string() {
        assert_eq!(codes("<?php if (1) { echo 1; }", run_if_condition), ["if.alwaysTrue"]);
        assert_eq!(codes("<?php if (0) { echo 1; }", run_if_condition), ["if.alwaysFalse"]);
        assert_eq!(codes("<?php if ('') { echo 1; }", run_if_condition), ["if.alwaysFalse"]);
        assert_eq!(codes("<?php if ('x') { echo 1; }", run_if_condition), ["if.alwaysTrue"]);
        assert_eq!(codes("<?php if ('0') { echo 1; }", run_if_condition), ["if.alwaysFalse"]);
    }

    #[test]
    fn if_via_type_map_assignment() {
        // `$x = false` flows Type::False into the condition.
        let src = "<?php $x = false; if ($x) { echo 1; }";
        assert_eq!(codes(src, run_if_condition), ["if.alwaysFalse"]);
    }

    #[test]
    fn if_on_variable_is_clean() {
        // An unknown variable's truthiness is not provable — no false positive.
        assert!(codes("<?php function f($x) { if ($x) { echo 1; } }", run_if_condition).is_empty());
        assert!(codes("<?php if (foo()) { echo 1; }", run_if_condition).is_empty());
    }

    #[test]
    fn elseif_always_constant() {
        // The `if` head is a call (unknown), the elseif is a literal false.
        let src = "<?php if (foo()) { } elseif (false) { }";
        assert_eq!(codes(src, run_if_condition), ["elseif.alwaysFalse"]);
    }

    #[test]
    fn nested_if_is_reached() {
        let src = "<?php function f() { if (true) { if (false) {} } }";
        let c = codes(src, run_if_condition);
        assert!(c.contains(&"if.alwaysTrue"));
        assert!(c.contains(&"if.alwaysFalse"));
    }

    // --- ternary ---

    #[test]
    fn ternary_constant() {
        assert_eq!(codes("<?php $x = true ? 1 : 2;", run_ternary_condition), ["ternary.alwaysTrue"]);
        assert_eq!(codes("<?php $x = false ? 1 : 2;", run_ternary_condition), ["ternary.alwaysFalse"]);
    }

    #[test]
    fn ternary_on_call_is_clean() {
        assert!(codes("<?php $x = foo() ? 1 : 2;", run_ternary_condition).is_empty());
    }

    // --- while / do-while ---

    #[test]
    fn while_always_false() {
        assert_eq!(codes("<?php while (false) { echo 1; }", run_while_condition), ["while.alwaysFalse"]);
    }

    #[test]
    fn while_true_is_flagged() {
        assert_eq!(codes("<?php while (true) { echo 1; }", run_while_condition), ["while.alwaysTrue"]);
    }

    #[test]
    fn while_on_call_is_clean() {
        assert!(codes("<?php while (foo()) { echo 1; }", run_while_condition).is_empty());
    }

    #[test]
    fn do_while_constant() {
        assert_eq!(
            codes("<?php do { echo 1; } while (false);", run_do_while_condition),
            ["doWhile.alwaysFalse"]
        );
        assert_eq!(
            codes("<?php do { echo 1; } while (true);", run_do_while_condition),
            ["doWhile.alwaysTrue"]
        );
    }

    // --- ! ---

    #[test]
    fn boolean_not_constant() {
        // !true -> always false ; !false -> always true.
        assert_eq!(codes("<?php $x = !true;", run_boolean_not), ["booleanNot.alwaysFalse"]);
        assert_eq!(codes("<?php $x = !false;", run_boolean_not), ["booleanNot.alwaysTrue"]);
    }

    #[test]
    fn boolean_not_on_call_is_clean() {
        assert!(codes("<?php $x = !foo();", run_boolean_not).is_empty());
    }

    // --- && / || / xor ---

    #[test]
    fn boolean_and_sides() {
        // Left literal-true, right a call (unknown): only the left fires.
        assert_eq!(codes("<?php $x = true && foo();", run_boolean_and), ["booleanAnd.leftAlwaysTrue"]);
        assert_eq!(codes("<?php $x = foo() && false;", run_boolean_and), ["booleanAnd.rightAlwaysFalse"]);
    }

    #[test]
    fn boolean_or_sides() {
        assert_eq!(codes("<?php $x = false || foo();", run_boolean_or), ["booleanOr.leftAlwaysFalse"]);
        assert_eq!(codes("<?php $x = foo() || true;", run_boolean_or), ["booleanOr.rightAlwaysTrue"]);
    }

    #[test]
    fn logical_and_keyword() {
        assert_eq!(codes("<?php $x = true and foo();", run_boolean_and), ["booleanAnd.leftAlwaysTrue"]);
    }

    #[test]
    fn logical_xor_sides() {
        assert_eq!(codes("<?php $x = true xor foo();", run_logical_xor), ["logicalXor.leftAlwaysTrue"]);
        assert_eq!(codes("<?php $x = foo() xor false;", run_logical_xor), ["logicalXor.rightAlwaysFalse"]);
    }

    #[test]
    fn boolean_and_on_two_calls_is_clean() {
        assert!(codes("<?php $x = foo() && bar();", run_boolean_and).is_empty());
    }

    // --- strict comparison of disjoint types ---

    #[test]
    fn strict_identical_disjoint_scalars() {
        // int literal === string literal: provably different categories.
        assert_eq!(codes("<?php $x = (1 === 'a');", run_strict_comparison), ["identical.alwaysFalse"]);
    }

    #[test]
    fn strict_not_identical_disjoint_scalars() {
        assert_eq!(codes("<?php $x = (1 !== 'a');", run_strict_comparison), ["notIdentical.alwaysTrue"]);
    }

    #[test]
    fn strict_disjoint_via_typed_params() {
        let src = "<?php function f(int $a, string $b) { return $a === $b; }";
        assert_eq!(codes(src, run_strict_comparison), ["identical.alwaysFalse"]);
    }

    #[test]
    fn strict_same_category_nonconstant_is_clean() {
        // Two int variables: same category, values unknown -> no report.
        let src = "<?php function f(int $a, int $b) { return $a === $b; }";
        assert!(codes(src, run_strict_comparison).is_empty());
    }

    #[test]
    fn strict_constant_equal_values_fold() {
        // Constant operands fold to a definite result (phpstan reports these).
        assert_eq!(codes("<?php $x = (1 === 1);", run_strict_comparison), ["identical.alwaysTrue"]);
        assert_eq!(codes("<?php $x = (1 === 2);", run_strict_comparison), ["identical.alwaysFalse"]);
        assert_eq!(codes("<?php $x = (2 !== 2);", run_strict_comparison), ["notIdentical.alwaysFalse"]);
    }

    // --- constant loose / number comparison ---

    #[test]
    fn constant_loose_comparison_folds() {
        assert_eq!(codes("<?php $x = (1 == 1);", run_constant_comparison), ["equal.alwaysTrue"]);
        assert_eq!(codes("<?php $x = (1 != 1);", run_constant_comparison), ["notEqual.alwaysFalse"]);
    }

    #[test]
    fn constant_number_comparison_folds() {
        assert_eq!(codes("<?php $x = (5 > 3);", run_constant_comparison), ["greater.alwaysTrue"]);
        assert_eq!(codes("<?php $x = (2 <= 1);", run_constant_comparison), ["smallerOrEqual.alwaysFalse"]);
    }

    #[test]
    fn nonconstant_comparison_is_clean() {
        let src = "<?php function f(int $a) { return $a > 3; }";
        assert!(codes(src, run_constant_comparison).is_empty());
    }

    #[test]
    fn strict_unknown_operand_is_clean() {
        // A param of unknown type vs a literal: not provably disjoint.
        let src = "<?php function f($a) { return $a === 1; }";
        assert!(codes(src, run_strict_comparison).is_empty());
    }

    #[test]
    fn loose_comparison_not_flagged_by_strict_rule() {
        assert!(codes("<?php $x = (1 == 'a');", run_strict_comparison).is_empty());
    }

    // --- match arm constant conditions ---

    #[test]
    fn match_arm_always_false_is_flagged() {
        // Subject 1; arm `2` can never match.
        let src = "<?php $x = match (1) { 2 => 'a', default => 'b' };";
        assert_eq!(codes(src, run_match_arms), ["match.alwaysFalse"]);
    }

    #[test]
    fn match_arm_always_true_with_following_arm_is_flagged() {
        // Subject 1; arm `1` always matches and a later arm `2` is dead. phpstan
        // reports the always-true arm once; the dead arm after it is not also
        // flagged as alwaysFalse.
        let src = "<?php $x = match (1) { 1 => 'a', 2 => 'b' };";
        assert_eq!(codes(src, run_match_arms), ["match.alwaysTrue"]);
    }

    #[test]
    fn match_earlier_false_arm_then_true_arm() {
        // Subject 2; arm `1` is always false, arm `2` always true (last arm so
        // no following dead arm) → only the false arm is reported.
        let src = "<?php $x = match (2) { 1 => 'a', 2 => 'b' };";
        assert_eq!(codes(src, run_match_arms), ["match.alwaysFalse"]);
    }

    #[test]
    fn match_arm_always_true_before_default_is_flagged() {
        // The `1` arm always matches; a trailing `default` arm is dead.
        let src = "<?php $x = match (1) { 1 => 'a', default => 'b' };";
        assert_eq!(codes(src, run_match_arms), ["match.alwaysTrue"]);
    }

    #[test]
    fn match_arm_always_true_as_last_condition_is_clean() {
        // Subject 1; the only/last condition is `1` → matches, but it's last so
        // no following arm is dead → no alwaysTrue report.
        let src = "<?php $x = match (1) { 1 => 'a' };";
        assert!(codes(src, run_match_arms).is_empty());
    }

    #[test]
    fn match_on_nonconstant_subject_is_clean() {
        let src = "<?php function f($n) { return match ($n) { 1 => 'a', 2 => 'b' }; }";
        assert!(codes(src, run_match_arms).is_empty());
    }

    #[test]
    fn match_with_nonconstant_arm_is_clean() {
        let src = "<?php function f($n) { return match (1) { $n => 'a', default => 'b' }; }";
        assert!(codes(src, run_match_arms).is_empty());
    }

    #[test]
    fn match_int_vs_string_arm_is_always_false() {
        // `===` distinguishes 1 (int) from '1' (string).
        let src = "<?php $x = match (1) { '1' => 'a', default => 'b' };";
        assert_eq!(codes(src, run_match_arms), ["match.alwaysFalse"]);
    }

    // --- void match used in a value position ---

    #[test]
    fn void_match_assigned_is_flagged() {
        let src = "<?php function v(): void {} $x = match (1) { default => v() };";
        assert_eq!(codes(src, run_void_match), ["match.void"]);
    }

    #[test]
    fn void_match_as_statement_is_clean() {
        // A bare statement-level match is allowed to be void.
        let src = "<?php function v(): void {} match (1) { default => v() };";
        assert!(codes(src, run_void_match).is_empty());
    }

    #[test]
    fn non_void_match_assigned_is_clean() {
        let src = "<?php $x = match (1) { default => 'a' };";
        assert!(codes(src, run_void_match).is_empty());
    }
}
