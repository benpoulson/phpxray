//! phpstan category **Operators** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Operators/` — 7 rule(s) at level(s) 0,2.
//! The rule set's coverage truth is `cargo run -p xtask -- rule-manifest`; for phpstan's behaviour read `phpstan-src/src/Rules/` directly. Add each rule as a `RuleEntry` to
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
//! Implemented (type-based — use `fa.type_of` + the conservative classifiers
//! below; flag only when EVERY member of an operand type is concrete and
//! known-incompatible, never on `mixed`/unknown/objects-with-overloads):
//! - `binaryOp.invalid` / `assignOp.invalid` (`InvalidBinaryOperationRule`,
//!   level 2) — an arithmetic/bitwise/shift/concat operator whose operand
//!   type can never be coerced to the operand kind the operator needs
//!   (e.g. `[] * 2`, `$arr . 'x'`, `"a" - "b"` is fine but `[] - 1` is not).
//! - `unaryOp.invalid` (`InvalidUnaryOperationRule`, level 2) — `+`/`-`/`~` on
//!   a non-numeric (and, for `~`, non-string) operand (`-[]`, `~$arr`).
//! - `equal.invalid` / `notEqual.invalid` / `smaller.invalid` /
//!   `smallerOrEqual.invalid` / `greater.invalid` / `greaterOrEqual.invalid` /
//!   `spaceship.invalid` (`InvalidComparisonOperationRule`, level 2) —
//!   comparing a number against a (possibly-nullable) object or array.
//!
//! Deferred (need richer type info than we model conservatively):
//! - DEFERRED: `InvalidIncDecOperationRule` (the `*.type` half — "Cannot use ++
//!   on <type>") — needs PHP's exact inc/dec type rules. Only the non-variable
//!   `*.expr` half is syntactic and implemented above.
//! - DEFERRED: `PipeOperatorRule` (`pipe.byRef`) — needs the callable type of the
//!   right operand (whether its first parameter is by-reference).

use crate::facts::AssignmentKind;
use crate::{
    facts::{AssignmentFact, BinaryFact, UnaryFact},
    FactRuleEntry, FactRuleHandler, FileAnalysis, RuleEntry,
};
use php_ast::{BinOp, Expr, ExprKind, UnOp};
use php_diagnostics::Diagnostic;
use php_resolve::{RefKind, Resolution, ResolvedRef};
use php_types::Type;
use std::collections::HashMap;

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
    for assign in fa.facts.assignments() {
        check_invalid_assign_var(fa, assign, &mut out);
    }
    out
}

fn check_invalid_assign_var(
    _fa: &FileAnalysis,
    assign: &AssignmentFact,
    out: &mut Vec<Diagnostic>,
) {
    let byref_rhs = match assign.kind {
        AssignmentKind::Ref => Some(assign.rhs),
        _ => None,
    };

    if contains_nullsafe(assign.target) {
        out.push(
            Diagnostic::error(
                assign.expr.span,
                "Nullsafe operator cannot be on left side of assignment.",
            )
            .with_code("nullsafe.assign"),
        );
        return;
    }

    if let Some(rhs) = byref_rhs {
        if contains_nullsafe(rhs) {
            out.push(
                Diagnostic::error(
                    assign.expr.span,
                    "Nullsafe operator cannot be on right side of assignment by reference.",
                )
                .with_code("nullsafe.byRef"),
            );
            return;
        }
    }

    if contains_non_assignable(assign.target) {
        out.push(
            Diagnostic::error(
                assign.expr.span,
                "Expression on left side of assignment is not assignable.",
            )
            .with_code("assign.invalidExpr"),
        );
    }
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
    for e in fa.facts.expressions() {
        check_invalid_inc_dec(fa, e, &mut out);
    }
    out
}

fn check_invalid_inc_dec(_fa: &FileAnalysis, e: &Expr, out: &mut Vec<Diagnostic>) {
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
}

/// `BacktickRule` (level 0): the backtick shell-exec operator `` `…` `` is
/// deprecated. Our target PHP version (8.6-dev) deprecates it, so it always
/// fires; use a `shell_exec()` call instead.
fn run_backtick(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for e in fa.facts.expressions() {
        check_backtick(fa, e, &mut out);
    }
    out
}

fn check_backtick(_fa: &FileAnalysis, e: &Expr, out: &mut Vec<Diagnostic>) {
    if let ExprKind::ShellExec(_) = &e.kind {
        out.push(
            Diagnostic::error(
                e.span,
                "Backtick operator is deprecated in PHP 8.5. Use shell_exec() function call instead.",
            )
            .with_code("backtick.deprecated"),
        );
    }
}

// ---------------------------------------------------------------------------
// Conservative operand-type classifiers
//
// The cardinal rule for these type-driven operator rules is ZERO false
// positives: we only flag an operand when we are *certain* every possible
// runtime value of its inferred type is incompatible with the operator. So the
// classifiers return `false` (= "could be ok, don't flag") for anything we are
// unsure about — `mixed`, unknown/template/conditional types, objects (which
// may define operator overloads via extensions or be `SimpleXMLElement`-like),
// resources, and any union/nullable that has even one compatible member.
// ---------------------------------------------------------------------------

/// `true` only if `t` can NEVER be coerced to a number (so a numeric operator on
/// it is definitely an error). Mirrors phpstan's `$type->toNumber()` returning
/// `ErrorType`. Conservative: unknown/object/mixed → `false`.
fn never_number(t: &Type) -> bool {
    match t {
        // Definitely-not-numeric value kinds.
        Type::Array(_) | Type::Iterable(_) | Type::List(_) | Type::Shape { .. } => true,
        // Numeric-coercible scalars (PHP coerces strings/bools/null in arithmetic).
        Type::Int
        | Type::Float
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Null
        | Type::String
        | Type::LiteralInt(_)
        | Type::LiteralString(_) => false,
        // A union/nullable is never-number only if *every* member is.
        Type::Union(parts) => parts.iter().all(never_number),
        Type::Nullable(inner) => never_number(inner),
        // Everything else (objects, callables, resources, mixed, templates,
        // class-string, self/static/parent, unknown, …) → not certain → don't flag.
        _ => false,
    }
}

/// `true` only if `t` can NEVER be coerced to a string (so `.`/`echo`/`print`/a
/// string cast on it is definitely an error). Mirrors `$type->toString()`
/// returning `ErrorType`. Arrays cannot be stringified; objects *might*
/// (`__toString`), so they are NOT flagged.
fn never_string(t: &Type) -> bool {
    match t {
        Type::Array(_) | Type::Iterable(_) | Type::List(_) | Type::Shape { .. } => true,
        Type::Int
        | Type::Float
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Null
        | Type::String
        | Type::LiteralInt(_)
        | Type::LiteralString(_) => false,
        Type::Union(parts) => parts.iter().all(never_string),
        Type::Nullable(inner) => never_string(inner),
        _ => false,
    }
}

/// `true` only if `t` is *definitely* not `string|int|float` (the operands `~`
/// accepts). Conservative on objects/mixed/unknown.
fn never_bitnot_operand(t: &Type) -> bool {
    match t {
        Type::Array(_) | Type::Iterable(_) | Type::List(_) | Type::Shape { .. } | Type::Null => {
            true
        }
        Type::Bool | Type::True | Type::False => true,
        Type::Int
        | Type::Float
        | Type::String
        | Type::StringOf(_)
        | Type::LiteralInt(_)
        | Type::LiteralString(_) => false,
        Type::Union(parts) => parts.iter().all(never_bitnot_operand),
        Type::Nullable(inner) => never_bitnot_operand(inner),
        _ => false,
    }
}

/// `true` only if `t` is *definitely* `int|float` (and nothing else) — used by
/// the comparison rule to detect the "number vs object/array" mismatch.
fn is_definitely_number(t: &Type) -> bool {
    match t {
        Type::Int | Type::Float | Type::LiteralInt(_) => true,
        Type::Union(parts) => !parts.is_empty() && parts.iter().all(is_definitely_number),
        _ => false,
    }
}

/// `true` only if `t` is *definitely* an object or array (with no `null`/scalar
/// alternatives) — the other side of the comparison mismatch.
fn is_definitely_object_or_array(t: &Type) -> bool {
    match t {
        Type::Object
        | Type::Named { .. }
        | Type::Array(_)
        | Type::List(_)
        | Type::Shape { .. }
        | Type::Iterable(_) => true,
        Type::Union(parts) => !parts.is_empty() && parts.iter().all(is_definitely_object_or_array),
        _ => false,
    }
}

/// `InvalidBinaryOperationRule` (level 2): an arithmetic / bitwise / shift /
/// concat operator applied to an operand whose type can never be coerced to what
/// the operator needs. We only flag when an operand is *definitely*
/// incompatible (`never_number`/`never_string`), so `mixed`, objects, and mixed
/// unions are silently allowed (zero false positives).
fn run_invalid_binary(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for e in fa.facts.expressions() {
        check_invalid_binary(fa, e, &mut out);
    }
    out
}

fn check_invalid_binary(fa: &FileAnalysis, e: &Expr, out: &mut Vec<Diagnostic>) {
    // Both `a OP b` and `a OP= b` share the operand-coercion check.
    let (op, lhs, rhs, ident) = match &e.kind {
        ExprKind::Binary { op, lhs, rhs } => (*op, lhs, rhs, "binaryOp.invalid"),
        ExprKind::AssignOp { op, target, rhs } => (*op, target, rhs, "assignOp.invalid"),
        _ => return,
    };

    // Pick the per-operator operand predicate + sigil. `Plus` allows arrays
    // (array + array is the union operator), so it is excluded from the
    // numeric check entirely (deciding `array + int` needs array-aware
    // logic we don't model — defer to avoid false positives).
    let (sigil, bad): (&str, fn(&Type) -> bool) = match op {
        BinOp::Concat => (".", never_string),
        BinOp::Sub => ("-", never_number),
        BinOp::Mul => ("*", never_number),
        BinOp::Div => ("/", never_number),
        BinOp::Mod => ("%", never_number),
        BinOp::Pow => ("**", never_number),
        BinOp::BitOr => ("|", never_number),
        BinOp::BitAnd => ("&", never_number),
        BinOp::BitXor => ("^", never_number),
        BinOp::Shl => ("<<", never_number),
        BinOp::Shr => (">>", never_number),
        // Add (`+`), comparisons, logical, coalesce, pipe, spaceship: not here.
        _ => return,
    };

    let lt = fa.type_of(lhs);
    let rt = fa.type_of(rhs);
    if bad(&lt) || bad(&rt) {
        out.push(
            Diagnostic::error(
                e.span,
                format!("Binary operation \"{sigil}\" between {lt} and {rt} results in an error."),
            )
            .with_code(ident),
        );
    }
}

/// `InvalidUnaryOperationRule` (level 2): `+`/`-`/`~` on an operand that can
/// never be the kind the operator needs (`+`/`-` need a number, `~` needs
/// int/float/string). `!` is always valid (any value is boolean-coercible).
fn run_invalid_unary(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for unary in fa.facts.unaries() {
        check_invalid_unary(fa, unary, &mut out);
    }
    out
}

fn check_invalid_unary(fa: &FileAnalysis, unary: &UnaryFact, out: &mut Vec<Diagnostic>) {
    let (sigil, bad): (&str, fn(&Type) -> bool) = match unary.op {
        UnOp::Plus => ("+", never_number),
        UnOp::Minus => ("-", never_number),
        UnOp::BitNot => ("~", never_bitnot_operand),
        UnOp::Not => return,
    };
    let t = fa.type_of(unary.inner);
    if bad(&t) {
        out.push(
            Diagnostic::error(
                unary.expr.span,
                format!("Unary operation \"{sigil}\" on {t} results in an error."),
            )
            .with_code("unaryOp.invalid"),
        );
    }
}

/// `InvalidComparisonOperationRule` (level 2): comparing a value that is
/// *definitely* a number against one that is *definitely* an object or array
/// (which PHP cannot meaningfully order). Only the certain "number vs
/// object/array" shape is flagged.
fn run_invalid_comparison(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for binary in fa.facts.binaries() {
        check_invalid_comparison(fa, binary, &mut out);
    }
    out
}

fn check_invalid_comparison(fa: &FileAnalysis, binary: &BinaryFact, out: &mut Vec<Diagnostic>) {
    let (sigil, ident) = match binary.op {
        BinOp::Eq => ("==", "equal.invalid"),
        BinOp::NotEq => ("!=", "notEqual.invalid"),
        BinOp::Lt => ("<", "smaller.invalid"),
        BinOp::LtEq => ("<=", "smallerOrEqual.invalid"),
        BinOp::Gt => (">", "greater.invalid"),
        BinOp::GtEq => (">=", "greaterOrEqual.invalid"),
        BinOp::Spaceship => ("<=>", "spaceship.invalid"),
        _ => return,
    };
    let lt = fa.type_of(binary.lhs);
    let rt = fa.type_of(binary.rhs);
    // Exactly one side a number, the other an object/array → invalid.
    let mismatch = (is_definitely_number(&lt) && is_definitely_object_or_array(&rt))
        || (is_definitely_number(&rt) && is_definitely_object_or_array(&lt));
    if mismatch {
        out.push(
            Diagnostic::error(
                binary.expr.span,
                format!(
                    "Comparison operation \"{sigil}\" between {lt} and {rt} results in an error."
                ),
            )
            .with_code(ident),
        );
    }
}

// ---------------------------------------------------------------------------
// PipeOperatorRule — `pipe.byRef`
// ---------------------------------------------------------------------------

/// The `|>` pipe (`$x |> $callable`) feeds its left value to the callable's first
/// parameter, which therefore may not be by-reference. We resolve the right
/// operand to a callable signature (a closure/arrow-fn directly, or a
/// first-class-callable `f(...)` / function-name string via reflection — including
/// the typed built-ins from Cap #4) and flag a by-ref first parameter.
fn run_pipe_byref(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap: HashMap<(u32, u32), &ResolvedRef> = fa
        .resolved_refs
        .iter()
        .filter(|r| r.kind == RefKind::Function)
        .map(|r| ((r.span.start, r.span.end), r))
        .collect();
    let mut out = Vec::new();
    for binary in fa.facts.binaries() {
        check_pipe_byref_with_refs(fa, binary, &fmap, &mut out);
    }
    out
}

fn check_pipe_byref(fa: &FileAnalysis, binary: &BinaryFact, out: &mut Vec<Diagnostic>) {
    let fmap: HashMap<(u32, u32), &ResolvedRef> = fa
        .resolved_refs
        .iter()
        .filter(|r| r.kind == RefKind::Function)
        .map(|r| ((r.span.start, r.span.end), r))
        .collect();
    check_pipe_byref_with_refs(fa, binary, &fmap, out);
}

fn check_pipe_byref_with_refs(
    fa: &FileAnalysis,
    binary: &BinaryFact,
    fmap: &HashMap<(u32, u32), &ResolvedRef>,
    out: &mut Vec<Diagnostic>,
) {
    if !matches!(binary.op, BinOp::Pipe) {
        return;
    }
    if let Some((true, name)) = callable_first_param(fa, binary.rhs, fmap) {
        let suffix = if name.is_empty() {
            String::new()
        } else {
            format!(" ${name}")
        };
        out.push(
            Diagnostic::error(
                binary.rhs.span,
                format!(
                    "Parameter #1{suffix} of callable on the right side of pipe operator is passed by reference."
                ),
            )
            .with_code("pipe.byRef"),
        );
    }
}

/// Resolve a callable expression to `(first_param_is_by_ref, first_param_name)`.
fn callable_first_param(
    fa: &FileAnalysis,
    e: &Expr,
    fmap: &HashMap<(u32, u32), &ResolvedRef>,
) -> Option<(bool, String)> {
    match &e.kind {
        ExprKind::Closure(c) => c
            .params
            .first()
            .map(|p| (p.by_ref, fa.interner.resolve(p.name).to_string())),
        ExprKind::ArrowFn(a) => a
            .params
            .first()
            .map(|p| (p.by_ref, fa.interner.resolve(p.name).to_string())),
        // First-class-callable `f(...)`.
        ExprKind::Call { callee, args } if args.iter().any(|a| a.placeholder) => {
            let ExprKind::Name(n) = &callee.kind else {
                return None;
            };
            let r = fmap.get(&(n.span.start, n.span.end))?;
            let fqn = match &r.resolution {
                Resolution::Fqn(f) => f.clone(),
                Resolution::Fallback { namespaced, global } => {
                    if fa.reflection.function(namespaced).is_some() {
                        namespaced.clone()
                    } else {
                        global.clone()
                    }
                }
                _ => return None,
            };
            let f = fa.reflection.function(&fqn)?;
            f.params.first().map(|p| (p.by_ref, p.name.clone()))
        }
        // A function-name string literal.
        ExprKind::Str(b) => {
            let name = std::str::from_utf8(b).ok()?;
            let f = fa.reflection.function(name)?;
            f.params.first().map(|p| (p.by_ref, p.name.clone()))
        }
        _ => None,
    }
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "operators.invalidAssignVar",
        level: 0,
        run: run_invalid_assign_var,
    },
    RuleEntry {
        name: "operators.invalidIncDec",
        level: 0,
        run: run_invalid_inc_dec,
    },
    RuleEntry {
        name: "operators.backtick",
        level: 0,
        run: run_backtick,
    },
    RuleEntry {
        name: "operators.pipeByRef",
        level: 0,
        run: run_pipe_byref,
    },
    RuleEntry {
        name: "operators.invalidBinary",
        level: 2,
        run: run_invalid_binary,
    },
    RuleEntry {
        name: "operators.invalidUnary",
        level: 2,
        run: run_invalid_unary,
    },
    RuleEntry {
        name: "operators.invalidComparison",
        level: 2,
        run: run_invalid_comparison,
    },
];

pub(crate) static FACT_RULES: &[FactRuleEntry] = &[
    FactRuleEntry::new(
        "operators.invalidAssignVar",
        FactRuleHandler::Assignment(check_invalid_assign_var),
    ),
    FactRuleEntry::new(
        "operators.invalidIncDec",
        FactRuleHandler::Expression(check_invalid_inc_dec),
    ),
    FactRuleEntry::new(
        "operators.backtick",
        FactRuleHandler::Expression(check_backtick),
    ),
    FactRuleEntry::new(
        "operators.pipeByRef",
        FactRuleHandler::Binary(check_pipe_byref),
    ),
    FactRuleEntry::new(
        "operators.invalidBinary",
        FactRuleHandler::Expression(check_invalid_binary),
    ),
    FactRuleEntry::new(
        "operators.invalidUnary",
        FactRuleHandler::Unary(check_invalid_unary),
    ),
    FactRuleEntry::new(
        "operators.invalidComparison",
        FactRuleHandler::Binary(check_invalid_comparison),
    ),
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- PipeOperatorRule (pipe.byRef) ----------------------------------------

    #[test]
    fn pipe_into_byref_closure_is_flagged() {
        let src = "<?php $r = 1 |> function (&$x) { return $x; };";
        assert_eq!(codes(src, run_pipe_byref), ["pipe.byRef"]);
    }

    #[test]
    fn pipe_into_byval_closure_is_clean() {
        let src = "<?php $r = 1 |> function ($x) { return $x; };";
        assert!(codes(src, run_pipe_byref).is_empty());
    }

    #[test]
    fn pipe_into_byref_arrow_is_flagged() {
        let src = "<?php $r = 1 |> fn (&$x) => $x;";
        assert_eq!(codes(src, run_pipe_byref), ["pipe.byRef"]);
    }

    #[test]
    fn pipe_into_user_function_first_class_callable() {
        // A by-ref-first-param function piped via first-class-callable syntax.
        let src = "<?php function inc(int &$n): void { $n++; } $r = 1 |> inc(...);";
        assert_eq!(codes(src, run_pipe_byref), ["pipe.byRef"]);
    }

    #[test]
    fn pipe_into_normal_function_is_clean() {
        let src = "<?php function dbl(int $n): int { return $n * 2; } $r = 1 |> dbl(...);";
        assert!(codes(src, run_pipe_byref).is_empty());
    }

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
        assert_eq!(
            codes("<?php 1 = 1;", run_invalid_assign_var),
            ["assign.invalidExpr"]
        );
        assert_eq!(
            codes("<?php foo() = 1;", run_invalid_assign_var),
            ["assign.invalidExpr"]
        );
    }

    #[test]
    fn non_assignable_inside_destructuring_is_flagged() {
        assert_eq!(
            codes("<?php [foo()] = $c;", run_invalid_assign_var),
            ["assign.invalidExpr"]
        );
    }

    #[test]
    fn nullsafe_on_left_side_is_flagged() {
        assert_eq!(
            codes("<?php $a?->b = 1;", run_invalid_assign_var),
            ["nullsafe.assign"]
        );
        // Nullsafe deeper in the chain spine is still flagged.
        assert_eq!(
            codes("<?php $a?->b->c = 1;", run_invalid_assign_var),
            ["nullsafe.assign"]
        );
        assert_eq!(
            codes("<?php $a?->b[0] = 1;", run_invalid_assign_var),
            ["nullsafe.assign"]
        );
    }

    #[test]
    fn nullsafe_on_right_of_byref_assign_is_flagged() {
        assert_eq!(
            codes("<?php $a = &$b?->c;", run_invalid_assign_var),
            ["nullsafe.byRef"]
        );
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
        assert_eq!(
            codes("<?php ++foo();", run_invalid_inc_dec),
            ["preInc.expr"]
        );
        assert_eq!(
            codes("<?php foo()--;", run_invalid_inc_dec),
            ["postDec.expr"]
        );
        assert_eq!(
            codes("<?php --foo();", run_invalid_inc_dec),
            ["preDec.expr"]
        );
    }

    // --- BacktickRule ---------------------------------------------------------

    #[test]
    fn backtick_is_flagged() {
        assert_eq!(
            codes("<?php `ls -la`;", run_backtick),
            ["backtick.deprecated"]
        );
        assert_eq!(
            codes("<?php $x = `whoami`;", run_backtick),
            ["backtick.deprecated"]
        );
    }

    #[test]
    fn no_backtick_no_diagnostic() {
        assert!(codes("<?php shell_exec('ls');", run_backtick).is_empty());
    }

    // --- InvalidBinaryOperationRule -------------------------------------------

    #[test]
    fn arithmetic_on_array_literal_is_flagged() {
        assert_eq!(
            codes("<?php $x = [] - 1;", run_invalid_binary),
            ["binaryOp.invalid"]
        );
        assert_eq!(
            codes("<?php $x = [1] * 2;", run_invalid_binary),
            ["binaryOp.invalid"]
        );
        assert_eq!(
            codes("<?php $x = 3 % [];", run_invalid_binary),
            ["binaryOp.invalid"]
        );
    }

    #[test]
    fn concat_with_array_literal_is_flagged() {
        assert_eq!(
            codes("<?php $x = [] . 'a';", run_invalid_binary),
            ["binaryOp.invalid"]
        );
        assert_eq!(
            codes("<?php $x = 'a' . [1, 2];", run_invalid_binary),
            ["binaryOp.invalid"]
        );
    }

    #[test]
    fn assign_op_on_array_literal_is_flagged() {
        // `$y .= []` — concat-assign with an array operand.
        assert_eq!(
            codes("<?php $y = 'x'; $y .= [];", run_invalid_binary),
            ["assignOp.invalid"]
        );
    }

    #[test]
    fn valid_arithmetic_and_concat_are_ok() {
        assert!(codes("<?php $x = 1 + 2;", run_invalid_binary).is_empty());
        assert!(codes("<?php $x = 3 - 4;", run_invalid_binary).is_empty());
        assert!(codes("<?php $x = 'a' . 'b';", run_invalid_binary).is_empty());
        // strings coerce to numbers in arithmetic — not flagged.
        assert!(codes("<?php $x = '5' * 2;", run_invalid_binary).is_empty());
    }

    #[test]
    fn unknown_operand_is_not_flagged() {
        // An untyped param is `mixed` — never flag (zero false positives).
        assert!(codes(
            "<?php function f($a) { return $a * 2; }",
            run_invalid_binary
        )
        .is_empty());
        assert!(codes(
            "<?php function f($a) { return $a . 'x'; }",
            run_invalid_binary
        )
        .is_empty());
    }

    #[test]
    fn nested_binary_is_reached() {
        assert_eq!(
            codes(
                "<?php function f() { $z = (1 + ([] * 3)); return $z; }",
                run_invalid_binary
            ),
            ["binaryOp.invalid"]
        );
    }

    // --- InvalidUnaryOperationRule --------------------------------------------

    #[test]
    fn unary_minus_on_array_is_flagged() {
        assert_eq!(
            codes("<?php $x = -[];", run_invalid_unary),
            ["unaryOp.invalid"]
        );
        assert_eq!(
            codes("<?php $x = +[1];", run_invalid_unary),
            ["unaryOp.invalid"]
        );
    }

    #[test]
    fn bitnot_on_array_is_flagged() {
        assert_eq!(
            codes("<?php $x = ~[];", run_invalid_unary),
            ["unaryOp.invalid"]
        );
    }

    #[test]
    fn bitnot_on_string_is_ok() {
        // `~` accepts strings (byte-wise complement).
        assert!(codes("<?php $x = ~'abc';", run_invalid_unary).is_empty());
    }

    #[test]
    fn valid_unary_is_ok() {
        assert!(codes("<?php $x = -5;", run_invalid_unary).is_empty());
        assert!(codes("<?php $x = ~5;", run_invalid_unary).is_empty());
        assert!(codes("<?php $x = ![];", run_invalid_unary).is_empty()); // ! is always ok
    }

    #[test]
    fn unary_on_unknown_is_not_flagged() {
        assert!(codes("<?php function f($a) { return -$a; }", run_invalid_unary).is_empty());
    }

    // --- InvalidComparisonOperationRule ---------------------------------------

    #[test]
    fn number_vs_array_comparison_is_flagged() {
        assert_eq!(
            codes("<?php $x = 1 < [];", run_invalid_comparison),
            ["smaller.invalid"]
        );
        assert_eq!(
            codes("<?php $x = [] > 2;", run_invalid_comparison),
            ["greater.invalid"]
        );
        assert_eq!(
            codes("<?php $x = 1 <=> [1];", run_invalid_comparison),
            ["spaceship.invalid"]
        );
    }

    #[test]
    fn number_vs_new_object_comparison_is_flagged() {
        let src = "<?php class A {} $x = 1 < new A();";
        assert_eq!(codes(src, run_invalid_comparison), ["smaller.invalid"]);
    }

    #[test]
    fn valid_comparisons_are_ok() {
        assert!(codes("<?php $x = 1 < 2;", run_invalid_comparison).is_empty());
        assert!(codes("<?php $x = 'a' < 'b';", run_invalid_comparison).is_empty());
        // array vs array is fine.
        assert!(codes("<?php $x = [] < [1];", run_invalid_comparison).is_empty());
    }

    #[test]
    fn comparison_with_unknown_is_not_flagged() {
        assert!(codes(
            "<?php function f($a) { return 1 < $a; }",
            run_invalid_comparison
        )
        .is_empty());
    }
}
