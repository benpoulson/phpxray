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
//! Partials / deferred:
//! - `function.impossibleType` (`ImpossibleCheckTypeFunctionCallRule`) — scalar
//!   `is_*` false-only subset.
//! - `method.impossibleType` / `staticMethod.impossibleType`
//!   (`ImpossibleCheckTypeMethodCallRule` / `ImpossibleCheckTypeStaticMethodCallRule`) —
//!   false-only subset for local methods with simple `@phpstan-assert` /
//!   `@phpstan-assert-if-true` parameter assertions.
//! - `MatchExpressionRule`'s `match.unhandled` — needs enum-case exhaustiveness,
//!   and enum cases are not yet reflected (`php-reflect` skips `EnumCase`).
//! - Always-true method/static type checks (`*.alreadyNarrowedType`) — needs
//!   phpstan's last-condition marker to avoid reports it suppresses.
//! - `ConstantConditionInTraitRule` — trait-instantiation aware; out of scope.

use crate::{
    facts::{BinaryFact, CallFact, MethodCallFact, StaticCallFact, UnaryFact},
    symbols, walk, FactKind, FactRuleEntry, FactRuleHandler, FileAnalysis, RuleEntry,
};
use php_ast::{
    BinOp, ClassDecl, ClassKind, ElseIf, Expr, ExprKind, Member, MemberName, MethodDecl, Stmt,
    StmtKind, UnOp,
};
use php_diagnostics::Diagnostic;
use php_infer::{eval_const, ConstVal};
use php_reflect::resolve_doc_type;
use php_resolve::{for_each_region, RefKind, Resolution, ResolvedRef, Scope};
use php_span::Span;
use php_types::Type;
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Provable truthiness
// ---------------------------------------------------------------------------

/// The last `\`-separated segment of a name, lowercased (for matching the magic
/// constants `true`/`false`/`null`, which may appear bare or fully-qualified).
fn name_keyword(text: &str) -> String {
    text.rsplit('\\')
        .next()
        .unwrap_or(text)
        .to_ascii_lowercase()
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
    for s in fa.facts.statements() {
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
    }
    out
}

fn push_elseif(fa: &FileAnalysis, ei: &ElseIf, out: &mut Vec<Diagnostic>) {
    if let Some(v) = const_bool(fa, &ei.cond) {
        out.push(diag(
            ei.cond.span,
            format!("Elseif condition is always {v}."),
            if v {
                "elseif.alwaysTrue"
            } else {
                "elseif.alwaysFalse"
            },
        ));
    }
}

// ---------------------------------------------------------------------------
// Ternary  (TernaryOperatorConstantConditionRule)
// ---------------------------------------------------------------------------

fn run_ternary_condition(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for e in fa.facts.expressions() {
        if let ExprKind::Ternary { cond, .. } = &e.kind {
            if let Some(v) = const_bool(fa, cond) {
                out.push(diag(
                    cond.span,
                    format!("Ternary operator condition is always {v}."),
                    if v {
                        "ternary.alwaysTrue"
                    } else {
                        "ternary.alwaysFalse"
                    },
                ));
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// while / do-while
// ---------------------------------------------------------------------------

/// `WhileLoopAlwaysFalseConditionRule` + the literal-`true` subset of
/// `WhileLoopAlwaysTrueConditionRule`.
fn run_while_condition(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for s in fa.facts.statements() {
        if let StmtKind::While { cond, body } = &s.kind {
            match const_bool(fa, cond) {
                Some(false) => out.push(diag(
                    cond.span,
                    "While loop condition is always false.",
                    "while.alwaysFalse",
                )),
                Some(true) if is_literal_true(cond) && !loop_body_exits(body, 0) => {
                    out.push(diag(
                        cond.span,
                        "While loop condition is always true.",
                        "while.alwaysTrue",
                    ))
                }
                _ => {}
            }
        }
    }
    out
}

/// `DoWhileLoopConstantConditionRule`. Same exit-point caveat as `while`.
fn run_do_while_condition(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for s in fa.facts.statements() {
        if let StmtKind::DoWhile { cond, body } = &s.kind {
            match const_bool(fa, cond) {
                Some(false) => out.push(diag(
                    cond.span,
                    "Do-while loop condition is always false.",
                    "doWhile.alwaysFalse",
                )),
                Some(true) if is_literal_true(cond) && !loop_body_exits(body, 0) => {
                    out.push(diag(
                        cond.span,
                        "Do-while loop condition is always true.",
                        "doWhile.alwaysTrue",
                    ))
                }
                _ => {}
            }
        }
    }
    out
}

/// Whether the loop body can *leave* the loop: a `break` reaching it, a
/// `return`/`throw`/`exit`/`goto`, or a multi-level `continue`. phpstan only
/// reports an always-true loop condition when the loop is breakless
/// (`BreaklessWhileLoopNode`) — `while (true) { …; break; }` and
/// `while (1) { …; return …; }` are intentional infinite-loop idioms, not
/// redundancy bugs. `depth` counts the break-able constructs between the
/// statement and OUR loop (a bare `break` inside a nested loop/switch exits
/// that construct, not ours).
fn loop_body_exits(s: &php_ast::Stmt, depth: i64) -> bool {
    let level = |e: &Option<Expr>| match e {
        None => 1,
        Some(Expr {
            kind: ExprKind::Int(n),
            ..
        }) => *n,
        // A dynamic `break $n` (PHP 5 relic) — assume it can exit us.
        Some(_) => i64::MAX,
    };
    match &s.kind {
        StmtKind::Break(n) => level(n) > depth,
        // `continue N` with N > depth+1 re-enters an OUTER construct — phpstan
        // bails on these too (it cannot prove the loop is breakless).
        StmtKind::Continue(n) => level(n) > depth + 1,
        StmtKind::Return(_) | StmtKind::Goto(_) => true,
        StmtKind::Expr(e) => matches!(&e.kind, ExprKind::Throw(_) | ExprKind::Exit(_)),
        StmtKind::Block(body) => body.iter().any(|s| loop_body_exits(s, depth)),
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            loop_body_exits(then, depth)
                || elseifs.iter().any(|ei| loop_body_exits(&ei.body, depth))
                || els.as_deref().is_some_and(|e| loop_body_exits(e, depth))
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => loop_body_exits(body, depth + 1),
        StmtKind::Switch { cases, .. } => cases
            .iter()
            .any(|c| c.body.iter().any(|s| loop_body_exits(s, depth + 1))),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter().any(|s| loop_body_exits(s, depth))
                || catches
                    .iter()
                    .any(|c| c.body.iter().any(|s| loop_body_exits(s, depth)))
                || finally
                    .as_ref()
                    .is_some_and(|f| f.iter().any(|s| loop_body_exits(s, depth)))
        }
        StmtKind::Declare {
            body: Some(body), ..
        } => loop_body_exits(body, depth),
        // Nested function/class bodies have their own control flow.
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// !  (BooleanNotConstantConditionRule)
// ---------------------------------------------------------------------------

fn run_boolean_not(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for unary in fa.facts.unaries() {
        check_boolean_not(fa, unary, &mut out);
    }
    out
}

fn check_boolean_not(fa: &FileAnalysis, unary: &UnaryFact, out: &mut Vec<Diagnostic>) {
    if !matches!(unary.op, UnOp::Not) {
        return;
    }
    if let Some(v) = const_bool(fa, unary.inner) {
        // `!` flips: a constantly-true operand makes the negation false.
        let result = !v;
        out.push(diag(
            unary.inner.span,
            format!("Negated boolean expression is always {result}."),
            if result {
                "booleanNot.alwaysTrue"
            } else {
                "booleanNot.alwaysFalse"
            },
        ));
    }
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
    for binary in fa.facts.binaries() {
        if !matches_op(binary.op) {
            continue;
        }
        if let Some(v) = const_bool(fa, binary.lhs) {
            out.push(diag(
                binary.lhs.span,
                format!("Left side of {sigil} is always {v}."),
                side_code(prefix, true, v),
            ));
        }
        if let Some(v) = const_bool(fa, binary.rhs) {
            out.push(diag(
                binary.rhs.span,
                format!("Right side of {sigil} is always {v}."),
                side_code(prefix, false, v),
            ));
        }
    }
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
    binary_sides(
        fa,
        |op| matches!(op, BinOp::BoolAnd),
        "booleanAnd",
        "&&",
        &mut out,
    );
    binary_sides(
        fa,
        |op| matches!(op, BinOp::LogicalAnd),
        "booleanAnd",
        "and",
        &mut out,
    );
    out
}

fn run_boolean_or(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    binary_sides(
        fa,
        |op| matches!(op, BinOp::BoolOr),
        "booleanOr",
        "||",
        &mut out,
    );
    binary_sides(
        fa,
        |op| matches!(op, BinOp::LogicalOr),
        "booleanOr",
        "or",
        &mut out,
    );
    out
}

fn run_logical_xor(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    binary_sides(
        fa,
        |op| matches!(op, BinOp::LogicalXor),
        "logicalXor",
        "xor",
        &mut out,
    );
    out
}

fn check_logical_xor(fa: &FileAnalysis, binary: &BinaryFact, out: &mut Vec<Diagnostic>) {
    if !matches!(binary.op, BinOp::LogicalXor) {
        return;
    }
    if let Some(v) = const_bool(fa, binary.lhs) {
        out.push(diag(
            binary.lhs.span,
            format!("Left side of xor is always {v}."),
            side_code("logicalXor", true, v),
        ));
    }
    if let Some(v) = const_bool(fa, binary.rhs) {
        out.push(diag(
            binary.rhs.span,
            format!("Right side of xor is always {v}."),
            side_code("logicalXor", false, v),
        ));
    }
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

// ---------------------------------------------------------------------------
// ImpossibleInstanceOfRule — instanceof.alwaysTrue / instanceof.alwaysFalse
// ---------------------------------------------------------------------------

/// `$x instanceof Foo` whose result is statically known. FP-safe: we only judge
/// when the tested class `Foo` and the value's class are fully indexed.
/// - **alwaysTrue**: the value is a concrete (non-nullable) class that *is-a* `Foo`.
/// - **alwaysFalse**: the value is a concrete **final** class that is not a `Foo`
///   (a non-final class could have a subclass that implements `Foo`, so it's not
///   provably false).
fn run_impossible_instanceof(fa: &FileAnalysis) -> Vec<Diagnostic> {
    // phpstan suppresses these when PHPDoc types aren't trusted as certain.
    if !fa.treat_phpdoc_types_as_certain {
        return Vec::new();
    }
    let cmap: HashMap<(u32, u32), &ResolvedRef> = fa
        .resolved_refs
        .iter()
        .filter(|r| r.kind == RefKind::Class)
        .map(|r| ((r.span.start, r.span.end), r))
        .collect();
    let mut out = Vec::new();
    for e in fa.facts.expressions() {
        check_impossible_instanceof_with_refs(fa, e, &cmap, &mut out);
    }
    out
}

fn check_impossible_instanceof(fa: &FileAnalysis, e: &Expr, out: &mut Vec<Diagnostic>) {
    if !fa.treat_phpdoc_types_as_certain {
        return;
    }
    let cmap: HashMap<(u32, u32), &ResolvedRef> = fa
        .resolved_refs
        .iter()
        .filter(|r| r.kind == RefKind::Class)
        .map(|r| ((r.span.start, r.span.end), r))
        .collect();
    check_impossible_instanceof_with_refs(fa, e, &cmap, out);
}

fn check_impossible_instanceof_with_refs(
    fa: &FileAnalysis,
    e: &Expr,
    cmap: &HashMap<(u32, u32), &ResolvedRef>,
    out: &mut Vec<Diagnostic>,
) {
    let ExprKind::Instanceof { expr, class } = &e.kind else {
        return;
    };
    let ExprKind::Name(n) = &class.kind else {
        return;
    };
    let Some(r) = cmap.get(&(n.span.start, n.span.end)) else {
        return;
    };
    // Only an explicitly-named, fully-known class (skip self/static/parent/builtin).
    let Resolution::Fqn(class_fqn) = &r.resolution else {
        return;
    };
    if !fa.class_fully_known(class_fqn) {
        return;
    }
    let vt = fa.type_of(expr);
    if let Some(result) = instanceof_result(fa, &vt, class_fqn) {
        // phpstan reports always-*false* instanceof by default but defaults the
        // always-*true* report OFF (`checkAlwaysTrueInstanceof`) — defensive
        // `instanceof` that's redundant is usually intentional. Match that.
        if result {
            return;
        }
        let (verb, code) = ("false", "instanceof.alwaysFalse");
        out.push(diag(
            e.span,
            format!("Instanceof between {vt} and {class_fqn} will always evaluate to {verb}."),
            code,
        ));
    }
}

fn instanceof_result(fa: &FileAnalysis, value: &Type, target: &str) -> Option<bool> {
    let Type::Named { fqn, .. } = value else {
        return None;
    };
    if !fa.class_fully_known(fqn) {
        return None;
    }
    if fa.reflection.is_subclass_of(fqn, target) {
        return Some(true);
    }
    // Not a subtype: provably false only if the value class is final.
    let is_final = fa
        .reflection
        .class(fqn)
        .map(|c| c.is_final)
        .unwrap_or(false);
    is_final.then_some(false)
}

// ---------------------------------------------------------------------------
// ImpossibleCheckTypeFunctionCallRule — function.impossibleType / .alreadyNarrowedType
// ---------------------------------------------------------------------------

/// `is_int($x)` / `is_string($x)` / … whose result is statically known from the
/// argument's inferred type. **alreadyNarrowedType** (always true) when the value
/// is exactly the predicate's category; **impossibleType** (always false) when
/// the value is a concrete, disjoint category. Only the scalar/null predicates
/// (whose category we can compare precisely) — FP-safe.
fn run_impossible_check_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.treat_phpdoc_types_as_certain {
        return Vec::new();
    }
    let fmap: HashMap<(u32, u32), &ResolvedRef> = fa
        .resolved_refs
        .iter()
        .filter(|r| r.kind == RefKind::Function)
        .map(|r| ((r.span.start, r.span.end), r))
        .collect();
    let mut out = Vec::new();
    for call in fa.facts.function_calls() {
        check_impossible_check_type_with_refs(fa, call, &fmap, &mut out);
    }
    out
}

fn check_impossible_check_type(fa: &FileAnalysis, call: &CallFact, out: &mut Vec<Diagnostic>) {
    if !fa.treat_phpdoc_types_as_certain {
        return;
    }
    let fmap: HashMap<(u32, u32), &ResolvedRef> = fa
        .resolved_refs
        .iter()
        .filter(|r| r.kind == RefKind::Function)
        .map(|r| ((r.span.start, r.span.end), r))
        .collect();
    check_impossible_check_type_with_refs(fa, call, &fmap, out);
}

fn check_impossible_check_type_with_refs(
    fa: &FileAnalysis,
    call: &CallFact,
    fmap: &HashMap<(u32, u32), &ResolvedRef>,
    out: &mut Vec<Diagnostic>,
) {
    let ExprKind::Name(n) = &call.callee.kind else {
        return;
    };
    let Some(r) = fmap.get(&(n.span.start, n.span.end)) else {
        return;
    };
    let fname = match &r.resolution {
        Resolution::Fqn(f) => f.trim_start_matches('\\').to_ascii_lowercase(),
        Resolution::Fallback { global, .. } => global.trim_start_matches('\\').to_ascii_lowercase(),
        _ => return,
    };
    let Some(pred) = predicate_cat(&fname) else {
        return;
    };
    let Some(arg0) = call.args.first() else {
        return;
    };
    if arg0.spread || arg0.placeholder || arg0.name.is_some() {
        return;
    }
    let Some(vcat) = category(&fa.type_of(&arg0.value)) else {
        return;
    };
    // Always-*true* type-check (`is_int($int)`) is OFF by default in phpstan
    // (`checkAlwaysTrueCheckTypeFunctionCall`) — it reports the resulting dead
    // code instead. Only report the impossible (always-false) case.
    if vcat == pred {
        return;
    }
    let (verb, code) = ("false", "function.impossibleType");
    out.push(diag(
        call.expr.span,
        format!("Call to function {fname}() will always evaluate to {verb}."),
        code,
    ));
}

/// The category a scalar/null type-predicate built-in asserts (only those whose
/// category we can compare precisely; `is_bool`/`is_array`/`is_object` span
/// categories we don't model here, so they're skipped — false-negative-safe).
fn predicate_cat(fname: &str) -> Option<Cat> {
    Some(match fname {
        "is_int" | "is_integer" | "is_long" => Cat::Int,
        "is_string" => Cat::Str,
        "is_float" | "is_double" => Cat::Float,
        "is_null" => Cat::Null,
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// ImpossibleCheckTypeMethodCallRule / StaticMethodCallRule
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct AssertMethod {
    param_index: usize,
    target: Type,
}

/// Local `@phpstan-assert` / `@phpstan-assert-if-true` methods keyed by
/// `(declaring-class-lower, method-lower, is-static)`.
fn assertion_methods(fa: &FileAnalysis) -> HashMap<(String, String, bool), AssertMethod> {
    let mut out = HashMap::new();
    for_each_class(fa, |scope, class_fqn, c| {
        for m in methods(c) {
            let Some(assertion) = method_assertion(fa, scope, m) else {
                continue;
            };
            out.insert(
                (
                    symbols::fqn_key(class_fqn),
                    fa.interner.resolve(m.name).to_ascii_lowercase(),
                    m.modifiers.is_static,
                ),
                assertion,
            );
        }
    });
    out
}

fn method_assertion(fa: &FileAnalysis, scope: &Scope, m: &MethodDecl) -> Option<AssertMethod> {
    let doc = m.doc.as_deref()?;
    for tag in php_phpdoc::parse_block(doc).tags {
        let name = tag.name.as_str();
        if !matches!(
            name,
            "phpstan-assert" | "phpstan-assert-if-true" | "psalm-assert" | "psalm-assert-if-true"
        ) {
            continue;
        }
        let (ty, rest) = parse_assert_type(&tag.value)?;
        let param_name = assert_param_name(rest)?;
        let param_index = m
            .params
            .iter()
            .position(|p| fa.interner.resolve(p.name) == param_name)?;
        let target = resolve_doc_type(scope, &[], &ty);
        // Keep only the categories this module can compare without ambiguity.
        category(&target)?;
        return Some(AssertMethod {
            param_index,
            target,
        });
    }
    None
}

fn parse_assert_type(value: &str) -> Option<(php_phpdoc::DocType, &str)> {
    let value = value.trim_start();
    // Exact-type assertions (`=int`) are safe for our coarse category checks.
    let value = value.strip_prefix('=').unwrap_or(value).trim_start();
    // Negated assertions (`!int`) invert the method result; defer until we model
    // the full assertion algebra.
    if value.starts_with('!') {
        return None;
    }
    let (ty, consumed) = php_phpdoc::parse_type_prefix(value)?;
    Some((ty, &value[consumed..]))
}

fn assert_param_name(rest: &str) -> Option<&str> {
    let rest = rest.trim_start();
    let rest = rest.strip_prefix('$')?;
    let end = rest
        .char_indices()
        .find_map(|(idx, ch)| (!(ch == '_' || ch.is_ascii_alphanumeric())).then_some(idx))
        .unwrap_or(rest.len());
    (end > 0).then_some(&rest[..end])
}

fn run_impossible_check_type_method_call(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.treat_phpdoc_types_as_certain {
        return Vec::new();
    }
    let assertions = assertion_methods(fa);
    let mut out = Vec::new();
    for call in fa.facts.method_calls() {
        check_impossible_check_type_method_call_with_assertions(fa, call, &assertions, &mut out);
    }
    out
}

fn check_impossible_check_type_method_call(
    fa: &FileAnalysis,
    call: &MethodCallFact,
    out: &mut Vec<Diagnostic>,
) {
    if !fa.treat_phpdoc_types_as_certain {
        return;
    }
    let assertions = assertion_methods(fa);
    check_impossible_check_type_method_call_with_assertions(fa, call, &assertions, out);
}

fn check_impossible_check_type_method_call_with_assertions(
    fa: &FileAnalysis,
    call: &MethodCallFact,
    assertions: &HashMap<(String, String, bool), AssertMethod>,
    out: &mut Vec<Diagnostic>,
) {
    if call.nullsafe {
        return;
    }
    let Some(method_name) = member_ident(fa, call.method) else {
        return;
    };
    let Some(receiver_fqn) = receiver_class(fa, call.recv) else {
        return;
    };
    if !fa.class_fully_known(&receiver_fqn) {
        return;
    }
    let Some(found) = fa.reflection.find_method(&receiver_fqn, &method_name) else {
        return;
    };
    if found.member.magic || found.member.is_static {
        return;
    }
    let Some(assertion) = assertions.get(&(
        symbols::fqn_key(found.declaring_class),
        found.member.name.to_ascii_lowercase(),
        false,
    )) else {
        return;
    };
    if assertion_call_is_false(fa, &assertion.target, assertion.param_index, call.args) {
        out.push(diag(
            call.expr.span,
            format!(
                "Call to method {}::{}() will always evaluate to false.",
                found.declaring_class.trim_start_matches('\\'),
                found.member.name
            ),
            "method.impossibleType",
        ));
    }
}

fn run_impossible_check_type_static_method_call(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.treat_phpdoc_types_as_certain {
        return Vec::new();
    }
    let assertions = assertion_methods(fa);
    let cmap: HashMap<(u32, u32), &ResolvedRef> = fa
        .resolved_refs
        .iter()
        .filter(|r| r.kind == RefKind::Class)
        .map(|r| ((r.span.start, r.span.end), r))
        .collect();
    let mut out = Vec::new();
    for call in fa.facts.static_calls() {
        check_impossible_check_type_static_method_call_with_maps(
            fa,
            call,
            &assertions,
            &cmap,
            &mut out,
        );
    }
    out
}

fn check_impossible_check_type_static_method_call(
    fa: &FileAnalysis,
    call: &StaticCallFact,
    out: &mut Vec<Diagnostic>,
) {
    if !fa.treat_phpdoc_types_as_certain {
        return;
    }
    let assertions = assertion_methods(fa);
    let cmap: HashMap<(u32, u32), &ResolvedRef> = fa
        .resolved_refs
        .iter()
        .filter(|r| r.kind == RefKind::Class)
        .map(|r| ((r.span.start, r.span.end), r))
        .collect();
    check_impossible_check_type_static_method_call_with_maps(fa, call, &assertions, &cmap, out);
}

fn check_impossible_check_type_static_method_call_with_maps(
    fa: &FileAnalysis,
    call: &StaticCallFact,
    assertions: &HashMap<(String, String, bool), AssertMethod>,
    cmap: &HashMap<(u32, u32), &ResolvedRef>,
    out: &mut Vec<Diagnostic>,
) {
    let Some(method_name) = member_ident(fa, call.method) else {
        return;
    };
    let Some(target_fqn) = static_call_class(fa, cmap, call.class) else {
        return;
    };
    if !fa.class_fully_known(&target_fqn) {
        return;
    }
    let Some(found) = fa.reflection.find_method(&target_fqn, &method_name) else {
        return;
    };
    if found.member.magic || !found.member.is_static {
        return;
    }
    let Some(assertion) = assertions.get(&(
        symbols::fqn_key(found.declaring_class),
        found.member.name.to_ascii_lowercase(),
        true,
    )) else {
        return;
    };
    if assertion_call_is_false(fa, &assertion.target, assertion.param_index, call.args) {
        out.push(diag(
            call.expr.span,
            format!(
                "Call to static method {}::{}() will always evaluate to false.",
                found.declaring_class.trim_start_matches('\\'),
                found.member.name
            ),
            "staticMethod.impossibleType",
        ));
    }
}

fn assertion_call_is_false(
    fa: &FileAnalysis,
    target: &Type,
    param_index: usize,
    args: &[php_ast::Arg],
) -> bool {
    let Some(arg) = args.get(param_index) else {
        return false;
    };
    if arg.spread || arg.placeholder || arg.name.is_some() {
        return false;
    }
    let Some(actual) = category(&fa.type_of(&arg.value)) else {
        return false;
    };
    let Some(expected) = category(target) else {
        return false;
    };
    actual != expected
}

fn member_ident(fa: &FileAnalysis, m: &MemberName) -> Option<String> {
    match m {
        MemberName::Ident(sym) => Some(fa.interner.resolve(*sym).to_string()),
        MemberName::Var(_) | MemberName::Expr(_) => None,
    }
}

fn receiver_class(fa: &FileAnalysis, recv: &Expr) -> Option<String> {
    match fa.type_of(recv) {
        Type::Named { fqn, .. } => Some(fqn.to_string()),
        _ => None,
    }
}

fn static_call_class(
    _fa: &FileAnalysis,
    cmap: &HashMap<(u32, u32), &ResolvedRef>,
    class: &Expr,
) -> Option<String> {
    let ExprKind::Name(n) = &class.kind else {
        return None;
    };
    let r = cmap.get(&(n.span.start, n.span.end))?;
    match &r.resolution {
        Resolution::Fqn(fqn) => Some(fqn.clone()),
        Resolution::Fallback { .. } | Resolution::LateStatic(_) | Resolution::BuiltinType(_) => {
            None
        }
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
    interner: &php_intern::Interner,
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
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                for s in &c.body {
                    walk_class_stmt(s, scope, interner, f);
                }
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for s in body {
                walk_class_stmt(s, scope, interner, f);
            }
            for c in catches {
                for s in &c.body {
                    walk_class_stmt(s, scope, interner, f);
                }
            }
            if let Some(fin) = finally {
                for s in fin {
                    walk_class_stmt(s, scope, interner, f);
                }
            }
        }
        _ => {}
    }
}

fn methods(c: &ClassDecl) -> impl Iterator<Item = &MethodDecl> {
    c.members.iter().filter_map(|m| match m {
        Member::Method(md) => Some(md),
        _ => None,
    })
}

fn run_strict_comparison(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for binary in fa.facts.binaries() {
        check_strict_comparison(fa, binary, &mut out);
    }
    out
}

fn check_strict_comparison(fa: &FileAnalysis, binary: &BinaryFact, out: &mut Vec<Diagnostic>) {
    let (sigil, always_false) = match binary.op {
        BinOp::Identical => ("===", true),
        BinOp::NotIdentical => ("!==", false),
        _ => return,
    };
    let lt = fa.type_of(binary.lhs);
    let rt = fa.type_of(binary.rhs);
    // 1. Disjoint *types* — provably never/always equal, even for non-constant
    //    typed operands (`int $a === string $b`). `===` on disjoint types is
    //    always false (reported); `!==` is always true — and phpstan defaults
    //    the always-*true* strict-comparison report OFF
    //    (`checkAlwaysTrueStrictComparison`), so we only report the false case.
    if disjoint(&lt, &rt) {
        if !always_false {
            return;
        }
        // With `treatPhpDocTypesAsCertain: false`, phpstan only reports a
        // redundancy provable from *native* types alone — a defensive check
        // against a PHPDoc-declared type (`@return int|Node` … `false ===`)
        // is deliberate runtime hardening, not dead code.
        if !fa.treat_phpdoc_types_as_certain {
            let nl = fa.native_type_of(binary.lhs);
            let nr = fa.native_type_of(binary.rhs);
            if !disjoint(&nl, &nr) {
                return;
            }
        }
        let (verb, code) = ("false", "identical.alwaysFalse");
        out.push(diag(
            binary.expr.span,
            format!("Strict comparison using {sigil} between {lt} and {rt} will always evaluate to {verb}."),
            code,
        ));
        return;
    }
    // 2. Same-category but constant-foldable (`1 === 1`, `1 === 2`).
    let (Some(ConstVal::Bool(result)), Some(l), Some(r)) = (
        eval_const(binary.expr),
        eval_const(binary.lhs),
        eval_const(binary.rhs),
    ) else {
        return;
    };
    let code = match (binary.op, result) {
        (BinOp::Identical, true) => "identical.alwaysTrue",
        (BinOp::Identical, false) => "identical.alwaysFalse",
        (BinOp::NotIdentical, true) => "notIdentical.alwaysTrue",
        (BinOp::NotIdentical, false) => "notIdentical.alwaysFalse",
        _ => return,
    };
    out.push(diag(
        binary.expr.span,
        format!(
            "Strict comparison using {sigil} between {} and {} will always evaluate to {result}.",
            l.describe(),
            r.describe()
        ),
        code,
    ));
}

// ---------------------------------------------------------------------------
// Constant loose (`==`/`!=`) and number (`<`/`>`/`<=`/`>=`) comparisons
// (ConstantLooseComparisonRule / NumberComparisonOperatorsConstantConditionRule)
// ---------------------------------------------------------------------------

fn run_constant_comparison(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for binary in fa.facts.binaries() {
        check_constant_comparison(fa, binary, &mut out);
    }
    out
}

fn check_constant_comparison(_fa: &FileAnalysis, binary: &BinaryFact, out: &mut Vec<Diagnostic>) {
    // (sigil, node-type for `<` family, loose flag)
    let (sigil, ntype, loose) = match binary.op {
        BinOp::Eq => ("==", "equal", true),
        BinOp::NotEq => ("!=", "notEqual", true),
        BinOp::Lt => ("<", "smaller", false),
        BinOp::Gt => (">", "greater", false),
        BinOp::LtEq => ("<=", "smallerOrEqual", false),
        BinOp::GtEq => (">=", "greaterOrEqual", false),
        _ => return,
    };
    let (Some(ConstVal::Bool(result)), Some(l), Some(r)) = (
        eval_const(binary.expr),
        eval_const(binary.lhs),
        eval_const(binary.rhs),
    ) else {
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
    out.push(diag(binary.expr.span, msg, code));
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
    for e in fa.facts.expressions() {
        check_match_arms(fa, e, &mut out);
    }
    out
}

fn check_match_arms(_fa: &FileAnalysis, e: &Expr, out: &mut Vec<Diagnostic>) {
    let ExprKind::Match { subject, arms } = &e.kind else {
        return;
    };
    let Some(subj) = eval_const(subject) else {
        return;
    };

    // Every condition must fold to a constant; otherwise we can't reason about
    // any arm safely (a non-constant arm could match the subject).
    let mut folded: Vec<Vec<(Span, ConstVal)>> = Vec::with_capacity(arms.len());
    let mut all_folded = true;
    for arm in arms {
        let mut arm_vals = Vec::new();
        if let Some(arm_conds) = &arm.conds {
            for c in arm_conds {
                let Some(v) = eval_const(c) else {
                    all_folded = false;
                    break;
                };
                arm_vals.push((c.span, v));
            }
        }
        if !all_folded {
            break;
        }
        folded.push(arm_vals);
    }
    if !all_folded {
        return;
    }

    let arms_count = arms.len();
    let mut already_matched = false;
    for (arm_idx, arm_vals) in folded.iter().enumerate() {
        for (span, v) in arm_vals {
            if already_matched {
                // A prior arm already always-matched -> this arm is dead.
                // phpstan reports the always-true arm once, not every dead
                // arm that follows, so we don't emit here.
                continue;
            }
            // PHP `match` uses `===`; `ConstVal`'s structural equality matches
            // strict-identity for these literal kinds (int != float != string).
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
    for s in fa.facts.statements() {
        if let StmtKind::Expr(e) = &s.kind {
            if matches!(e.kind, ExprKind::Match { .. }) {
                statement_matches.insert((e.span.start, e.span.end));
            }
        }
    }

    let mut out = Vec::new();
    for e in fa.facts.expressions() {
        if !matches!(e.kind, ExprKind::Match { .. }) {
            continue;
        }
        if statement_matches.contains(&(e.span.start, e.span.end)) {
            continue; // bare statement — its void result isn't "used"
        }
        if matches!(fa.type_of(e), Type::Void) {
            out.push(diag(
                e.span,
                "Result of match expression (void) is used.",
                "match.void",
            ));
        }
    }
    out
}

// ---------------------------------------------------------------------------
// ConstantConditionInTraitRule — trait-context constant conditions
// ---------------------------------------------------------------------------

struct TraitInfo {
    scope: Scope,
    class: ClassDecl,
}

struct TraitCtx<'a> {
    fa: &'a FileAnalysis<'a>,
    scope: &'a Scope,
    consumer_fqn: &'a str,
    const_values: &'a HashMap<(String, String), ConstVal>,
}

fn run_constant_condition_in_trait(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut traits = HashMap::new();
    let mut consumers: HashMap<String, Vec<String>> = HashMap::new();
    let mut const_values = HashMap::new();

    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            let StmtKind::Class(c) = &st.kind else {
                continue;
            };
            let Some(name) = c.name else { continue };
            let fqn = scope.qualify(fa.interner.resolve(name));
            collect_foldable_class_constants(fa, &fqn, c, &mut const_values);
            if c.kind == ClassKind::Trait {
                traits.insert(
                    class_key(&fqn),
                    TraitInfo {
                        scope: scope.clone(),
                        class: c.clone(),
                    },
                );
                continue;
            }
            if c.kind == ClassKind::Interface {
                continue;
            }
            for m in &c.members {
                let Member::TraitUse(tu) = m else { continue };
                for tr in &tu.traits {
                    if let Resolution::Fqn(trait_fqn) = scope.resolve_class(tr) {
                        consumers
                            .entry(class_key(&trait_fqn))
                            .or_default()
                            .push(fqn.clone());
                    }
                }
            }
        }
    });

    let mut out = Vec::new();
    for (key, info) in traits {
        let Some(using_classes) = consumers.get(&key) else {
            continue;
        };
        for m in &info.class.members {
            let Member::Method(method) = m else { continue };
            let Some(body) = &method.body else { continue };
            for st in body {
                visit_trait_context_stmt(fa, &info, using_classes, &const_values, st, &mut out);
            }
        }
    }
    out
}

fn collect_foldable_class_constants(
    fa: &FileAnalysis,
    class_fqn: &str,
    c: &ClassDecl,
    out: &mut HashMap<(String, String), ConstVal>,
) {
    let key = class_key(class_fqn);
    for m in &c.members {
        let Member::ClassConst(cc) = m else { continue };
        for ce in &cc.consts {
            if let Some(v) = eval_const(&ce.value) {
                out.insert((key.clone(), fa.interner.resolve(ce.name).to_string()), v);
            }
        }
    }
}

fn visit_trait_context_stmt(
    fa: &FileAnalysis,
    info: &TraitInfo,
    using_classes: &[String],
    const_values: &HashMap<(String, String), ConstVal>,
    st: &Stmt,
    out: &mut Vec<Diagnostic>,
) {
    match &st.kind {
        StmtKind::If {
            cond,
            then,
            elseifs,
            els,
        } => {
            if let Some(v) = stable_trait_bool(fa, info, using_classes, const_values, cond) {
                out.push(diag(
                    cond.span,
                    format!("If condition is always {v}."),
                    if v { "if.alwaysTrue" } else { "if.alwaysFalse" },
                ));
            }
            collect_trait_context_expr_diags(fa, info, using_classes, const_values, cond, out);
            visit_trait_context_stmt(fa, info, using_classes, const_values, then, out);
            for ei in elseifs {
                if let Some(v) = stable_trait_bool(fa, info, using_classes, const_values, &ei.cond)
                {
                    out.push(diag(
                        ei.cond.span,
                        format!("Elseif condition is always {v}."),
                        if v {
                            "elseif.alwaysTrue"
                        } else {
                            "elseif.alwaysFalse"
                        },
                    ));
                }
                collect_trait_context_expr_diags(
                    fa,
                    info,
                    using_classes,
                    const_values,
                    &ei.cond,
                    out,
                );
                visit_trait_context_stmt(fa, info, using_classes, const_values, &ei.body, out);
            }
            if let Some(els) = els {
                visit_trait_context_stmt(fa, info, using_classes, const_values, els, out);
            }
        }
        StmtKind::While { cond, body } => {
            if let Some(v) = stable_trait_bool(fa, info, using_classes, const_values, cond) {
                out.push(diag(
                    cond.span,
                    format!("While loop condition is always {v}."),
                    if v {
                        "while.alwaysTrue"
                    } else {
                        "while.alwaysFalse"
                    },
                ));
            }
            collect_trait_context_expr_diags(fa, info, using_classes, const_values, cond, out);
            visit_trait_context_stmt(fa, info, using_classes, const_values, body, out);
        }
        StmtKind::DoWhile { body, cond } => {
            visit_trait_context_stmt(fa, info, using_classes, const_values, body, out);
            if let Some(v) = stable_trait_bool(fa, info, using_classes, const_values, cond) {
                out.push(diag(
                    cond.span,
                    format!("Do-while loop condition is always {v}."),
                    if v {
                        "doWhile.alwaysTrue"
                    } else {
                        "doWhile.alwaysFalse"
                    },
                ));
            }
            collect_trait_context_expr_diags(fa, info, using_classes, const_values, cond, out);
        }
        StmtKind::Block(stmts) => {
            for st in stmts {
                visit_trait_context_stmt(fa, info, using_classes, const_values, st, out);
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for st in body {
                visit_trait_context_stmt(fa, info, using_classes, const_values, st, out);
            }
            for catch in catches {
                for st in &catch.body {
                    visit_trait_context_stmt(fa, info, using_classes, const_values, st, out);
                }
            }
            if let Some(finally) = finally {
                for st in finally {
                    visit_trait_context_stmt(fa, info, using_classes, const_values, st, out);
                }
            }
        }
        StmtKind::Switch { subject, cases } => {
            collect_trait_context_expr_diags(fa, info, using_classes, const_values, subject, out);
            for case in cases {
                if let Some(cond) = &case.test {
                    collect_trait_context_expr_diags(
                        fa,
                        info,
                        using_classes,
                        const_values,
                        cond,
                        out,
                    );
                }
                for st in &case.body {
                    visit_trait_context_stmt(fa, info, using_classes, const_values, st, out);
                }
            }
        }
        StmtKind::For {
            init,
            cond,
            update,
            body,
        } => {
            for e in init.iter().chain(cond).chain(update) {
                collect_trait_context_expr_diags(fa, info, using_classes, const_values, e, out);
            }
            visit_trait_context_stmt(fa, info, using_classes, const_values, body, out);
        }
        StmtKind::Foreach {
            subject,
            key,
            value,
            body,
            ..
        } => {
            collect_trait_context_expr_diags(fa, info, using_classes, const_values, subject, out);
            if let Some(key) = key {
                collect_trait_context_expr_diags(fa, info, using_classes, const_values, key, out);
            }
            collect_trait_context_expr_diags(fa, info, using_classes, const_values, value, out);
            visit_trait_context_stmt(fa, info, using_classes, const_values, body, out);
        }
        StmtKind::Declare { directives, body } => {
            for (_, e) in directives {
                collect_trait_context_expr_diags(fa, info, using_classes, const_values, e, out);
            }
            if let Some(body) = body {
                visit_trait_context_stmt(fa, info, using_classes, const_values, body, out);
            }
        }
        _ => collect_trait_context_stmt_exprs(fa, info, using_classes, const_values, st, out),
    }
}

fn collect_trait_context_stmt_exprs(
    fa: &FileAnalysis,
    info: &TraitInfo,
    using_classes: &[String],
    const_values: &HashMap<(String, String), ConstVal>,
    st: &Stmt,
    out: &mut Vec<Diagnostic>,
) {
    match &st.kind {
        StmtKind::Expr(e) | StmtKind::Return(Some(e)) => {
            collect_trait_context_expr_diags(fa, info, using_classes, const_values, e, out);
        }
        StmtKind::Echo(exprs) | StmtKind::Global(exprs) | StmtKind::Unset(exprs) => {
            for e in exprs {
                collect_trait_context_expr_diags(fa, info, using_classes, const_values, e, out);
            }
        }
        StmtKind::StaticVars(vars) => {
            for v in vars {
                if let Some(default) = &v.default {
                    collect_trait_context_expr_diags(
                        fa,
                        info,
                        using_classes,
                        const_values,
                        default,
                        out,
                    );
                }
            }
        }
        StmtKind::ConstDecl { consts, .. } => {
            for c in consts {
                collect_trait_context_expr_diags(
                    fa,
                    info,
                    using_classes,
                    const_values,
                    &c.value,
                    out,
                );
            }
        }
        _ => {}
    }
}

fn collect_trait_context_expr_diags(
    fa: &FileAnalysis,
    info: &TraitInfo,
    using_classes: &[String],
    const_values: &HashMap<(String, String), ConstVal>,
    root: &Expr,
    out: &mut Vec<Diagnostic>,
) {
    walk::for_each_subexpr(root, &mut |e| match &e.kind {
        ExprKind::Ternary { cond, .. } => {
            if let Some(v) = stable_trait_bool(fa, info, using_classes, const_values, cond) {
                out.push(diag(
                    cond.span,
                    format!("Ternary operator condition is always {v}."),
                    if v {
                        "ternary.alwaysTrue"
                    } else {
                        "ternary.alwaysFalse"
                    },
                ));
            }
        }
        ExprKind::Unary {
            op: UnOp::Not,
            expr,
        } => {
            if let Some(v) = stable_trait_bool(fa, info, using_classes, const_values, expr) {
                let result = !v;
                out.push(diag(
                    e.span,
                    format!("Negated boolean expression is always {result}."),
                    if result {
                        "booleanNot.alwaysTrue"
                    } else {
                        "booleanNot.alwaysFalse"
                    },
                ));
            }
        }
        ExprKind::Binary { op, lhs, rhs } => {
            collect_trait_binary_side(fa, info, using_classes, const_values, *op, lhs, true, out);
            collect_trait_binary_side(fa, info, using_classes, const_values, *op, rhs, false, out);
            collect_trait_comparison(fa, info, using_classes, const_values, e, *op, lhs, rhs, out);
        }
        ExprKind::Match { subject, arms } => {
            collect_trait_match(fa, info, using_classes, const_values, e, subject, arms, out);
        }
        _ => {}
    });
}

#[allow(clippy::too_many_arguments)]
fn collect_trait_binary_side(
    fa: &FileAnalysis,
    info: &TraitInfo,
    using_classes: &[String],
    const_values: &HashMap<(String, String), ConstVal>,
    op: BinOp,
    side: &Expr,
    left: bool,
    out: &mut Vec<Diagnostic>,
) {
    let (prefix, sigil) = match op {
        BinOp::BoolAnd | BinOp::LogicalAnd => ("booleanAnd", "&&"),
        BinOp::BoolOr | BinOp::LogicalOr => ("booleanOr", "||"),
        BinOp::LogicalXor => ("logicalXor", "xor"),
        _ => return,
    };
    if let Some(v) = stable_trait_bool(fa, info, using_classes, const_values, side) {
        out.push(diag(
            side.span,
            format!(
                "{} side of {sigil} is always {v}.",
                if left { "Left" } else { "Right" }
            ),
            side_code(prefix, left, v),
        ));
    }
}

#[allow(clippy::too_many_arguments)]
fn collect_trait_comparison(
    fa: &FileAnalysis,
    info: &TraitInfo,
    using_classes: &[String],
    const_values: &HashMap<(String, String), ConstVal>,
    e: &Expr,
    op: BinOp,
    lhs: &Expr,
    rhs: &Expr,
    out: &mut Vec<Diagnostic>,
) {
    if !trait_expr_has_context(fa, e) {
        return;
    }
    let Some(ConstVal::Bool(result)) = stable_trait_const(fa, info, using_classes, const_values, e)
    else {
        return;
    };
    let Some(l) = stable_trait_const_allow_literal(fa, info, using_classes, const_values, lhs)
    else {
        return;
    };
    let Some(r) = stable_trait_const_allow_literal(fa, info, using_classes, const_values, rhs)
    else {
        return;
    };
    match op {
        BinOp::Identical | BinOp::NotIdentical => {
            let sigil = if op == BinOp::Identical { "===" } else { "!==" };
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
        BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
            let (sigil, ntype, loose) = match op {
                BinOp::Eq => ("==", "equal", true),
                BinOp::NotEq => ("!=", "notEqual", true),
                BinOp::Lt => ("<", "smaller", false),
                BinOp::Gt => (">", "greater", false),
                BinOp::LtEq => ("<=", "smallerOrEqual", false),
                BinOp::GtEq => (">=", "greaterOrEqual", false),
                _ => return,
            };
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
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn collect_trait_match(
    fa: &FileAnalysis,
    info: &TraitInfo,
    using_classes: &[String],
    const_values: &HashMap<(String, String), ConstVal>,
    e: &Expr,
    subject: &Expr,
    arms: &[php_ast::MatchArm],
    out: &mut Vec<Diagnostic>,
) {
    if !trait_expr_has_context(fa, e) {
        return;
    }
    let Some(subj) =
        stable_trait_const_allow_literal(fa, info, using_classes, const_values, subject)
    else {
        return;
    };
    let mut folded: Vec<Vec<(Span, ConstVal)>> = Vec::new();
    for arm in arms {
        let Some(conds) = &arm.conds else { continue };
        let mut vals = Vec::new();
        for cond in conds {
            let Some(v) =
                stable_trait_const_allow_literal(fa, info, using_classes, const_values, cond)
            else {
                return;
            };
            vals.push((cond.span, v));
        }
        folded.push(vals);
    }
    let arms_count = folded.len();
    let mut already_matched = false;
    for (arm_idx, conds) in folded.iter().enumerate() {
        for (span, v) in conds {
            if already_matched {
                continue;
            }
            if *v == subj {
                if arm_idx != arms_count - 1 {
                    out.push(diag(
                        *span,
                        "Match arm comparison is always true.",
                        "match.alwaysTrue",
                    ));
                }
                already_matched = true;
            } else {
                out.push(diag(
                    *span,
                    "Match arm comparison is always false.",
                    "match.alwaysFalse",
                ));
            }
        }
    }
}

fn stable_trait_bool(
    fa: &FileAnalysis,
    info: &TraitInfo,
    using_classes: &[String],
    const_values: &HashMap<(String, String), ConstVal>,
    e: &Expr,
) -> Option<bool> {
    if !trait_expr_has_context(fa, e) {
        return None;
    }
    stable_trait_const(fa, info, using_classes, const_values, e).map(|v| v.truthy())
}

fn stable_trait_const(
    fa: &FileAnalysis,
    info: &TraitInfo,
    using_classes: &[String],
    const_values: &HashMap<(String, String), ConstVal>,
    e: &Expr,
) -> Option<ConstVal> {
    if using_classes.is_empty() {
        return None;
    }
    let mut result: Option<ConstVal> = None;
    for consumer in using_classes {
        let ctx = TraitCtx {
            fa,
            scope: &info.scope,
            consumer_fqn: consumer,
            const_values,
        };
        let v = trait_eval_const(&ctx, e)?;
        if result.as_ref().is_some_and(|prev| *prev != v) {
            return None;
        }
        result = Some(v);
    }
    result
}

fn stable_trait_const_allow_literal(
    fa: &FileAnalysis,
    info: &TraitInfo,
    using_classes: &[String],
    const_values: &HashMap<(String, String), ConstVal>,
    e: &Expr,
) -> Option<ConstVal> {
    if trait_expr_has_context(fa, e) {
        stable_trait_const(fa, info, using_classes, const_values, e)
    } else {
        eval_const(e)
    }
}

fn trait_eval_const(ctx: &TraitCtx<'_>, e: &Expr) -> Option<ConstVal> {
    use ConstVal::*;
    match &e.kind {
        ExprKind::Paren(inner) => trait_eval_const(ctx, inner),
        ExprKind::Int(n) => Some(Int(*n)),
        ExprKind::Float(f) => Some(Float(*f)),
        ExprKind::Str(b) => Some(Str(b.clone())),
        ExprKind::Name(n) => match n
            .text
            .trim_start_matches('\\')
            .to_ascii_lowercase()
            .as_str()
        {
            "true" => Some(Bool(true)),
            "false" => Some(Bool(false)),
            "null" => Some(Null),
            _ => None,
        },
        ExprKind::ClassConst { class, name } => {
            let MemberName::Ident(sym) = name else {
                return None;
            };
            let class_fqn = trait_class_expr_fqn(ctx, class)?;
            trait_class_const_value(ctx, &class_fqn, ctx.fa.interner.resolve(*sym))
        }
        ExprKind::Unary { op, expr } => {
            let v = trait_eval_const(ctx, expr)?;
            Some(match (op, v) {
                (UnOp::Not, v) => Bool(!v.truthy()),
                (UnOp::Minus, Int(n)) => Int(n.checked_neg()?),
                (UnOp::Minus, Float(f)) => Float(-f),
                (UnOp::Plus, Int(n)) => Int(n),
                (UnOp::Plus, Float(f)) => Float(f),
                _ => return None,
            })
        }
        ExprKind::Binary { op, lhs, rhs } => trait_eval_binary(ctx, *op, lhs, rhs),
        ExprKind::Instanceof { expr, class } => trait_instanceof(ctx, expr, class).map(Bool),
        _ => None,
    }
}

fn trait_eval_binary(ctx: &TraitCtx<'_>, op: BinOp, lhs: &Expr, rhs: &Expr) -> Option<ConstVal> {
    use ConstVal::*;
    match op {
        BinOp::BoolAnd | BinOp::LogicalAnd => {
            return Some(Bool(
                trait_eval_const(ctx, lhs)?.truthy() && trait_eval_const(ctx, rhs)?.truthy(),
            ));
        }
        BinOp::BoolOr | BinOp::LogicalOr => {
            return Some(Bool(
                trait_eval_const(ctx, lhs)?.truthy() || trait_eval_const(ctx, rhs)?.truthy(),
            ));
        }
        _ => {}
    }
    let l = trait_eval_const(ctx, lhs)?;
    let r = trait_eval_const(ctx, rhs)?;
    Some(match op {
        BinOp::Identical => Bool(l == r),
        BinOp::NotIdentical => Bool(l != r),
        BinOp::Eq => Bool(loose_const_eq(&l, &r)?),
        BinOp::NotEq => Bool(!loose_const_eq(&l, &r)?),
        BinOp::Lt => {
            let (l, r) = numeric_pair(&l, &r)?;
            Bool(l < r)
        }
        BinOp::Gt => {
            let (l, r) = numeric_pair(&l, &r)?;
            Bool(l > r)
        }
        BinOp::LtEq => {
            let (l, r) = numeric_pair(&l, &r)?;
            Bool(l <= r)
        }
        BinOp::GtEq => {
            let (l, r) = numeric_pair(&l, &r)?;
            Bool(l >= r)
        }
        BinOp::LogicalXor => Bool(l.truthy() ^ r.truthy()),
        _ => return None,
    })
}

fn loose_const_eq(l: &ConstVal, r: &ConstVal) -> Option<bool> {
    if l == r {
        return Some(true);
    }
    if let Some((a, b)) = numeric_pair(l, r) {
        return Some(a == b);
    }
    match (l, r) {
        (ConstVal::Bool(_), _) | (_, ConstVal::Bool(_)) => Some(l.truthy() == r.truthy()),
        (ConstVal::Null, ConstVal::Str(s)) | (ConstVal::Str(s), ConstVal::Null) => {
            Some(s.is_empty())
        }
        _ => None,
    }
}

fn numeric_pair(l: &ConstVal, r: &ConstVal) -> Option<(f64, f64)> {
    Some((const_number(l)?, const_number(r)?))
}

fn const_number(v: &ConstVal) -> Option<f64> {
    match v {
        ConstVal::Int(n) => Some(*n as f64),
        ConstVal::Float(f) => Some(*f),
        _ => None,
    }
}

fn trait_instanceof(ctx: &TraitCtx<'_>, expr: &Expr, class: &Expr) -> Option<bool> {
    let ExprKind::Variable(sym) = &expr.kind else {
        return None;
    };
    if ctx.fa.interner.resolve(*sym) != "this" {
        return None;
    }
    let target = trait_class_expr_fqn(ctx, class)?;
    if !ctx.fa.class_fully_known(ctx.consumer_fqn) || !ctx.fa.class_fully_known(&target) {
        return None;
    }
    if ctx.fa.reflection.is_subclass_of(ctx.consumer_fqn, &target) {
        return Some(true);
    }
    let class = ctx.fa.reflection.class(ctx.consumer_fqn)?;
    class.is_final.then_some(false)
}

fn trait_class_expr_fqn(ctx: &TraitCtx<'_>, e: &Expr) -> Option<String> {
    let ExprKind::Name(name) = &e.kind else {
        return None;
    };
    match ctx.scope.resolve_class(name) {
        Resolution::Fqn(fqn) => Some(fqn),
        Resolution::LateStatic(s) if s.eq_ignore_ascii_case("self") => {
            Some(ctx.consumer_fqn.to_string())
        }
        Resolution::LateStatic(s) if s.eq_ignore_ascii_case("static") => {
            Some(ctx.consumer_fqn.to_string())
        }
        Resolution::LateStatic(s) if s.eq_ignore_ascii_case("parent") => {
            let class = ctx.fa.reflection.class(ctx.consumer_fqn)?;
            class
                .parents
                .iter()
                .find_map(named_type_fqn)
                .map(str::to_string)
        }
        _ => None,
    }
}

fn trait_class_const_value(ctx: &TraitCtx<'_>, class_fqn: &str, name: &str) -> Option<ConstVal> {
    let found = ctx.fa.reflection.find_constant(class_fqn, name)?;
    if let Some(v) = found.member.int_value {
        return Some(ConstVal::Int(v));
    }
    ctx.const_values
        .get(&(class_key(found.declaring_class), name.to_string()))
        .cloned()
}

fn trait_expr_has_context(fa: &FileAnalysis, e: &Expr) -> bool {
    let mut found = false;
    walk::for_each_subexpr(e, &mut |sub| match &sub.kind {
        ExprKind::ClassConst { class, .. } => {
            if matches!(
                &class.kind,
                ExprKind::Name(name)
                    if matches!(name_keyword(&name.text).as_str(), "self" | "static" | "parent")
            ) {
                found = true;
            }
        }
        ExprKind::Instanceof { expr, .. } => {
            if matches!(&expr.kind, ExprKind::Variable(sym) if fa.interner.resolve(*sym) == "this")
            {
                found = true;
            }
        }
        _ => {}
    });
    found
}

fn named_type_fqn(t: &Type) -> Option<&str> {
    match t {
        Type::Named { fqn, .. } => Some(fqn),
        _ => None,
    }
}

fn class_key(fqn: &str) -> String {
    fqn.trim_start_matches('\\').to_ascii_lowercase()
}

// ---------------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------------

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "comparison.if",
        level: 4,
        run: run_if_condition,
    },
    RuleEntry {
        name: "comparison.ternary",
        level: 4,
        run: run_ternary_condition,
    },
    RuleEntry {
        name: "comparison.while",
        level: 4,
        run: run_while_condition,
    },
    RuleEntry {
        name: "comparison.doWhile",
        level: 4,
        run: run_do_while_condition,
    },
    RuleEntry {
        name: "comparison.booleanNot",
        level: 4,
        run: run_boolean_not,
    },
    RuleEntry {
        name: "comparison.booleanAnd",
        level: 4,
        run: run_boolean_and,
    },
    RuleEntry {
        name: "comparison.booleanOr",
        level: 4,
        run: run_boolean_or,
    },
    RuleEntry {
        name: "comparison.logicalXor",
        level: 4,
        run: run_logical_xor,
    },
    RuleEntry {
        name: "comparison.strict",
        level: 4,
        run: run_strict_comparison,
    },
    RuleEntry {
        name: "comparison.constant",
        level: 4,
        run: run_constant_comparison,
    },
    RuleEntry {
        name: "comparison.impossibleInstanceof",
        level: 4,
        run: run_impossible_instanceof,
    },
    RuleEntry {
        name: "comparison.impossibleCheckType",
        level: 4,
        run: run_impossible_check_type,
    },
    RuleEntry {
        name: "comparison.impossibleCheckTypeMethodCall",
        level: 4,
        run: run_impossible_check_type_method_call,
    },
    RuleEntry {
        name: "comparison.impossibleCheckTypeStaticMethodCall",
        level: 4,
        run: run_impossible_check_type_static_method_call,
    },
    RuleEntry {
        name: "comparison.matchArms",
        level: 4,
        run: run_match_arms,
    },
    RuleEntry {
        name: "comparison.voidMatch",
        level: 2,
        run: run_void_match,
    },
    RuleEntry {
        name: "comparison.constantConditionInTrait",
        level: 4,
        run: run_constant_condition_in_trait,
    },
];

pub(crate) static FACT_RULES: &[FactRuleEntry] = &[
    FactRuleEntry::new(
        "comparison.booleanNot",
        4,
        FactKind::Unary,
        FactRuleHandler::Unary(check_boolean_not),
    ),
    FactRuleEntry::new(
        "comparison.logicalXor",
        4,
        FactKind::Binary,
        FactRuleHandler::Binary(check_logical_xor),
    ),
    FactRuleEntry::new(
        "comparison.strict",
        4,
        FactKind::Binary,
        FactRuleHandler::Binary(check_strict_comparison),
    ),
    FactRuleEntry::new(
        "comparison.constant",
        4,
        FactKind::Binary,
        FactRuleHandler::Binary(check_constant_comparison),
    ),
    FactRuleEntry::new(
        "comparison.impossibleInstanceof",
        4,
        FactKind::Expression,
        FactRuleHandler::Expression(check_impossible_instanceof),
    ),
    FactRuleEntry::new(
        "comparison.impossibleCheckType",
        4,
        FactKind::FunctionCall,
        FactRuleHandler::FunctionCall(check_impossible_check_type),
    ),
    FactRuleEntry::new(
        "comparison.impossibleCheckTypeMethodCall",
        4,
        FactKind::MethodCall,
        FactRuleHandler::MethodCall(check_impossible_check_type_method_call),
    ),
    FactRuleEntry::new(
        "comparison.impossibleCheckTypeStaticMethodCall",
        4,
        FactKind::StaticCall,
        FactRuleHandler::StaticCall(check_impossible_check_type_static_method_call),
    ),
    FactRuleEntry::new(
        "comparison.matchArms",
        4,
        FactKind::Expression,
        FactRuleHandler::Expression(check_match_arms),
    ),
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{codes, codes_with};

    // --- impossible instanceof ---

    #[test]
    fn instanceof_subclass_always_true_is_off_by_default() {
        // phpstan defaults always-true instanceof reporting OFF; we match that.
        let src =
            "<?php class A {} class B extends A {} function f(B $b) { return $b instanceof A; }";
        assert!(codes(src, run_impossible_instanceof).is_empty());
    }

    #[test]
    fn instanceof_same_class_always_true_is_off_by_default() {
        let src = "<?php class A {} function f(A $a) { return $a instanceof A; }";
        assert!(codes(src, run_impossible_instanceof).is_empty());
    }

    #[test]
    fn instanceof_final_unrelated_always_false() {
        let src = "<?php final class C {} class D {} function f(C $c) { return $c instanceof D; }";
        assert_eq!(
            codes(src, run_impossible_instanceof),
            ["instanceof.alwaysFalse"]
        );
    }

    #[test]
    fn instanceof_nonfinal_unrelated_is_clean() {
        // E could have a subclass that extends F -> not provably false.
        let src = "<?php class E {} class F {} function f(E $e) { return $e instanceof F; }";
        assert!(codes(src, run_impossible_instanceof).is_empty());
    }

    #[test]
    fn instanceof_unknown_parent_is_clean() {
        let src = "<?php class C extends \\Vendor { } function f(C $c) { return $c instanceof D; }";
        assert!(codes(src, run_impossible_instanceof).is_empty());
    }

    // --- impossible is_* checks ---

    #[test]
    fn is_int_on_int_always_true_is_off_by_default() {
        // Always-true type-check reporting is off by default in phpstan.
        let src = "<?php function f(int $x) { return is_int($x); }";
        assert!(codes(src, run_impossible_check_type).is_empty());
    }

    #[test]
    fn is_int_on_string_always_false() {
        let src = "<?php function f(string $s) { return is_int($s); }";
        assert_eq!(
            codes(src, run_impossible_check_type),
            ["function.impossibleType"]
        );
    }

    #[test]
    fn is_string_on_mixed_is_clean() {
        let src = "<?php function f($x) { return is_string($x); }";
        assert!(codes(src, run_impossible_check_type).is_empty());
    }

    #[test]
    fn assertion_method_impossible_scalar_type() {
        let src = "<?php
            class TypeChecker {
                /** @phpstan-assert-if-true string $value */
                public function isString($value): bool { return is_string($value); }
            }
            function f(TypeChecker $c, int $i) { return $c->isString($i); }";
        assert_eq!(
            codes(src, run_impossible_check_type_method_call),
            ["method.impossibleType"]
        );
    }

    #[test]
    fn assertion_method_already_narrowed_is_deferred() {
        let src = "<?php
            class TypeChecker {
                /** @phpstan-assert-if-true string $value */
                public function isString($value): bool { return is_string($value); }
            }
            function f(TypeChecker $c, string $s) { return $c->isString($s); }";
        assert!(codes(src, run_impossible_check_type_method_call).is_empty());
    }

    #[test]
    fn assertion_method_on_mixed_is_clean() {
        let src = "<?php
            class TypeChecker {
                /** @phpstan-assert-if-true string $value */
                public function isString($value): bool { return is_string($value); }
            }
            function f(TypeChecker $c, $x) { return $c->isString($x); }";
        assert!(codes(src, run_impossible_check_type_method_call).is_empty());
    }

    #[test]
    fn method_without_assertion_doc_is_clean() {
        let src = "<?php
            class TypeChecker {
                public function isString($value): bool { return is_string($value); }
            }
            function f(TypeChecker $c, int $i) { return $c->isString($i); }";
        assert!(codes(src, run_impossible_check_type_method_call).is_empty());
    }

    #[test]
    fn assertion_static_method_impossible_scalar_type() {
        let src = "<?php
            class TypeChecker {
                /** @phpstan-assert-if-true string $value */
                public static function isString($value): bool { return is_string($value); }
            }
            function f(int $i) { return TypeChecker::isString($i); }";
        assert_eq!(
            codes(src, run_impossible_check_type_static_method_call),
            ["staticMethod.impossibleType"]
        );
    }

    #[test]
    fn assertion_static_method_already_narrowed_is_deferred() {
        let src = "<?php
            class TypeChecker {
                /** @phpstan-assert-if-true string $value */
                public static function isString($value): bool { return is_string($value); }
            }
            function f(string $s) { return TypeChecker::isString($s); }";
        assert!(codes(src, run_impossible_check_type_static_method_call).is_empty());
    }

    // --- if / elseif ---

    #[test]
    fn if_always_true_and_false() {
        assert_eq!(
            codes("<?php if (true) { echo 1; }", run_if_condition),
            ["if.alwaysTrue"]
        );
        assert_eq!(
            codes("<?php if (false) { echo 1; }", run_if_condition),
            ["if.alwaysFalse"]
        );
    }

    #[test]
    fn if_on_literal_int_and_string() {
        assert_eq!(
            codes("<?php if (1) { echo 1; }", run_if_condition),
            ["if.alwaysTrue"]
        );
        assert_eq!(
            codes("<?php if (0) { echo 1; }", run_if_condition),
            ["if.alwaysFalse"]
        );
        assert_eq!(
            codes("<?php if ('') { echo 1; }", run_if_condition),
            ["if.alwaysFalse"]
        );
        assert_eq!(
            codes("<?php if ('x') { echo 1; }", run_if_condition),
            ["if.alwaysTrue"]
        );
        assert_eq!(
            codes("<?php if ('0') { echo 1; }", run_if_condition),
            ["if.alwaysFalse"]
        );
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
        assert!(codes(
            "<?php function f($x) { if ($x) { echo 1; } }",
            run_if_condition
        )
        .is_empty());
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
        assert_eq!(
            codes("<?php $x = true ? 1 : 2;", run_ternary_condition),
            ["ternary.alwaysTrue"]
        );
        assert_eq!(
            codes("<?php $x = false ? 1 : 2;", run_ternary_condition),
            ["ternary.alwaysFalse"]
        );
    }

    #[test]
    fn ternary_on_call_is_clean() {
        assert!(codes("<?php $x = foo() ? 1 : 2;", run_ternary_condition).is_empty());
    }

    // --- while / do-while ---

    #[test]
    fn while_always_false() {
        assert_eq!(
            codes("<?php while (false) { echo 1; }", run_while_condition),
            ["while.alwaysFalse"]
        );
    }

    #[test]
    fn while_true_is_flagged() {
        assert_eq!(
            codes("<?php while (true) { echo 1; }", run_while_condition),
            ["while.alwaysTrue"]
        );
    }

    #[test]
    fn while_true_with_exit_points_is_an_intentional_loop() {
        // phpstan only checks BREAKLESS loops: `while (true)` with a break,
        // return, or throw is the idiomatic infinite loop.
        for src in [
            "<?php while (true) { if (foo()) { break; } }",
            "<?php while (1) { if (foo()) { return 2; } }",
            "<?php function f(): int { while (true) { if (foo()) { return 1; } } }",
            "<?php while (true) { if (foo()) { throw new \\Exception('x'); } }",
            // break 2 from a nested loop exits the outer one.
            "<?php while (true) { foreach ($xs as $x) { break 2; } }",
        ] {
            assert!(
                codes(src, run_while_condition).is_empty(),
                "should be clean: {src}"
            );
        }
        // A break that only exits a NESTED construct doesn't make ours exit.
        assert_eq!(
            codes(
                "<?php while (true) { foreach ($xs as $x) { break; } }",
                run_while_condition
            ),
            ["while.alwaysTrue"]
        );
    }

    #[test]
    fn while_on_call_is_clean() {
        assert!(codes("<?php while (foo()) { echo 1; }", run_while_condition).is_empty());
    }

    #[test]
    fn do_while_constant() {
        assert_eq!(
            codes(
                "<?php do { echo 1; } while (false);",
                run_do_while_condition
            ),
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
        assert_eq!(
            codes("<?php $x = !true;", run_boolean_not),
            ["booleanNot.alwaysFalse"]
        );
        assert_eq!(
            codes("<?php $x = !false;", run_boolean_not),
            ["booleanNot.alwaysTrue"]
        );
    }

    #[test]
    fn boolean_not_on_call_is_clean() {
        assert!(codes("<?php $x = !foo();", run_boolean_not).is_empty());
    }

    // --- && / || / xor ---

    #[test]
    fn boolean_and_sides() {
        // Left literal-true, right a call (unknown): only the left fires.
        assert_eq!(
            codes("<?php $x = true && foo();", run_boolean_and),
            ["booleanAnd.leftAlwaysTrue"]
        );
        assert_eq!(
            codes("<?php $x = foo() && false;", run_boolean_and),
            ["booleanAnd.rightAlwaysFalse"]
        );
    }

    #[test]
    fn boolean_or_sides() {
        assert_eq!(
            codes("<?php $x = false || foo();", run_boolean_or),
            ["booleanOr.leftAlwaysFalse"]
        );
        assert_eq!(
            codes("<?php $x = foo() || true;", run_boolean_or),
            ["booleanOr.rightAlwaysTrue"]
        );
    }

    #[test]
    fn logical_and_keyword() {
        assert_eq!(
            codes("<?php $x = true and foo();", run_boolean_and),
            ["booleanAnd.leftAlwaysTrue"]
        );
    }

    #[test]
    fn logical_xor_sides() {
        assert_eq!(
            codes("<?php $x = true xor foo();", run_logical_xor),
            ["logicalXor.leftAlwaysTrue"]
        );
        assert_eq!(
            codes("<?php $x = foo() xor false;", run_logical_xor),
            ["logicalXor.rightAlwaysFalse"]
        );
    }

    #[test]
    fn boolean_and_on_two_calls_is_clean() {
        assert!(codes("<?php $x = foo() && bar();", run_boolean_and).is_empty());
    }

    // --- strict comparison of disjoint types ---

    #[test]
    fn strict_identical_disjoint_scalars() {
        // int literal === string literal: provably different categories.
        assert_eq!(
            codes("<?php $x = (1 === 'a');", run_strict_comparison),
            ["identical.alwaysFalse"]
        );
    }

    #[test]
    fn strict_not_identical_disjoint_scalars_off_by_default() {
        // `!==` on disjoint types is always-true → off by default (phpstan).
        assert!(codes("<?php $x = (1 !== 'a');", run_strict_comparison).is_empty());
    }

    #[test]
    fn strict_disjoint_via_typed_params() {
        let src = "<?php function f(int $a, string $b) { return $a === $b; }";
        assert_eq!(codes(src, run_strict_comparison), ["identical.alwaysFalse"]);
    }

    #[test]
    fn strict_disjoint_honours_treat_phpdoc_types_as_certain() {
        // The operand's type comes only from PHPDoc — with
        // `treatPhpDocTypesAsCertain: false` the defensive runtime check is
        // not reported (phpstan parity); native disjointness still is.
        let doc_only = "<?php
            interface V {
                /** @return int */
                public function g();
            }
            function f(V $v): bool { $r = $v->g(); return false === $r; }";
        assert_eq!(
            codes(doc_only, run_strict_comparison),
            ["identical.alwaysFalse"]
        );
        assert!(codes_with(doc_only, run_strict_comparison, |fa| {
            fa.treat_phpdoc_types_as_certain = false;
        })
        .is_empty());

        // Natively provable: reported regardless of the option.
        let native = "<?php function f(int $a, string $b) { return $a === $b; }";
        assert_eq!(
            codes_with(native, run_strict_comparison, |fa| {
                fa.treat_phpdoc_types_as_certain = false;
            }),
            ["identical.alwaysFalse"]
        );
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
        assert_eq!(
            codes("<?php $x = (1 === 1);", run_strict_comparison),
            ["identical.alwaysTrue"]
        );
        assert_eq!(
            codes("<?php $x = (1 === 2);", run_strict_comparison),
            ["identical.alwaysFalse"]
        );
        assert_eq!(
            codes("<?php $x = (2 !== 2);", run_strict_comparison),
            ["notIdentical.alwaysFalse"]
        );
    }

    // --- constant loose / number comparison ---

    #[test]
    fn constant_loose_comparison_folds() {
        assert_eq!(
            codes("<?php $x = (1 == 1);", run_constant_comparison),
            ["equal.alwaysTrue"]
        );
        assert_eq!(
            codes("<?php $x = (1 != 1);", run_constant_comparison),
            ["notEqual.alwaysFalse"]
        );
    }

    #[test]
    fn constant_number_comparison_folds() {
        assert_eq!(
            codes("<?php $x = (5 > 3);", run_constant_comparison),
            ["greater.alwaysTrue"]
        );
        assert_eq!(
            codes("<?php $x = (2 <= 1);", run_constant_comparison),
            ["smallerOrEqual.alwaysFalse"]
        );
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

    // --- ConstantConditionInTraitRule ------------------------------------

    #[test]
    fn trait_context_self_constant_false_is_flagged() {
        let src = r#"<?php
            trait T { function m(): void { if (self::FLAG) {} } }
            class C { use T; private const FLAG = false; }"#;
        assert_eq!(
            codes(src, run_constant_condition_in_trait),
            ["if.alwaysFalse"]
        );
    }

    #[test]
    fn trait_context_different_consumer_values_are_suppressed() {
        let src = r#"<?php
            trait T { function m(): void { if (self::FLAG) {} } }
            class A { use T; private const FLAG = false; }
            class B { use T; private const FLAG = true; }"#;
        assert!(codes(src, run_constant_condition_in_trait).is_empty());
    }

    #[test]
    fn trait_context_this_instanceof_final_class_is_flagged_when_stable() {
        let src = r#"<?php
            final class C { use T; }
            trait T { function m(): void { if ($this instanceof D) {} } }
            final class D {}"#;
        assert_eq!(
            codes(src, run_constant_condition_in_trait),
            ["if.alwaysFalse"]
        );
    }

    #[test]
    fn trait_context_constant_condition_families_are_checked() {
        let src = r#"<?php
            trait T {
                function m(): void {
                    $a = self::FLAG ? 1 : 2;
                    $b = !self::FLAG;
                    $c = self::FLAG && foo();
                    while (self::FLAG) {}
                    do {} while (self::FLAG);
                    $d = self::N === 1;
                    $e = self::N < 2;
                    $f = match (self::N) { 1 => 'one', 2 => 'two' };
                }
            }
            class C {
                use T;
                private const FLAG = false;
                private const N = 1;
            }"#;
        assert_eq!(
            codes(src, run_constant_condition_in_trait),
            [
                "ternary.alwaysFalse",
                "booleanNot.alwaysTrue",
                "booleanAnd.leftAlwaysFalse",
                "while.alwaysFalse",
                "doWhile.alwaysFalse",
                "identical.alwaysTrue",
                "smaller.alwaysTrue",
                "match.alwaysTrue",
            ]
        );
    }
}
