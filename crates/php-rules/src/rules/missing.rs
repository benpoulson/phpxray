//! phpstan category **Missing** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Missing/` — 1 rule(s) at level(s) 0.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented (level 0):
//! - `return.missing` (`MissingReturnRule`) — a function/method with a **native**
//!   return typehint that is not `void`/`never`/`mixed`, is not a generator
//!   (`yield`), and whose body can reach the end without a `return` statement.
//!
//! This is the *conservative, native-only* slice of phpstan's rule (its default
//! config has `checkPhpDocMissingReturn=false`/`checkExplicitMixedMissingReturn=
//! false`, so it only fires on native typehints). Zero false positives is the
//! priority: the reachability analysis errs toward "always terminates" whenever
//! control flow is hard to prove (loops it can't bound, `goto`, `match`
//! statements, dynamic flow). We flag only when there is a *clearly* missing
//! return.

#![allow(unused_imports)]
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{
    ClassDecl, ClosureExpr, Expr, ExprKind, FunctionDecl, Member, MethodDecl, Stmt, StmtKind, Type,
    TypeKind,
};
use php_diagnostics::Diagnostic;
use php_intern::Interner;
use php_span::Span;

/// A function/method whose declared native return type means a value MUST be
/// produced — i.e. not `void`/`never`/`mixed`. Returns the displayed type for
/// the message, or `None` when the rule should not apply.
fn checkable_return(rt: &Option<Type>) -> Option<String> {
    let ty = rt.as_ref()?;
    if let Some(name) = single_keyword(ty) {
        // `void`/`never`/`mixed` standalone: nothing to require.
        if matches!(name.as_str(), "void" | "never" | "mixed") {
            return None;
        }
    }
    Some(render_type(ty))
}

/// The lowercased keyword if `ty` is a single bare name; else `None`.
fn single_keyword(ty: &Type) -> Option<String> {
    if let TypeKind::Simple(name) = &ty.kind {
        return Some(name.text.to_ascii_lowercase());
    }
    None
}

/// A best-effort textual rendering of a native type for the diagnostic message.
fn render_type(ty: &Type) -> String {
    match &ty.kind {
        TypeKind::Simple(name) => name.text.clone(),
        TypeKind::Nullable(inner) => format!("?{}", render_type(inner)),
        TypeKind::Union(parts) => parts.iter().map(render_type).collect::<Vec<_>>().join("|"),
        TypeKind::Intersection(parts) => {
            parts.iter().map(render_type).collect::<Vec<_>>().join("&")
        }
    }
}

// ---------------------------------------------------------------------------
// Generator detection: a body containing `yield`/`yield from` is a generator,
// for which a missing `return` is fine (phpstan's default config skips it).
// ---------------------------------------------------------------------------

/// Whether the statement list (this scope only — NOT nested functions/closures)
/// contains a `yield` or `yield from`.
fn contains_yield(stmts: &[Stmt]) -> bool {
    let mut found = false;
    for st in stmts {
        // Only descend within this scope; a nested closure's yield doesn't make
        // the outer function a generator.
        walk::for_each_expr_in_scope(st, &mut |e| {
            if matches!(e.kind, ExprKind::Yield { .. } | ExprKind::YieldFrom(_)) {
                found = true;
            }
        });
        if found {
            break;
        }
    }
    found
}

// ---------------------------------------------------------------------------
// Reachability: does a statement list ALWAYS terminate (return/throw/exit/…)?
// Conservative — returns `true` (terminates ⇒ no missing-return flag) whenever
// control flow can't be proven to fall through. The ONLY way we emit a
// diagnostic is when we can prove the end is reachable, so over-estimating
// termination is the FP-safe direction.
// ---------------------------------------------------------------------------

/// Whether executing `stmts` (in order) always ends control flow before falling
/// off the end.
fn always_terminates(fa: &FileAnalysis, stmts: &[Stmt]) -> bool {
    for st in stmts {
        if stmt_terminates(fa, st) {
            return true;
        }
    }
    false
}

/// Whether a single statement unconditionally ends control flow.
fn stmt_terminates(fa: &FileAnalysis, st: &Stmt) -> bool {
    match &st.kind {
        StmtKind::Return(_) => true,
        StmtKind::Expr(e) => expr_terminates(fa, e),
        // `goto` jumps somewhere we don't track — assume it terminates this path
        // (FP-safe: prevents a false "missing return").
        StmtKind::Goto(_) => true,
        StmtKind::Block(b) => always_terminates(fa, b),
        StmtKind::If {
            cond: _,
            then,
            elseifs,
            els,
        } => {
            // Only terminating when there's a final `else` AND every branch
            // (then / each elseif / else) terminates.
            let Some(els) = els else { return false };
            if !stmt_terminates(fa, then) {
                return false;
            }
            for ei in elseifs {
                if !stmt_terminates(fa, &ei.body) {
                    return false;
                }
            }
            stmt_terminates(fa, els)
        }
        StmtKind::Switch { cases, .. } => switch_terminates(fa, cases),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            // If `finally` always terminates, the whole try does.
            if let Some(fin) = finally {
                if always_terminates(fa, fin) {
                    return true;
                }
            }
            // Otherwise: the protected body and every catch must terminate.
            if !always_terminates(fa, body) {
                return false;
            }
            catches.iter().all(|c| always_terminates(fa, &c.body))
        }
        // An infinite loop with no `break` never falls through.
        StmtKind::While { cond, body } => is_truthy(cond) && !contains_break(body),
        StmtKind::DoWhile { cond, body } => is_truthy(cond) && !contains_break(body),
        StmtKind::For { cond, body, .. } => {
            // `for (;;)` / `for (; true; )` with no break.
            (cond.is_empty() || cond.last().map(is_truthy).unwrap_or(false))
                && !contains_break(body)
        }
        _ => false,
    }
}

/// Whether an expression-statement unconditionally ends control flow.
///
/// - `throw …;` / `exit(…)` / `die(…)` always terminate.
/// - A *call* is treated as terminating when its resolved return type is `never`
///   (so we don't false-flag `function f(): int { fail(); }` where
///   `fail(): never`) **or** when we couldn't resolve it (`mixed`/`unknown`):
///   in that case we cannot prove the call returns, so — to guarantee zero false
///   positives — we assume it might not fall through. This means a trailing call
///   only contributes to a missing-return finding when we *positively* resolved a
///   non-`never` return type for it (the common, confident case).
fn expr_terminates(fa: &FileAnalysis, e: &Expr) -> bool {
    if matches!(e.kind, ExprKind::Throw(_) | ExprKind::Exit(_)) {
        return true;
    }
    if matches!(
        e.kind,
        ExprKind::Call { .. } | ExprKind::MethodCall { .. } | ExprKind::StaticCall { .. }
    ) {
        return matches!(
            fa.type_of(e),
            php_types::Type::Never
                | php_types::Type::Mixed
                | php_types::Type::ExplicitMixed
                | php_types::Type::Unknown(_)
        );
    }
    false
}

/// A `switch` terminates only when it has a `default` case AND every case body
/// terminates. PHP cases fall through, so an empty case body inherits the next
/// case's termination; to stay conservative we require *each* case (in order,
/// accounting for fall-through) to ultimately reach a terminator.
fn switch_terminates(fa: &FileAnalysis, cases: &[php_ast::SwitchCase]) -> bool {
    let has_default = cases.iter().any(|c| c.test.is_none());
    if !has_default {
        return false;
    }
    // Walk cases; a case that falls through (empty/non-terminating body) must be
    // covered by a later case that terminates.
    for (i, c) in cases.iter().enumerate() {
        if always_terminates(fa, &c.body) {
            continue;
        }
        // Non-terminating body: only OK if it falls through (no break/continue)
        // into a successor that eventually terminates.
        if contains_break(&wrap(&c.body)) {
            return false;
        }
        // Falls through: a later case must terminate.
        let later_terminates = cases[i + 1..]
            .iter()
            .any(|n| always_terminates(fa, &n.body));
        if !later_terminates {
            return false;
        }
    }
    true
}

/// Helper: wrap a slice into a single synthetic block statement so the shared
/// break scanner can be reused on a `Vec<Stmt>` slice.
fn wrap(stmts: &[Stmt]) -> Stmt {
    Stmt::new(Span::new(0, 0), StmtKind::Block(stmts.to_vec()))
}

/// Whether `body` contains a `break`/`continue` that could escape the enclosing
/// loop (so an otherwise-infinite loop might fall through). Conservative: any
/// `break`/`continue` at all (even nested) counts — over-counting only makes us
/// classify a loop as *non*-terminating, which avoids the loop suppressing a
/// genuine missing return; but since a loop only *suppresses* a flag when it's
/// infinite, over-counting `break` here can never cause a false positive on the
/// loop itself (a loop that isn't proven infinite is simply not a terminator).
///
/// Important FP note: we must NOT descend into nested loops/switches for `break`
/// (a `break` there targets the inner construct). We approximate by scanning
/// only the direct statement tree but stopping at nested loop/switch bodies.
fn contains_break(body: &Stmt) -> bool {
    let mut found = false;
    scan_break(body, &mut found);
    found
}

fn scan_break(st: &Stmt, found: &mut bool) {
    if *found {
        return;
    }
    match &st.kind {
        StmtKind::Break(_) | StmtKind::Continue(_) => *found = true,
        StmtKind::Block(b) => b.iter().for_each(|s| scan_break(s, found)),
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            scan_break(then, found);
            for ei in elseifs {
                scan_break(&ei.body, found);
            }
            if let Some(e) = els {
                scan_break(e, found);
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter().for_each(|s| scan_break(s, found));
            for c in catches {
                c.body.iter().for_each(|s| scan_break(s, found));
            }
            if let Some(f) = finally {
                f.iter().for_each(|s| scan_break(s, found));
            }
        }
        StmtKind::Declare { body: Some(b), .. } => scan_break(b, found),
        // Nested loops/switches capture their own break/continue — do not descend.
        StmtKind::While { .. }
        | StmtKind::DoWhile { .. }
        | StmtKind::For { .. }
        | StmtKind::Foreach { .. }
        | StmtKind::Switch { .. } => {}
        _ => {}
    }
}

/// Whether `cond` is a literal `true` (the common `while (true)` idiom). `true`
/// is lexed as a bare name in this AST.
fn is_truthy(cond: &Expr) -> bool {
    match &cond.kind {
        ExprKind::Name(n) => n.text.eq_ignore_ascii_case("true"),
        // `while (1)` is a common infinite-loop idiom.
        ExprKind::Int(n) => *n != 0,
        ExprKind::Paren(inner) => is_truthy(inner),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// The rule
// ---------------------------------------------------------------------------

fn check_body(
    fa: &FileAnalysis,
    label: &str,
    span: Span,
    body: &[Stmt],
    rt: &Option<Type>,
    out: &mut Vec<Diagnostic>,
) {
    let Some(type_str) = checkable_return(rt) else {
        return;
    };
    // Generators are exempt.
    if contains_yield(body) {
        return;
    }
    if always_terminates(fa, body) {
        return;
    }
    // phpstan can prove some loops always execute (a non-empty array `foreach`,
    // etc.) and thus always hit a `return` inside them; we don't track
    // non-emptiness, so to stay false-positive-free we don't report a missing
    // return when a value-return lives inside a loop.
    if has_return_in_loop(body) {
        return;
    }
    out.push(
        Diagnostic::error(
            span,
            format!("{label} should return {type_str} but return statement is missing."),
        )
        .with_code("return.missing"),
    );
}

/// Whether any `return <expr>` appears inside a loop body in `stmts` (not
/// crossing into nested function/closure scopes).
fn has_return_in_loop(stmts: &[Stmt]) -> bool {
    fn walk(s: &Stmt, in_loop: bool) -> bool {
        match &s.kind {
            StmtKind::Return(Some(_)) => in_loop,
            StmtKind::While { body, .. }
            | StmtKind::DoWhile { body, .. }
            | StmtKind::For { body, .. }
            | StmtKind::Foreach { body, .. } => walk(body, true),
            StmtKind::Block(b) => b.iter().any(|s| walk(s, in_loop)),
            StmtKind::If {
                then, elseifs, els, ..
            } => {
                walk(then, in_loop)
                    || elseifs.iter().any(|ei| walk(&ei.body, in_loop))
                    || els.as_ref().is_some_and(|e| walk(e, in_loop))
            }
            StmtKind::Switch { cases, .. } => cases
                .iter()
                .any(|c| c.body.iter().any(|s| walk(s, in_loop))),
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                body.iter().any(|s| walk(s, in_loop))
                    || catches
                        .iter()
                        .any(|c| c.body.iter().any(|s| walk(s, in_loop)))
                    || finally
                        .as_ref()
                        .is_some_and(|f| f.iter().any(|s| walk(s, in_loop)))
            }
            StmtKind::Declare { body: Some(b), .. } => walk(b, in_loop),
            _ => false,
        }
    }
    stmts.iter().any(|s| walk(s, false))
}

fn run_missing_return(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let interner = fa.interner;

    // Named functions and class methods (incl. nested decls — `for_each_stmt`
    // visits every statement). Anonymous classes are handled in the expr walk.
    walk::for_each_stmt(fa.program, &mut |s| match &s.kind {
        StmtKind::Function(f) => {
            let label = format!("Function {}()", interner.resolve(f.name));
            check_body(fa, &label, f.name_span, &f.body, &f.return_type, &mut out);
        }
        StmtKind::Class(c) => check_class_methods(fa, c, interner, &mut out),
        _ => {}
    });

    // Closures and anonymous-class methods (expression position).
    walk::for_each_expr(fa.program, &mut |e| match &e.kind {
        ExprKind::Closure(c) => {
            check_body(
                fa,
                "Anonymous function",
                e.span,
                &c.body,
                &c.return_type,
                &mut out,
            );
        }
        ExprKind::NewAnon { class, .. } => check_class_methods(fa, class, interner, &mut out),
        // Arrow functions always have an expression body that yields a value —
        // never a missing return.
        _ => {}
    });

    out
}

fn check_class_methods(
    fa: &FileAnalysis,
    c: &ClassDecl,
    interner: &Interner,
    out: &mut Vec<Diagnostic>,
) {
    let class_name = c
        .name
        .map(|n| interner.resolve(n).to_string())
        .unwrap_or_else(|| "class@anonymous".to_string());
    for m in &c.members {
        let Member::Method(md) = m else { continue };
        // Abstract/interface methods have no body — nothing to check.
        let Some(body) = &md.body else { continue };
        let label = format!("Method {}::{}()", class_name, interner.resolve(md.name));
        check_body(fa, &label, md.name_span, body, &md.return_type, out);
    }
}

pub(crate) static RULES: &[RuleEntry] = &[RuleEntry {
    name: "missing.return",
    level: 0,
    run: run_missing_return,
}];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- positives -----------------------------------------------------------

    #[test]
    fn empty_body_with_return_type_is_flagged() {
        assert_eq!(
            codes("<?php function f(): int {}", run_missing_return),
            ["return.missing"]
        );
    }

    #[test]
    fn fallthrough_after_statement_is_flagged() {
        assert_eq!(
            codes("<?php function f(): int { $x = 1; }", run_missing_return),
            ["return.missing"]
        );
    }

    #[test]
    fn if_without_else_is_flagged() {
        assert_eq!(
            codes(
                "<?php function f(): int { if (cond()) { return 1; } }",
                run_missing_return
            ),
            ["return.missing"]
        );
    }

    #[test]
    fn method_missing_return_is_flagged() {
        assert_eq!(
            codes(
                "<?php class C { function m(): string { $x = 1; } }",
                run_missing_return
            ),
            ["return.missing"]
        );
    }

    #[test]
    fn nullable_return_missing_is_flagged() {
        assert_eq!(
            codes("<?php function f(): ?int { $x = 1; }", run_missing_return),
            ["return.missing"]
        );
    }

    #[test]
    fn switch_without_default_is_flagged() {
        assert_eq!(
            codes(
                "<?php function f($x): int { switch ($x) { case 1: return 1; } }",
                run_missing_return
            ),
            ["return.missing"]
        );
    }

    // --- negatives: declared type means no value required ---------------------

    #[test]
    fn void_return_is_ok() {
        assert!(codes("<?php function f(): void {}", run_missing_return).is_empty());
    }

    #[test]
    fn never_return_is_ok() {
        assert!(codes("<?php function f(): never {}", run_missing_return).is_empty());
    }

    #[test]
    fn mixed_return_is_ok() {
        assert!(codes("<?php function f(): mixed {}", run_missing_return).is_empty());
    }

    #[test]
    fn no_declared_return_is_ok() {
        assert!(codes("<?php function f() {}", run_missing_return).is_empty());
    }

    // --- negatives: body always terminates -----------------------------------

    #[test]
    fn always_returns_is_ok() {
        assert!(codes("<?php function f(): int { return 1; }", run_missing_return).is_empty());
    }

    #[test]
    fn always_throws_is_ok() {
        assert!(codes(
            "<?php function f(): int { throw new E(); }",
            run_missing_return
        )
        .is_empty());
    }

    #[test]
    fn exit_is_ok() {
        assert!(codes("<?php function f(): int { exit(1); }", run_missing_return).is_empty());
    }

    #[test]
    fn if_else_all_return_is_ok() {
        assert!(codes(
            "<?php function f($c): int { if ($c) { return 1; } else { return 2; } }",
            run_missing_return
        )
        .is_empty());
    }

    #[test]
    fn if_elseif_else_all_return_is_ok() {
        assert!(codes(
            "<?php function f($c): int { if ($c) { return 1; } elseif ($c) { return 2; } else { return 3; } }",
            run_missing_return
        )
        .is_empty());
    }

    #[test]
    fn switch_with_default_all_return_is_ok() {
        assert!(codes(
            "<?php function f($x): int { switch ($x) { case 1: return 1; default: return 0; } }",
            run_missing_return
        )
        .is_empty());
    }

    #[test]
    fn try_finally_returns_is_ok() {
        assert!(codes(
            "<?php function f(): int { try { foo(); } finally { return 1; } }",
            run_missing_return
        )
        .is_empty());
    }

    #[test]
    fn try_catch_all_return_is_ok() {
        assert!(codes(
            "<?php function f(): int { try { return 1; } catch (E $e) { return 2; } }",
            run_missing_return
        )
        .is_empty());
    }

    #[test]
    fn infinite_while_loop_is_ok() {
        assert!(codes(
            "<?php function f(): int { while (true) { doStuff(); } }",
            run_missing_return
        )
        .is_empty());
    }

    #[test]
    fn infinite_for_loop_is_ok() {
        assert!(codes(
            "<?php function f(): int { for (;;) { work(); } }",
            run_missing_return
        )
        .is_empty());
    }

    // --- negatives: generators & abstract -------------------------------------

    #[test]
    fn generator_is_ok() {
        assert!(codes(
            "<?php function f(): \\Generator { yield 1; }",
            run_missing_return
        )
        .is_empty());
    }

    #[test]
    fn yield_from_generator_is_ok() {
        assert!(codes(
            "<?php function f(): iterable { yield from g(); }",
            run_missing_return
        )
        .is_empty());
    }

    #[test]
    fn abstract_method_is_ok() {
        assert!(codes(
            "<?php abstract class C { abstract function m(): int; }",
            run_missing_return
        )
        .is_empty());
    }

    #[test]
    fn interface_method_is_ok() {
        assert!(codes(
            "<?php interface I { function m(): int; }",
            run_missing_return
        )
        .is_empty());
    }

    // --- closures & arrow fns -------------------------------------------------

    #[test]
    fn closure_missing_return_is_flagged() {
        assert_eq!(
            codes(
                "<?php $f = function (): int { $x = 1; };",
                run_missing_return
            ),
            ["return.missing"]
        );
    }

    #[test]
    fn closure_with_return_is_ok() {
        assert!(codes(
            "<?php $f = function (): int { return 1; };",
            run_missing_return
        )
        .is_empty());
    }

    #[test]
    fn arrow_fn_is_never_flagged() {
        assert!(codes("<?php $f = fn (): int => 1;", run_missing_return).is_empty());
    }

    #[test]
    fn nested_closure_yield_does_not_exempt_outer() {
        // The outer function is NOT a generator just because a nested closure
        // yields; it has a real fallthrough → flagged.
        assert_eq!(
            codes(
                "<?php function f(): int { $g = function () { yield 1; }; }",
                run_missing_return
            ),
            ["return.missing"]
        );
    }

    // --- anonymous class ------------------------------------------------------

    #[test]
    fn anon_class_method_missing_return_is_flagged() {
        assert_eq!(
            codes(
                "<?php $o = new class { function m(): int { $x = 1; } };",
                run_missing_return
            ),
            ["return.missing"]
        );
    }
}
