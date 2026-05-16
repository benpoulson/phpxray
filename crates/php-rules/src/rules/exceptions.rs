//! phpstan category **Exceptions** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Exceptions/`.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented here:
//! - **ThrowExprTypeRule** (`throw.notThrowable`, level 3) — `throw <expr>` whose
//!   type is a *definite* non-`Throwable` (a scalar / array, or a fully-known
//!   user class whose entire ancestry is indexed and contains no `Throwable`).
//! - **CaughtExceptionExistenceRule** (`catch.notThrowable`, level 0) — `catch`
//!   of a known, fully-indexed class that is not a `Throwable`. (The
//!   `class.notFound` half of phpstan's rule is covered by `unknown-symbol`.)
//! - **OverwrittenExitPointByFinallyRule** (`finally.exitPoint`, level 4) — a
//!   `return`/`throw`/`break`/`continue` exit point in a `try`/`catch` body that
//!   is overwritten by another exit point in the `finally` block.
//!
//! Deferred (need analysis we don't model):
//! - `CatchWithUnthrownExceptionRule` (`catch.alreadyCaught`/`catch.neverThrown`)
//!   — needs throw-set analysis of the try block + checked-exception config.
//! - `NoncapturingCatchRule` / `ThrowExpressionRule` — pure PHP-version gates
//!   (8.0+ features); we target 8.6, so they are always clean.
//! - `MissingCheckedExceptionInThrows*` / `ThrowsVoid*` / `TooWide*ThrowType*` /
//!   `MethodThrowTypeCovarianceRule` — need a `@throws` throw-point analysis we
//!   don't have.

#![allow(unused_imports)]
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{Catch, Expr, ExprKind, Name, Stmt, StmtKind};
use php_diagnostics::Diagnostic;
use php_reflect::ReflectionIndex;
use php_resolve::{for_each_region, Resolution, Scope};
use php_span::Span;
use php_types::Type;

/// The reserved built-in throwable roots. These live in C and are *not* in the
/// reflection index, so any user class extending one has an unindexed ancestor
/// (see [`FileAnalysis::class_fully_known`]) — which is exactly why we only flag a
/// *fully-known* class as a non-throwable: an unknown ancestor could be one of
/// these.
fn is_throwable_name(fqn: &str) -> bool {
    let bare = fqn.trim_start_matches('\\');
    bare.eq_ignore_ascii_case("Throwable")
        || bare.eq_ignore_ascii_case("Exception")
        || bare.eq_ignore_ascii_case("Error")
}

/// Whether `fqn` is, transitively, a `Throwable` according to the reflection
/// index: it (or any ancestor) is named `Throwable`/`Exception`/`Error`, or it
/// extends/implements one of them. Cycle/diamond tolerant.
fn is_throwable_class(refl: &ReflectionIndex, fqn: &str) -> bool {
    fn walk(refl: &ReflectionIndex, fqn: &str, seen: &mut Vec<String>) -> bool {
        if is_throwable_name(fqn) {
            return true;
        }
        let key = fqn.trim_start_matches('\\').to_ascii_lowercase();
        if seen.contains(&key) {
            return false;
        }
        seen.push(key);
        let Some(c) = refl.class(fqn) else { return false };
        c.parents.iter().chain(&c.interfaces).any(|t| match t {
            Type::Named { fqn, .. } => walk(refl, fqn, seen),
            _ => false,
        })
    }
    walk(refl, fqn, &mut Vec::new())
}

// ---------------------------------------------------------------------------
// ThrowExprTypeRule — `throw <expr>` of a non-Throwable
// ---------------------------------------------------------------------------

fn run_throw_expr_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    // Resolve `new X` class names per region scope; everything else via the type
    // map. We walk regions so a `throw new X` operand's name resolves correctly.
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            // Walk every expression in the statement (crossing closure/function
            // boundaries — `throw new X` resolves by name regardless of scope).
            walk::for_each_expr(&php_ast::Program { stmts: vec![st.clone()] }, &mut |e| {
                let ExprKind::Throw(inner) = &e.kind else { return };
                if let Some(d) = check_thrown(fa, scope, inner) {
                    out.push(d);
                }
            });
        }
    });
    out
}

/// Return a diagnostic iff `inner` is a *definite* non-`Throwable`.
fn check_thrown(fa: &FileAnalysis, scope: &Scope, inner: &Expr) -> Option<Diagnostic> {
    // `throw new X` — resolve the class name directly (more precise than the type
    // map, and works before flow inference).
    if let ExprKind::New { class, .. } = &inner.kind {
        if let ExprKind::Name(name) = &class.kind {
            let Resolution::Fqn(fqn) = scope.resolve_class(name) else { return None };
            // Only flag a class whose *entire* ancestry is indexed (so an unknown
            // ancestor can't secretly be a Throwable) and which is not a Throwable.
            if fa.class_fully_known(&fqn) && !is_throwable_class(fa.reflection, &fqn) {
                let display = fqn.trim_start_matches('\\').to_string();
                return Some(
                    Diagnostic::error(inner.span, format!("Invalid type {display} to throw."))
                        .with_code("throw.notThrowable"),
                );
            }
        }
        return None;
    }

    // Syntactic literals are definite non-objects regardless of the type map
    // (which is opaque inside closures). `array(...)`/`[...]` likewise.
    let literal = match &inner.kind {
        ExprKind::Int(_) => Some("int"),
        ExprKind::Float(_) => Some("float"),
        ExprKind::Str(_) | ExprKind::Interpolated(_) => Some("string"),
        ExprKind::Array { .. } => Some("array"),
        _ => None,
    };
    if let Some(word) = literal {
        return Some(
            Diagnostic::error(inner.span, format!("Invalid type {word} to throw."))
                .with_code("throw.notThrowable"),
        );
    }

    // Otherwise consult the inferred type, and only flag *definite* non-objects.
    let ty = fa.type_of(inner);
    let bad = match &ty {
        Type::Int
        | Type::Float
        | Type::String
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Array(_)
        | Type::List(_)
        | Type::LiteralInt(_)
        | Type::LiteralString(_) => true,
        Type::Named { fqn, .. } => {
            fa.class_fully_known(fqn) && !is_throwable_class(fa.reflection, fqn)
        }
        _ => false,
    };
    if !bad {
        return None;
    }
    Some(
        Diagnostic::error(inner.span, format!("Invalid type {ty} to throw."))
            .with_code("throw.notThrowable"),
    )
}

// ---------------------------------------------------------------------------
// CaughtExceptionExistenceRule — `catch (NonThrowable $e)`
// ---------------------------------------------------------------------------

fn run_caught_exception(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            walk::for_each_stmt_in_stmt(st, &mut |s| {
                let StmtKind::Try { catches, .. } = &s.kind else { return };
                for c in catches {
                    for ty in &c.types {
                        check_caught(fa, scope, ty, &mut out);
                    }
                }
            });
        }
    });
    out
}

fn check_caught(fa: &FileAnalysis, scope: &Scope, ty: &Name, out: &mut Vec<Diagnostic>) {
    let Resolution::Fqn(fqn) = scope.resolve_class(ty) else { return };
    // Existence (`class.notFound`) is the unknown-symbol rule's job. Here we only
    // classify a *known* caught class. Only a fully-known class whose ancestry is
    // entirely indexed can be confidently declared a non-throwable (an unindexed
    // ancestor could be `Throwable`/`Exception`/`Error`). Interfaces are always
    // allowed as catch types in phpstan.
    let Some(cr) = fa.reflection.class(&fqn) else { return };
    if cr.kind == php_ast::ClassKind::Interface {
        return;
    }
    if !fa.class_fully_known(&fqn) {
        return;
    }
    if is_throwable_class(fa.reflection, &fqn) {
        return;
    }
    let display = fqn.trim_start_matches('\\').to_string();
    out.push(
        Diagnostic::error(ty.span, format!("Caught class {display} is not an exception."))
            .with_code("catch.notThrowable"),
    );
}

// ---------------------------------------------------------------------------
// OverwrittenExitPointByFinallyRule
// ---------------------------------------------------------------------------

/// A description of an exit-point statement (`return`/`throw`/`break`/`continue`)
/// kept alongside its span for the diagnostic.
struct ExitPoint {
    word: &'static str,
    span: Span,
}

/// Collect the exit points that appear *directly* in a statement list, without
/// descending into nested function bodies, classes, or further `try` constructs
/// (a nested `try`/`finally` owns its own analysis). We do descend into plain
/// control flow (`if`/loops/switch/blocks) since those exit points still escape
/// the enclosing try/finally.
fn collect_exit_points(stmts: &[Stmt], out: &mut Vec<ExitPoint>) {
    for st in stmts {
        collect_exit_points_one(st, out);
    }
}

fn collect_exit_points_one(st: &Stmt, out: &mut Vec<ExitPoint>) {
    match &st.kind {
        StmtKind::Return(_) => out.push(ExitPoint { word: "return", span: st.span }),
        StmtKind::Break(_) => out.push(ExitPoint { word: "break", span: st.span }),
        StmtKind::Continue(_) => out.push(ExitPoint { word: "continue", span: st.span }),
        StmtKind::Expr(e) if matches!(e.kind, ExprKind::Throw(_)) => {
            out.push(ExitPoint { word: "throw", span: st.span })
        }
        StmtKind::Block(b) => collect_exit_points(b, out),
        StmtKind::If { then, elseifs, els, .. } => {
            collect_exit_points_one(then, out);
            for e in elseifs {
                collect_exit_points_one(&e.body, out);
            }
            if let Some(e) = els {
                collect_exit_points_one(e, out);
            }
        }
        StmtKind::While { body, .. } | StmtKind::DoWhile { body, .. } => {
            collect_exit_points_one(body, out)
        }
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                collect_exit_points(&c.body, out);
            }
        }
        // `for`/`foreach` bodies host loop-local break/continue that don't escape
        // the try; a `return`/`throw` there is too noisy to attribute, so we skip
        // loop bodies entirely (phpstan tracks real exit points via its CFG; we
        // stay conservative / FP-safe).
        _ => {}
    }
}

fn run_overwritten_finally(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        let StmtKind::Try { body, catches, finally } = &s.kind else { return };
        let Some(finally) = finally else { return };

        // Exit points in the finally block that overwrite the try/catch ones.
        let mut finally_exits = Vec::new();
        collect_exit_points(finally, &mut finally_exits);
        if finally_exits.is_empty() {
            return;
        }

        // Exit points in the try body + each catch body.
        let mut try_exits = Vec::new();
        collect_exit_points(body, &mut try_exits);
        for c in catches {
            collect_exit_points(&c.body, &mut try_exits);
        }
        if try_exits.is_empty() {
            return;
        }

        for ep in &try_exits {
            out.push(
                Diagnostic::error(
                    ep.span,
                    format!(
                        "This {} is overwritten by a different one in the finally block below.",
                        ep.word
                    ),
                )
                .with_code("finally.exitPoint"),
            );
        }
        for ep in &finally_exits {
            out.push(
                Diagnostic::error(
                    ep.span,
                    format!("The overwriting {} is on this line.", ep.word),
                )
                .with_code("finally.exitPoint"),
            );
        }
    });
    out
}

// ---------------------------------------------------------------------------
// CatchWithUnthrownExceptionRule — `catch.alreadyCaught` (the structural half)
// ---------------------------------------------------------------------------

/// phpstan's `CatchWithUnthrownExceptionRule` reports `catch.alreadyCaught` when a
/// `catch` is dead because every type it names is already covered by an earlier
/// `catch` in the same `try` (the caught type subtracts down to `never`). We model
/// exactly that structural case — a later catch type that is the *same as*, or a
/// subclass/implementor of, a type caught above. The other half (`catch.neverThrown`)
/// needs throw-set analysis of the try body and stays deferred.
///
/// FP-safe: [`ReflectionIndex::is_subclass_of`] is reflexive on the resolved FQN
/// (so identical catches are caught regardless of indexing) but only reports a real
/// subclass link when the class is indexed — an unindexed/built-in hierarchy yields
/// `false`, i.e. we under-report rather than guess.
fn run_dead_catch(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            walk::for_each_stmt_in_stmt(st, &mut |s| {
                let StmtKind::Try { catches, .. } = &s.kind else { return };
                check_dead_catches(fa, scope, catches, &mut out);
            });
        }
    });
    out
}

fn check_dead_catches(fa: &FileAnalysis, scope: &Scope, catches: &[Catch], out: &mut Vec<Diagnostic>) {
    // FQNs (leading `\` stripped) caught by earlier `catch` blocks in this `try`.
    let mut seen: Vec<String> = Vec::new();
    for c in catches {
        let resolved: Vec<String> = c
            .types
            .iter()
            .filter_map(|t| match scope.resolve_class(t) {
                Resolution::Fqn(fqn) => Some(fqn.trim_start_matches('\\').to_string()),
                _ => None,
            })
            .collect();
        // Only flag when *every* written type resolved AND each is already caught
        // above (so the whole caught type is dead). A partially-covered union
        // (`A|B` with only `A` caught) is live → no report.
        let all_covered = resolved.len() == c.types.len()
            && !resolved.is_empty()
            && resolved.iter().all(|ty| seen.iter().any(|prev| fa.reflection.is_subclass_of(ty, prev)));
        if all_covered {
            let display = resolved.join("|");
            let span = c.types.first().unwrap().span.to(c.types.last().unwrap().span);
            out.push(
                Diagnostic::error(span, format!("Dead catch - {display} is already caught above."))
                    .with_code("catch.alreadyCaught"),
            );
        }
        seen.extend(resolved);
    }
}

// ---------------------------------------------------------------------------
// NoncapturingCatchRule / ThrowExpressionRule — PHP-version gated (< 8.0)
// ---------------------------------------------------------------------------

/// `catch (X)` without a captured variable is only valid on PHP 8.0+. Gated on
/// `fa.php_version` (default 8.4 → silent); fires when a project pins PHP < 8.0.
fn run_noncapturing_catch(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if fa.php_version.at_least(80000) {
        return Vec::new();
    }
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        let StmtKind::Try { catches, .. } = &s.kind else { return };
        for c in catches {
            if c.var.is_none() {
                if let Some(t) = c.types.first() {
                    out.push(
                        Diagnostic::error(
                            t.span,
                            "Non-capturing catch is supported only on PHP 8.0 and later."
                                .to_string(),
                        )
                        .with_code("catch.nonCapturingNotSupported"),
                    );
                }
            }
        }
    });
    out
}

/// `throw` used as an *expression* (anywhere other than a standalone `throw …;`
/// statement) is only valid on PHP 8.0+. A standalone throw — the direct
/// expression of an expression statement — is fine at every version (mirrors
/// phpstan's `StandaloneThrowExprVisitor`). Gated on `fa.php_version`.
fn run_throw_expression(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if fa.php_version.at_least(80000) {
        return Vec::new();
    }
    // Spans of throws that sit directly as an expression statement (`throw X;`).
    let mut standalone: std::collections::HashSet<(u32, u32)> = std::collections::HashSet::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::Expr(e) = &s.kind {
            if matches!(e.kind, ExprKind::Throw(_)) {
                let r = e.span.range();
                standalone.insert((r.start as u32, r.end as u32));
            }
        }
    });
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        if !matches!(e.kind, ExprKind::Throw(_)) {
            return;
        }
        let r = e.span.range();
        if standalone.contains(&(r.start as u32, r.end as u32)) {
            return;
        }
        out.push(
            Diagnostic::error(
                e.span,
                "Throw expression is supported only on PHP 8.0 and later.".to_string(),
            )
            .with_code("throw.notSupported"),
        );
    });
    out
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "throw.notThrowable", level: 3, run: run_throw_expr_type },
    RuleEntry { name: "catch.notThrowable", level: 0, run: run_caught_exception },
    RuleEntry { name: "finally.exitPoint", level: 4, run: run_overwritten_finally },
    RuleEntry { name: "catch.alreadyCaught", level: 4, run: run_dead_catch },
    RuleEntry { name: "catch.nonCapturingNotSupported", level: 0, run: run_noncapturing_catch },
    RuleEntry { name: "throw.notSupported", level: 0, run: run_throw_expression },
];

#[cfg(test)]
mod tests {
    use crate::testutil::{codes, codes_version};
    use crate::PhpVersion;

    use super::*;

    // --- ThrowExprTypeRule ---

    #[test]
    fn throw_scalar_is_flagged() {
        let src = r#"<?php function f() { throw 5; }"#;
        assert_eq!(codes(src, run_throw_expr_type), ["throw.notThrowable"]);
    }

    #[test]
    fn throw_string_var_is_flagged() {
        let src = r#"<?php function f() { $s = "boom"; throw $s; }"#;
        assert_eq!(codes(src, run_throw_expr_type), ["throw.notThrowable"]);
    }

    #[test]
    fn throw_non_throwable_class_is_flagged() {
        // A fully-known user class with no Throwable ancestor.
        let src = r#"<?php class Plain {} function f() { throw new Plain(); }"#;
        assert_eq!(codes(src, run_throw_expr_type), ["throw.notThrowable"]);
    }

    #[test]
    fn throw_class_extending_builtin_exception_is_ok() {
        // `MyExc` extends the built-in `Exception` (unindexed) → not fully known →
        // never flagged (FP-safe).
        let src = r#"<?php class MyExc extends Exception {} function f() { throw new MyExc(); }"#;
        assert!(codes(src, run_throw_expr_type).is_empty());
    }

    #[test]
    fn throw_builtin_exception_is_ok() {
        let src = r#"<?php function f() { throw new Exception("x"); }"#;
        assert!(codes(src, run_throw_expr_type).is_empty());
    }

    #[test]
    fn throw_unknown_variable_is_ok() {
        let src = r#"<?php function f($e) { throw $e; }"#;
        assert!(codes(src, run_throw_expr_type).is_empty());
    }

    #[test]
    fn nested_throw_in_closure_is_flagged() {
        let src = r#"<?php $f = function () { throw 1; };"#;
        assert_eq!(codes(src, run_throw_expr_type), ["throw.notThrowable"]);
    }

    // --- CaughtExceptionExistenceRule ---

    #[test]
    fn catch_non_throwable_class_is_flagged() {
        let src = r#"<?php class Plain {} function f() { try {} catch (Plain $e) {} }"#;
        assert_eq!(codes(src, run_caught_exception), ["catch.notThrowable"]);
    }

    #[test]
    fn catch_class_extending_builtin_is_ok() {
        let src = r#"<?php class MyExc extends Exception {} function f() { try {} catch (MyExc $e) {} }"#;
        assert!(codes(src, run_caught_exception).is_empty());
    }

    #[test]
    fn catch_builtin_exception_is_ok() {
        let src = r#"<?php function f() { try {} catch (Exception $e) {} }"#;
        assert!(codes(src, run_caught_exception).is_empty());
    }

    #[test]
    fn catch_unknown_class_is_not_flagged_here() {
        // Existence is `unknown-symbol`'s job; this rule stays silent.
        let src = r#"<?php function f() { try {} catch (TotallyMadeUp $e) {} }"#;
        assert!(codes(src, run_caught_exception).is_empty());
    }

    // --- OverwrittenExitPointByFinallyRule ---

    #[test]
    fn return_overwritten_by_finally_return_is_flagged() {
        let src = r#"<?php function f() { try { return 1; } finally { return 2; } }"#;
        let c = codes(src, run_overwritten_finally);
        assert_eq!(c, ["finally.exitPoint", "finally.exitPoint"]);
    }

    #[test]
    fn finally_without_exit_point_is_ok() {
        let src = r#"<?php function f() { try { return 1; } finally { echo "cleanup"; } }"#;
        assert!(codes(src, run_overwritten_finally).is_empty());
    }

    #[test]
    fn try_without_exit_point_is_ok() {
        let src = r#"<?php function f() { try { echo "x"; } finally { return 2; } }"#;
        assert!(codes(src, run_overwritten_finally).is_empty());
    }

    #[test]
    fn catch_body_return_overwritten_is_flagged() {
        let src = r#"<?php function f() { try { } catch (Exception $e) { return 1; } finally { return 2; } }"#;
        let c = codes(src, run_overwritten_finally);
        assert_eq!(c, ["finally.exitPoint", "finally.exitPoint"]);
    }

    #[test]
    fn no_finally_is_ok() {
        let src = r#"<?php function f() { try { return 1; } catch (Exception $e) {} }"#;
        assert!(codes(src, run_overwritten_finally).is_empty());
    }

    // --- CatchWithUnthrownExceptionRule (catch.alreadyCaught) ---

    #[test]
    fn duplicate_catch_class_is_dead() {
        let src = r#"<?php
            class MyErr extends \Exception {}
            function f() { try {} catch (MyErr $e) {} catch (MyErr $e) {} }"#;
        assert_eq!(codes(src, run_dead_catch), ["catch.alreadyCaught"]);
    }

    #[test]
    fn subclass_caught_after_parent_is_dead() {
        // Catching the parent first makes the child catch dead.
        let src = r#"<?php
            class Base extends \Exception {}
            class Child extends Base {}
            function f() { try {} catch (Base $e) {} catch (Child $e) {} }"#;
        assert_eq!(codes(src, run_dead_catch), ["catch.alreadyCaught"]);
    }

    #[test]
    fn parent_after_child_is_live() {
        // Catching the child first does NOT make the parent catch dead.
        let src = r#"<?php
            class Base extends \Exception {}
            class Child extends Base {}
            function f() { try {} catch (Child $e) {} catch (Base $e) {} }"#;
        assert!(codes(src, run_dead_catch).is_empty());
    }

    #[test]
    fn distinct_catches_are_live() {
        let src = r#"<?php
            class A extends \Exception {}
            class B extends \Exception {}
            function f() { try {} catch (A $e) {} catch (B $e) {} }"#;
        assert!(codes(src, run_dead_catch).is_empty());
    }

    #[test]
    fn partially_covered_union_is_live() {
        // `A|C` where only `A` is caught above is still live (C may be thrown).
        let src = r#"<?php
            class A extends \Exception {}
            class C extends \Exception {}
            function f() { try {} catch (A $e) {} catch (A | C $e) {} }"#;
        assert!(codes(src, run_dead_catch).is_empty());
    }

    #[test]
    fn fully_covered_union_is_dead() {
        let src = r#"<?php
            class A extends \Exception {}
            class C extends \Exception {}
            function f() { try {} catch (A $e) {} catch (C $e) {} catch (A | C $e) {} }"#;
        assert_eq!(codes(src, run_dead_catch), ["catch.alreadyCaught"]);
    }

    #[test]
    fn unindexed_hierarchy_is_not_guessed() {
        // Built-in SPL hierarchy isn't indexed → no subclass link proven → no
        // report (under-report rather than risk a false positive).
        let src = r#"<?php
            function f() { try {} catch (\Exception $e) {} catch (\RuntimeException $e) {} }"#;
        assert!(codes(src, run_dead_catch).is_empty());
    }

    // --- NoncapturingCatchRule (version-gated) ---

    #[test]
    fn noncapturing_catch_flagged_below_php80() {
        let src = r#"<?php function f() { try {} catch (\Exception) {} }"#;
        assert_eq!(
            codes_version(src, run_noncapturing_catch, PhpVersion::parse("7.4").unwrap()),
            ["catch.nonCapturingNotSupported"]
        );
    }

    #[test]
    fn noncapturing_catch_ok_on_php80_plus() {
        let src = r#"<?php function f() { try {} catch (\Exception) {} }"#;
        assert!(codes(src, run_noncapturing_catch).is_empty()); // default 8.4
        // A capturing catch is fine even below 8.0.
        let cap = r#"<?php function f() { try {} catch (\Exception $e) {} }"#;
        assert!(codes_version(cap, run_noncapturing_catch, PhpVersion::parse("7.4").unwrap()).is_empty());
    }

    // --- ThrowExpressionRule (version-gated) ---

    #[test]
    fn throw_expression_flagged_below_php80() {
        let src = r#"<?php function f($x) { $y = $x ?? throw new \Exception(); }"#;
        assert_eq!(
            codes_version(src, run_throw_expression, PhpVersion::parse("7.4").unwrap()),
            ["throw.notSupported"]
        );
    }

    #[test]
    fn standalone_throw_is_ok_below_php80() {
        let src = r#"<?php function f() { throw new \Exception(); }"#;
        assert!(codes_version(src, run_throw_expression, PhpVersion::parse("7.4").unwrap()).is_empty());
    }

    #[test]
    fn throw_expression_ok_on_php80_plus() {
        let src = r#"<?php function f($x) { $y = $x ?? throw new \Exception(); }"#;
        assert!(codes(src, run_throw_expression).is_empty()); // default 8.4
    }
}
