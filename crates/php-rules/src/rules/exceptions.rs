//! phpstan category **Exceptions** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Exceptions/`.
//! The rule set's coverage truth is `cargo run -p xtask -- rule-manifest`; for phpstan's behaviour read `phpstan-src/src/Rules/` directly. Add each rule as a `RuleEntry` to
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
//! - **CatchWithUnthrownExceptionRule** (`catch.alreadyCaught`, level 4) — the
//!   structural dead-catch half, when an earlier catch already covers a later
//!   one.
//! - **NoncapturingCatchRule** / **ThrowExpressionRule** — PHP-version gates that
//!   fire only for projects targeting PHP < 8.0.
//! - **ThrowsVoidFunctionWithExplicitThrowPointRule** / **ThrowsVoidMethodWithExplicitThrowPointRule**
//!   (`throws.void`, level 3) — a declaration with explicit `@throws void` and a
//!   direct `throw` expression in its body.
//! - **TooWide{Function,Method}ThrowTypeRule** (`throws.unusedType`, level 4) —
//!   a declared `@throws T` the body never throws. FP-safe subset: only explicit
//!   `throw` gives precise thrown types; any call/`new`/`clone`/`match`/`eval`/
//!   division is a "broad" source that suppresses the report (see the block
//!   above the rule). Validated against the phpstan oracle (byte-identical
//!   messages; we under-report only the built-in-specific throw cases phpstan
//!   models and we don't).
//!
//! Deferred (need analysis we don't model):
//! - `CatchWithUnthrownExceptionRule` (`catch.neverThrown`) — needs try-block
//!   throw-set analysis + the checked-exception config subsystem (default
//!   `reportUncheckedExceptionDeadCatch: false` + empty checked-class lists make
//!   it near-dormant by default, so low priority).
//! - `MissingCheckedExceptionInThrows*` / `MethodThrowTypeCovarianceRule` —
//!   need checked-exception config + interprocedural throw sets.
//! - `ThrowsVoidPropertyHookWithExplicitThrowPointRule` — property hooks don't
//!   carry their own docblocks in our AST yet, so we can't tell hook-level
//!   `@throws void` apart from a property docblock.

use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{
    BinOp, Catch, ClassDecl, Expr, ExprKind, FunctionDecl, HookBody, Member, MethodDecl, Name,
    PropertyHook, Stmt, StmtKind,
};
use php_diagnostics::Diagnostic;
use php_phpdoc::parse as parse_doc;
use php_reflect::{resolve_doc_type, ReflectionIndex};
use php_resolve::{for_each_region, Resolution, Scope};
use php_span::Span;
use php_types::Type;
use std::collections::HashSet;

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
        let Some(c) = refl.class(fqn) else {
            return false;
        };
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
            walk::for_each_expr(
                &php_ast::Program {
                    stmts: vec![st.clone()],
                },
                &mut |e| {
                    let ExprKind::Throw(inner) = &e.kind else {
                        return;
                    };
                    if let Some(d) = check_thrown(fa, scope, inner) {
                        out.push(d);
                    }
                },
            );
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
            let Resolution::Fqn(fqn) = scope.resolve_class(name) else {
                return None;
            };
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
                let StmtKind::Try { catches, .. } = &s.kind else {
                    return;
                };
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
    let Resolution::Fqn(fqn) = scope.resolve_class(ty) else {
        return;
    };
    // Existence (`class.notFound`) is the unknown-symbol rule's job. Here we only
    // classify a *known* caught class. Only a fully-known class whose ancestry is
    // entirely indexed can be confidently declared a non-throwable (an unindexed
    // ancestor could be `Throwable`/`Exception`/`Error`). Interfaces are always
    // allowed as catch types in phpstan.
    let Some(cr) = fa.reflection.class(&fqn) else {
        return;
    };
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
        Diagnostic::error(
            ty.span,
            format!("Caught class {display} is not an exception."),
        )
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
        StmtKind::Return(_) => out.push(ExitPoint {
            word: "return",
            span: st.span,
        }),
        StmtKind::Break(_) => out.push(ExitPoint {
            word: "break",
            span: st.span,
        }),
        StmtKind::Continue(_) => out.push(ExitPoint {
            word: "continue",
            span: st.span,
        }),
        StmtKind::Expr(e) if matches!(e.kind, ExprKind::Throw(_)) => out.push(ExitPoint {
            word: "throw",
            span: st.span,
        }),
        StmtKind::Block(b) => collect_exit_points(b, out),
        StmtKind::If {
            then, elseifs, els, ..
        } => {
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
        let StmtKind::Try {
            body,
            catches,
            finally,
        } = &s.kind
        else {
            return;
        };
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
                let StmtKind::Try { catches, .. } = &s.kind else {
                    return;
                };
                check_dead_catches(fa, scope, catches, &mut out);
            });
        }
    });
    out
}

fn check_dead_catches(
    fa: &FileAnalysis,
    scope: &Scope,
    catches: &[Catch],
    out: &mut Vec<Diagnostic>,
) {
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
            && resolved.iter().all(|ty| {
                seen.iter()
                    .any(|prev| fa.reflection.is_subclass_of(ty, prev))
            });
        if all_covered {
            let display = resolved.join("|");
            let span = c
                .types
                .first()
                .unwrap()
                .span
                .to(c.types.last().unwrap().span);
            out.push(
                Diagnostic::error(
                    span,
                    format!("Dead catch - {display} is already caught above."),
                )
                .with_code("catch.alreadyCaught"),
            );
        }
        seen.extend(resolved);
    }
}

// ---------------------------------------------------------------------------
// ThrowsVoid*WithExplicitThrowPointRule — `throws.void`
// ---------------------------------------------------------------------------

/// PHPStan's `ThrowsVoid*WithExplicitThrowPointRule` reports a declaration whose
/// PHPDoc says `@throws void` but whose body contains an explicit `throw`
/// expression. We intentionally model only explicit throw points in the body;
/// throws coming from called functions/methods need a full throw-set analysis and
/// belong to the Missing/TooWide throw-type rules.
fn run_throws_void_function(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            walk_function_decls(st, scope, &mut |scope, fd| {
                if !doc_throws_void(scope, fd.doc.as_deref()) {
                    return;
                }
                let name = scope.qualify(fa.interner.resolve(fd.name));
                for tp in explicit_throw_points(fa, &fd.body) {
                    out.push(
                        Diagnostic::error(
                            tp.span,
                            format!(
                                "Function {}() throws exception {} but the PHPDoc contains @throws void.",
                                name.trim_start_matches('\\'),
                                tp.display
                            ),
                        )
                        .with_code("throws.void"),
                    );
                }
            });
        }
    });
    out
}

fn run_throws_void_method(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            walk_method_decls(st, scope, &mut |scope, class, md| {
                let Some(body) = &md.body else { return };
                if !doc_throws_void(scope, md.doc.as_deref()) {
                    return;
                }
                let Some(class_name) = class.name else { return };
                let class_display = scope.qualify(fa.interner.resolve(class_name));
                let method = fa.interner.resolve(md.name);
                for tp in explicit_throw_points(fa, body) {
                    out.push(
                        Diagnostic::error(
                            tp.span,
                            format!(
                                "Method {}::{}() throws exception {} but the PHPDoc contains @throws void.",
                                class_display.trim_start_matches('\\'),
                                method,
                                tp.display
                            ),
                        )
                        .with_code("throws.void"),
                    );
                }
            });
        }
    });
    out
}

fn run_throws_void_property_hook(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            let StmtKind::Class(class) = &st.kind else {
                continue;
            };
            let Some(class_name) = class.name else {
                continue;
            };
            let class_display = scope.qualify(fa.interner.resolve(class_name));
            for member in &class.members {
                let Member::Property(prop) = member else {
                    continue;
                };
                for elem in &prop.props {
                    let property_name = fa.interner.resolve(elem.name);
                    let Some(hooks) = &elem.hooks else { continue };
                    for hook in hooks {
                        if !doc_throws_void(scope, hook.doc.as_deref()) {
                            continue;
                        }
                        let hook_name = fa.interner.resolve(hook.name);
                        for tp in explicit_throw_points_in_hook(fa, hook) {
                            out.push(
                                Diagnostic::error(
                                    tp.span,
                                    format!(
                                        "{} hook for property {}::${} throws exception {} but the PHPDoc contains @throws void.",
                                        hook_name_title(hook_name),
                                        class_display.trim_start_matches('\\'),
                                        property_name,
                                        tp.display
                                    ),
                                )
                                .with_code("throws.void"),
                            );
                        }
                    }
                }
            }
        }
    });
    out
}

fn hook_name_title(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().chain(chars).collect(),
        None => String::new(),
    }
}

fn doc_throws_void(scope: &Scope, doc: Option<&str>) -> bool {
    let Some(raw) = doc else { return false };
    let doc = parse_doc(raw);
    !doc.throws.is_empty()
        && doc
            .throws
            .iter()
            .all(|t| type_is_void(&resolve_doc_type(scope, &[], t)))
}

fn type_is_void(t: &Type) -> bool {
    match t {
        Type::Void => true,
        Type::Union(parts) => !parts.is_empty() && parts.iter().all(type_is_void),
        _ => false,
    }
}

struct ThrowPoint {
    span: Span,
    display: String,
}

fn explicit_throw_points(fa: &FileAnalysis, body: &[Stmt]) -> Vec<ThrowPoint> {
    let mut out = Vec::new();
    for st in body {
        walk::for_each_expr_in_scope(st, &mut |e| {
            let ExprKind::Throw(inner) = &e.kind else {
                return;
            };
            out.push(ThrowPoint {
                span: e.span,
                display: display_throw_expr(fa, inner),
            });
        });
    }
    out
}

fn explicit_throw_points_in_hook(fa: &FileAnalysis, hook: &PropertyHook) -> Vec<ThrowPoint> {
    match &hook.body {
        HookBody::Block(body) => explicit_throw_points(fa, body),
        HookBody::Short(expr) => {
            let mut out = Vec::new();
            walk::for_each_subexpr(expr, &mut |e| {
                let ExprKind::Throw(inner) = &e.kind else {
                    return;
                };
                out.push(ThrowPoint {
                    span: e.span,
                    display: display_throw_expr(fa, inner),
                });
            });
            out
        }
        HookBody::Abstract => Vec::new(),
    }
}

fn display_throw_expr(fa: &FileAnalysis, e: &Expr) -> String {
    if let ExprKind::New { class, .. } = &e.kind {
        if let ExprKind::Name(name) = &class.kind {
            return name.text.trim_start_matches('\\').to_string();
        }
    }
    display_throw_type(&fa.type_of(e))
}

fn display_throw_type(t: &Type) -> String {
    match t {
        Type::Named { fqn, args } if args.is_empty() => fqn.trim_start_matches('\\').to_string(),
        Type::Named { fqn, args } => {
            let args = args
                .iter()
                .map(display_throw_type)
                .collect::<Vec<_>>()
                .join(", ");
            format!("{}<{args}>", fqn.trim_start_matches('\\'))
        }
        Type::Union(parts) => parts
            .iter()
            .map(display_throw_type)
            .collect::<Vec<_>>()
            .join("|"),
        Type::Intersection(parts) => parts
            .iter()
            .map(display_throw_type)
            .collect::<Vec<_>>()
            .join("&"),
        Type::Nullable(inner) => format!("?{}", display_throw_type(inner)),
        _ => t.to_string(),
    }
}

fn walk_function_decls<'a>(
    st: &'a Stmt,
    scope: &Scope,
    f: &mut impl FnMut(&Scope, &'a FunctionDecl),
) {
    match &st.kind {
        StmtKind::Function(fd) => {
            f(scope, fd);
            for s in fd.body.iter() {
                walk_function_decls(s, scope, f);
            }
        }
        StmtKind::Class(c) => {
            for m in &c.members {
                if let Member::Method(md) = m {
                    if let Some(body) = &md.body {
                        for s in body.iter() {
                            walk_function_decls(s, scope, f);
                        }
                    }
                }
            }
        }
        StmtKind::Block(body) => {
            for s in body {
                walk_function_decls(s, scope, f);
            }
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            walk_function_decls(then, scope, f);
            for ei in elseifs {
                walk_function_decls(&ei.body, scope, f);
            }
            if let Some(e) = els {
                walk_function_decls(e, scope, f);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. }
        | StmtKind::Declare {
            body: Some(body), ..
        } => walk_function_decls(body, scope, f),
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                for s in &c.body {
                    walk_function_decls(s, scope, f);
                }
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for s in body {
                walk_function_decls(s, scope, f);
            }
            for c in catches {
                for s in &c.body {
                    walk_function_decls(s, scope, f);
                }
            }
            if let Some(fin) = finally {
                for s in fin {
                    walk_function_decls(s, scope, f);
                }
            }
        }
        StmtKind::Namespace {
            body: Some(body), ..
        } => {
            for s in body {
                walk_function_decls(s, scope, f);
            }
        }
        _ => {}
    }
}

fn walk_method_decls<'a>(
    st: &'a Stmt,
    scope: &Scope,
    f: &mut impl FnMut(&Scope, &'a ClassDecl, &'a MethodDecl),
) {
    match &st.kind {
        StmtKind::Class(c) => {
            for m in &c.members {
                if let Member::Method(md) = m {
                    f(scope, c, md);
                    if let Some(body) = &md.body {
                        for s in body.iter() {
                            walk_method_decls(s, scope, f);
                        }
                    }
                }
            }
        }
        StmtKind::Function(fd) => {
            for s in fd.body.iter() {
                walk_method_decls(s, scope, f);
            }
        }
        StmtKind::Block(body) => {
            for s in body {
                walk_method_decls(s, scope, f);
            }
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            walk_method_decls(then, scope, f);
            for ei in elseifs {
                walk_method_decls(&ei.body, scope, f);
            }
            if let Some(e) = els {
                walk_method_decls(e, scope, f);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. }
        | StmtKind::Declare {
            body: Some(body), ..
        } => walk_method_decls(body, scope, f),
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                for s in &c.body {
                    walk_method_decls(s, scope, f);
                }
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for s in body {
                walk_method_decls(s, scope, f);
            }
            for c in catches {
                for s in &c.body {
                    walk_method_decls(s, scope, f);
                }
            }
            if let Some(fin) = finally {
                for s in fin {
                    walk_method_decls(s, scope, f);
                }
            }
        }
        StmtKind::Namespace {
            body: Some(body), ..
        } => {
            for s in body {
                walk_method_decls(s, scope, f);
            }
        }
        _ => {}
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
        let StmtKind::Try { catches, .. } = &s.kind else {
            return;
        };
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

// ---------------------------------------------------------------------------
// TooWide{Function,Method}ThrowTypeRule — `throws.unusedType` (level 4)
//
// A declared `@throws T` that the body never (statically) throws. phpstan does
// interprocedural throw inference + curated built-in throw modeling; we have
// neither, so we take the *FP-safe* subset: only **explicit `throw`** produces a
// precise thrown type. ANY call/`new`/`clone`/`match`/`eval`/division is a
// "broad" throw source (it could throw anything, incl. via an unannotated
// callee), and its presence suppresses every unused report for that body. So we
// report T only when the body has no broad source and no explicit `throw` of a
// type *related* to T (matching phpstan on empty-body and unrelated-explicit-
// throw cases; under-reporting the built-in-specific cases it can't see).

/// Escaping throw signature of a body: the concrete thrown class types (from
/// `throw new X` / `throw $typed`) and whether a broad (unmodelable) throw
/// source is present. Caught-vs-uncaught is not distinguished — keeping caught
/// throws only makes declared types *more* justified (fewer reports), which is
/// the FP-safe direction.
fn escaping_throw_signature(fa: &FileAnalysis, body: &[Stmt]) -> (Vec<Type>, bool) {
    // `new`/anon-class operands that are the direct object of a `throw`: the
    // construction of the thrown exception itself is not a broad source.
    let mut thrown_new_ops: HashSet<*const Expr> = HashSet::new();
    let mut concrete: Vec<Type> = Vec::new();
    let mut broad = false;

    for st in body {
        walk::for_each_expr_in_scope(st, &mut |e| {
            let ExprKind::Throw(inner) = &e.kind else {
                return;
            };
            if matches!(&inner.kind, ExprKind::New { .. } | ExprKind::NewAnon { .. }) {
                thrown_new_ops.insert(inner.as_ref() as *const Expr);
            }
            match fa.type_of(inner) {
                t @ Type::Named { .. } => concrete.push(t),
                // A dynamically-typed thrown value could be anything.
                _ => broad = true,
            }
        });
    }
    for st in body {
        walk::for_each_expr_in_scope(st, &mut |e| {
            let is_broad = match &e.kind {
                ExprKind::Call { .. }
                | ExprKind::MethodCall { .. }
                | ExprKind::StaticCall { .. }
                | ExprKind::Clone(_)
                | ExprKind::Match { .. }
                | ExprKind::Eval(_) => true,
                // A `new` throws (its constructor) unless it *is* the thrown
                // object (`throw new X()` is a precise X point, not broad).
                ExprKind::New { .. } | ExprKind::NewAnon { .. } => {
                    !thrown_new_ops.contains(&(e as *const Expr))
                }
                // Division / modulo by zero throws DivisionByZeroError.
                ExprKind::Binary {
                    op: BinOp::Div | BinOp::Mod,
                    ..
                } => true,
                _ => false,
            };
            broad |= is_broad;
        });
    }
    (concrete, broad)
}

/// `sub` is-a `sup` in the throwable hierarchy (reflexive, transitive over
/// parents/interfaces; everything throwable is-a `Throwable`). Cycle-tolerant.
fn throwable_is_a(refl: &ReflectionIndex, sub: &str, sup: &str) -> bool {
    let sub = sub.trim_start_matches('\\');
    let sup = sup.trim_start_matches('\\');
    if sub.eq_ignore_ascii_case(sup) {
        return true;
    }
    if sup.eq_ignore_ascii_case("Throwable") && is_throwable_class(refl, sub) {
        return true;
    }
    fn walk(refl: &ReflectionIndex, fqn: &str, sup: &str, seen: &mut Vec<String>) -> bool {
        let key = fqn.trim_start_matches('\\').to_ascii_lowercase();
        if seen.contains(&key) {
            return false;
        }
        seen.push(key);
        let Some(c) = refl.class(fqn) else {
            return false;
        };
        c.parents.iter().chain(&c.interfaces).any(|t| match t {
            Type::Named { fqn, .. } => {
                fqn.trim_start_matches('\\').eq_ignore_ascii_case(sup) || walk(refl, fqn, sup, seen)
            }
            _ => false,
        })
    }
    walk(refl, sub, sup, &mut Vec::new())
}

/// Whether `fqn`'s entire throwable ancestry is resolvable — a known root
/// (`Throwable`/`Exception`/`Error`) or indexed with every ancestor likewise
/// known. Only then can we *confidently* judge two classes unrelated (an
/// unindexed ancestor could secretly relate them → would be a false positive).
fn throwable_hierarchy_known(refl: &ReflectionIndex, fqn: &str) -> bool {
    fn walk(refl: &ReflectionIndex, fqn: &str, seen: &mut Vec<String>) -> bool {
        if is_throwable_name(fqn) {
            return true;
        }
        let key = fqn.trim_start_matches('\\').to_ascii_lowercase();
        if seen.contains(&key) {
            return true;
        }
        seen.push(key);
        let Some(c) = refl.class(fqn) else {
            return false;
        };
        c.parents.iter().chain(&c.interfaces).all(|t| match t {
            Type::Named { fqn, .. } => walk(refl, fqn, seen),
            _ => true,
        })
    }
    walk(refl, fqn, &mut Vec::new())
}

/// The FQN of a single concrete throwable type, if it is one.
fn named_fqn(t: &Type) -> Option<&str> {
    match t {
        Type::Named { fqn, .. } => Some(fqn),
        _ => None,
    }
}

fn check_too_wide_throws(
    fa: &FileAnalysis,
    scope: &Scope,
    doc: Option<&str>,
    body: &[Stmt],
    subject: &str,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    let Some(doc) = doc else { return };
    let parsed = parse_doc(doc);
    if parsed.throws.is_empty() {
        return;
    }
    let refl = fa.reflection;
    let (concrete, broad) = escaping_throw_signature(fa, body);
    // A broad source could throw anything: we cannot prove any declared type
    // unused.
    if broad {
        return;
    }
    // Every thrown type must be confidently resolvable, else "unrelated" is not
    // provable.
    if concrete
        .iter()
        .any(|c| named_fqn(c).is_none_or(|f| !throwable_hierarchy_known(refl, f)))
    {
        return;
    }

    // Flatten the declared @throws into individual class types.
    let mut declared: Vec<Type> = Vec::new();
    for t in &parsed.throws {
        match resolve_doc_type(scope, &[], t) {
            Type::Union(parts) => declared.extend(parts.iter().cloned()),
            other => declared.push(other),
        }
    }
    let mut seen_reported: Vec<String> = Vec::new();
    for dt in &declared {
        let Some(dfqn) = named_fqn(dt) else { continue };
        // Only throwable, fully-resolvable declared types are judged here.
        if !is_throwable_class(refl, dfqn) || !throwable_hierarchy_known(refl, dfqn) {
            continue;
        }
        let key = dfqn.trim_start_matches('\\').to_ascii_lowercase();
        if seen_reported.contains(&key) {
            continue;
        }
        // Used iff some thrown type is related (either is-a the other).
        let used = concrete.iter().any(|c| {
            let cf = named_fqn(c).unwrap();
            throwable_is_a(refl, cf, dfqn) || throwable_is_a(refl, dfqn, cf)
        });
        if used {
            continue;
        }
        seen_reported.push(key);
        out.push(
            Diagnostic::error(
                span,
                format!(
                    "{subject} has {} in PHPDoc @throws tag but it's not thrown.",
                    display_throw_type(dt)
                ),
            )
            .with_code("throws.unusedType"),
        );
    }
}

fn run_too_wide_throw_type_function(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            walk_function_decls(st, scope, &mut |scope, fd| {
                let name = scope.qualify(fa.interner.resolve(fd.name));
                check_too_wide_throws(
                    fa,
                    scope,
                    fd.doc.as_deref(),
                    &fd.body,
                    &format!("Function {}()", name.trim_start_matches('\\')),
                    fd.name_span,
                    &mut out,
                );
            });
        }
    });
    out
}

fn run_too_wide_throw_type_method(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            walk_method_decls(st, scope, &mut |scope, c, md| {
                let Some(body) = &md.body else { return };
                let class = c
                    .name
                    .map(|n| scope.qualify(fa.interner.resolve(n)))
                    .unwrap_or_default();
                let method = fa.interner.resolve(md.name);
                check_too_wide_throws(
                    fa,
                    scope,
                    md.doc.as_deref(),
                    body,
                    &format!("Method {}::{method}()", class.trim_start_matches('\\')),
                    md.name_span,
                    &mut out,
                );
            });
        }
    });
    out
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "throws.unusedType",
        level: 4,
        run: run_too_wide_throw_type_function,
    },
    RuleEntry {
        name: "throws.unusedType",
        level: 4,
        run: run_too_wide_throw_type_method,
    },
    RuleEntry {
        name: "throw.notThrowable",
        level: 3,
        run: run_throw_expr_type,
    },
    RuleEntry {
        name: "catch.notThrowable",
        level: 0,
        run: run_caught_exception,
    },
    RuleEntry {
        name: "finally.exitPoint",
        level: 4,
        run: run_overwritten_finally,
    },
    RuleEntry {
        name: "catch.alreadyCaught",
        level: 4,
        run: run_dead_catch,
    },
    RuleEntry {
        name: "throws.void.function",
        level: 3,
        run: run_throws_void_function,
    },
    RuleEntry {
        name: "throws.void.method",
        level: 3,
        run: run_throws_void_method,
    },
    RuleEntry {
        name: "throws.void.propertyHook",
        level: 3,
        run: run_throws_void_property_hook,
    },
    RuleEntry {
        name: "catch.nonCapturingNotSupported",
        level: 0,
        run: run_noncapturing_catch,
    },
    RuleEntry {
        name: "throw.notSupported",
        level: 0,
        run: run_throw_expression,
    },
];

#[cfg(test)]
mod tests {
    use crate::testutil::{codes, codes_version, run};
    use crate::PhpVersion;

    use super::*;

    // --- TooWide throw type (throws.unusedType) ---

    #[test]
    fn unused_throws_empty_body_is_flagged() {
        let src = "<?php /** @throws \\RuntimeException */ function f(): void {}";
        let ds = run(src, run_too_wide_throw_type_function);
        assert_eq!(
            codes(src, run_too_wide_throw_type_function),
            ["throws.unusedType"]
        );
        assert_eq!(
            ds[0].message,
            "Function f() has RuntimeException in PHPDoc @throws tag but it's not thrown."
        );
    }

    #[test]
    fn unused_throws_unrelated_explicit_throw_is_flagged() {
        let src = "<?php /** @throws \\RuntimeException */ function f(): void { throw new \\LogicException('x'); }";
        assert_eq!(
            codes(src, run_too_wide_throw_type_function),
            ["throws.unusedType"]
        );
    }

    #[test]
    fn declared_throws_matching_explicit_throw_is_clean() {
        let src = "<?php /** @throws \\RuntimeException */ function f(): void { throw new \\RuntimeException('x'); }";
        assert!(codes(src, run_too_wide_throw_type_function).is_empty());
    }

    #[test]
    fn declared_supertype_of_thrown_is_clean() {
        // @throws Exception, throws RuntimeException — Exception covers it.
        let src = "<?php /** @throws \\Exception */ function f(): void { throw new \\RuntimeException('x'); }";
        assert!(codes(src, run_too_wide_throw_type_function).is_empty());
    }

    #[test]
    fn broad_call_suppresses_unused_report() {
        // An unannotated call is a broad throw source → cannot prove unused.
        let src = "<?php function helper(): void {} /** @throws \\RuntimeException */ function f(): void { helper(); }";
        assert!(codes(src, run_too_wide_throw_type_function).is_empty());
    }

    #[test]
    fn throw_new_is_not_a_broad_source() {
        // `throw new X` must not itself count as a broad `new`, else the
        // unrelated-throw report would never fire.
        let src = "<?php /** @throws \\RuntimeException */ function f(): void { throw new \\LogicException('x'); }";
        assert_eq!(
            codes(src, run_too_wide_throw_type_function),
            ["throws.unusedType"]
        );
    }

    #[test]
    fn unresolvable_declared_type_is_not_reported() {
        // A declared type whose hierarchy we can't resolve is left alone (safe).
        let src = "<?php /** @throws \\Vendor\\MysteryError */ function f(): void {}";
        assert!(codes(src, run_too_wide_throw_type_function).is_empty());
    }

    #[test]
    fn unused_throws_on_method_is_flagged() {
        let src =
            "<?php class C { /** @throws \\RuntimeException */ public function m(): void {} }";
        let ds = run(src, run_too_wide_throw_type_method);
        assert_eq!(
            codes(src, run_too_wide_throw_type_method),
            ["throws.unusedType"]
        );
        assert_eq!(
            ds[0].message,
            "Method C::m() has RuntimeException in PHPDoc @throws tag but it's not thrown."
        );
    }

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
        let src =
            r#"<?php class MyExc extends Exception {} function f() { try {} catch (MyExc $e) {} }"#;
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
    fn builtin_hierarchy_is_known_for_dead_catch() {
        // Built-in SPL hierarchy is indexed, so RuntimeException is known to be
        // covered by the earlier Exception catch.
        let src = r#"<?php
            function f() { try {} catch (\Exception $e) {} catch (\RuntimeException $e) {} }"#;
        assert_eq!(codes(src, run_dead_catch), ["catch.alreadyCaught"]);
    }

    // --- ThrowsVoidFunctionWithExplicitThrowPointRule --------------------

    #[test]
    fn throws_void_function_with_direct_throw_is_flagged() {
        let src = r#"<?php
            /** @throws void */
            function f(): void { throw new \RuntimeException(); }"#;
        assert_eq!(codes(src, run_throws_void_function), ["throws.void"]);
    }

    #[test]
    fn throws_void_function_message_matches_phpstan() {
        let src = r#"<?php namespace App;
            /** @throws void */
            function f(): void { throw new \RuntimeException(); }"#;
        let messages = run(src, run_throws_void_function)
            .into_iter()
            .map(|d| d.message)
            .collect::<Vec<_>>();
        assert_eq!(
            messages,
            ["Function App\\f() throws exception RuntimeException but the PHPDoc contains @throws void."]
        );
    }

    #[test]
    fn phpstan_throws_void_function_is_flagged() {
        let src = r#"<?php
            /** @phpstan-throws void */
            function f(): void { throw new \RuntimeException(); }"#;
        assert_eq!(codes(src, run_throws_void_function), ["throws.void"]);
    }

    #[test]
    fn throws_void_function_without_throw_is_clean() {
        let src = r#"<?php
            /** @throws void */
            function f(): void { echo "ok"; }"#;
        assert!(codes(src, run_throws_void_function).is_empty());
    }

    #[test]
    fn throws_exception_function_is_clean() {
        let src = r#"<?php
            /** @throws \RuntimeException */
            function f(): void { throw new \RuntimeException(); }"#;
        assert!(codes(src, run_throws_void_function).is_empty());
    }

    #[test]
    fn nested_closure_throw_does_not_belong_to_outer_function() {
        let src = r#"<?php
            /** @throws void */
            function f(): void {
                $cb = function (): void { throw new \RuntimeException(); };
            }"#;
        assert!(codes(src, run_throws_void_function).is_empty());
    }

    #[test]
    fn nested_named_function_is_checked_independently() {
        let src = r#"<?php
            function outer(): void {
                /** @throws void */
                function inner(): void { throw new \RuntimeException(); }
            }"#;
        assert_eq!(codes(src, run_throws_void_function), ["throws.void"]);
    }

    #[test]
    fn thrown_typed_param_in_throws_void_function_is_flagged() {
        let src = r#"<?php
            /** @throws void */
            function f(\RuntimeException $e): void { throw $e; }"#;
        assert_eq!(codes(src, run_throws_void_function), ["throws.void"]);
    }

    // --- ThrowsVoidMethodWithExplicitThrowPointRule ----------------------

    #[test]
    fn throws_void_method_with_direct_throw_is_flagged() {
        let src = r#"<?php
            class C {
                /** @throws void */
                public function m(): void { throw new \RuntimeException(); }
            }"#;
        assert_eq!(codes(src, run_throws_void_method), ["throws.void"]);
    }

    #[test]
    fn throws_void_method_message_matches_phpstan() {
        let src = r#"<?php namespace App;
            class C {
                /** @throws void */
                public function m(): void { throw new \RuntimeException(); }
            }"#;
        let messages = run(src, run_throws_void_method)
            .into_iter()
            .map(|d| d.message)
            .collect::<Vec<_>>();
        assert_eq!(
            messages,
            ["Method App\\C::m() throws exception RuntimeException but the PHPDoc contains @throws void."]
        );
    }

    #[test]
    fn throws_void_method_without_body_throw_is_clean() {
        let src = r#"<?php
            class C {
                /** @throws void */
                public function m(): void { echo "ok"; }
            }"#;
        assert!(codes(src, run_throws_void_method).is_empty());
    }

    #[test]
    fn method_with_non_void_throws_doc_is_clean() {
        let src = r#"<?php
            class C {
                /** @throws \RuntimeException */
                public function m(): void { throw new \RuntimeException(); }
            }"#;
        assert!(codes(src, run_throws_void_method).is_empty());
    }

    #[test]
    fn nested_closure_throw_does_not_belong_to_method() {
        let src = r#"<?php
            class C {
                /** @throws void */
                public function m(): void {
                    $cb = function (): void { throw new \RuntimeException(); };
                }
            }"#;
        assert!(codes(src, run_throws_void_method).is_empty());
    }

    #[test]
    fn nested_class_method_is_checked_independently() {
        let src = r#"<?php
            function f(): void {
                class Inner {
                    /** @throws void */
                    public function m(): void { throw new \RuntimeException(); }
                }
            }"#;
        assert_eq!(codes(src, run_throws_void_method), ["throws.void"]);
    }

    // --- ThrowsVoidPropertyHookWithExplicitThrowPointRule ----------------

    #[test]
    fn throws_void_property_get_hook_with_throw_is_flagged() {
        let src = r#"<?php
            class C {
                public int $p {
                    /** @throws void */
                    get { throw new \RuntimeException(); }
                }
            }"#;
        assert_eq!(codes(src, run_throws_void_property_hook), ["throws.void"]);
    }

    #[test]
    fn throws_void_property_hook_message_matches_phpstan() {
        let src = r#"<?php namespace App;
            class C {
                public int $p {
                    /** @throws void */
                    get { throw new \RuntimeException(); }
                }
            }"#;
        let messages = run(src, run_throws_void_property_hook)
            .into_iter()
            .map(|d| d.message)
            .collect::<Vec<_>>();
        assert_eq!(
            messages,
            ["Get hook for property App\\C::$p throws exception RuntimeException but the PHPDoc contains @throws void."]
        );
    }

    #[test]
    fn throws_void_short_property_hook_with_throw_is_flagged() {
        let src = r#"<?php
            class C {
                public int $p {
                    /** @throws void */
                    get => throw new \RuntimeException();
                }
            }"#;
        assert_eq!(codes(src, run_throws_void_property_hook), ["throws.void"]);
    }

    #[test]
    fn property_level_throws_void_does_not_count_as_hook_docblock() {
        let src = r#"<?php
            class C {
                /** @throws void */
                public int $p {
                    get { throw new \RuntimeException(); }
                }
            }"#;
        assert!(codes(src, run_throws_void_property_hook).is_empty());
    }

    // --- NoncapturingCatchRule (version-gated) ---

    #[test]
    fn noncapturing_catch_flagged_below_php80() {
        let src = r#"<?php function f() { try {} catch (\Exception) {} }"#;
        assert_eq!(
            codes_version(
                src,
                run_noncapturing_catch,
                PhpVersion::parse("7.4").unwrap()
            ),
            ["catch.nonCapturingNotSupported"]
        );
    }

    #[test]
    fn noncapturing_catch_ok_on_php80_plus() {
        let src = r#"<?php function f() { try {} catch (\Exception) {} }"#;
        assert!(codes(src, run_noncapturing_catch).is_empty()); // default 8.4
                                                                // A capturing catch is fine even below 8.0.
        let cap = r#"<?php function f() { try {} catch (\Exception $e) {} }"#;
        assert!(codes_version(
            cap,
            run_noncapturing_catch,
            PhpVersion::parse("7.4").unwrap()
        )
        .is_empty());
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
        assert!(
            codes_version(src, run_throw_expression, PhpVersion::parse("7.4").unwrap()).is_empty()
        );
    }

    #[test]
    fn throw_expression_ok_on_php80_plus() {
        let src = r#"<?php function f($x) { $y = $x ?? throw new \Exception(); }"#;
        assert!(codes(src, run_throw_expression).is_empty()); // default 8.4
    }
}
