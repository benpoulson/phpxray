//! phpstan category **TooWideTypehints** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/TooWideTypehints/` — 7 rule(s) at level 4.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented here (all `return.unusedType`, level 4):
//! - **TooWideFunctionReturnTypehintRule** — a named function whose declared
//!   *union* return type contains a member it never actually returns.
//! - **TooWideMethodReturnTypehintRule** — likewise for a method (private methods
//!   only; for non-private methods phpstan needs the inheritance chain /
//!   `checkProtectedAndPublicMethods` toggle, which we don't model — so we stay
//!   private-only, matching phpstan's default behaviour for a first declaration).
//! - **TooWideClosureReturnTypehintRule** — likewise for a `function () { … }`
//!   closure with a declared union return type.
//! - **TooWideArrowFunctionReturnTypehintRule** — likewise for an `fn () => …`
//!   arrow function with a declared union return type.
//!
//! The shared engine ([`check_returns`]) mirrors phpstan's `TooWideTypeCheck`:
//! collect every returned value's type, and for each member of the declared
//! *union* return type, if no returned value is a subtype of it, the member is
//! unused and can be removed.
//!
//! **Zero-false-positive discipline.** We only flag a union member as unused when
//! the whole body is fully analyzable: we bail entirely on generators
//! (`yield`/`yield from`), on any returned expression whose inferred type is
//! `mixed`/unknown, and when there are no value returns. The `null` member is
//! never flagged if the body can fall through (an implicit `null` return), and we
//! only flag a member when `is_assignable` is a *confident* negative for every
//! returned value (it is lenient, so "not assignable" means genuinely
//! incompatible).
//!
//! Deferred (need analysis we don't expose):
//! - `TooWidePropertyTypeRule` — needs the set of every assignment to a private
//!   property across the class body unioned with its default; our type map does
//!   not track per-property assigned-type aggregation. DEFERRED.
//! - `TooWideFunctionParameterOutTypeRule` / `TooWideMethodParameterOutTypeRule` /
//!   `TooWidePropertyHookParameterType*` — need `@param-out` / by-ref end-of-body
//!   variable types, which the rules layer does not surface. DEFERRED.

#![allow(unused_imports)]
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{
    ArrowFn, ClassDecl, ClosureExpr, Expr, ExprKind, FunctionDecl, Member, MethodDecl, Param,
    Program, Stmt, StmtKind, Type as AstType, TypeKind,
};
use php_diagnostics::Diagnostic;
use php_infer::TypeCtx;
use php_reflect::resolve_ast_type;
use php_resolve::{for_each_region, Scope};
use php_types::Type;

// ---------------------------------------------------------------------------
// Shared return-type engine
// ---------------------------------------------------------------------------

/// Decompose a syntactic return type into its *resolved* union members, *iff* it
/// is written as a union (`A|B`, `?A` ≡ `A|null`). A non-union declared type (a
/// bare `int`, etc.) has nothing to narrow — phpstan only fires on `UnionType` —
/// so we return `None`, signalling "skip this declaration".
fn union_members(scope: &Scope, ty: &AstType) -> Option<Vec<Type>> {
    match &ty.kind {
        TypeKind::Union(parts) => Some(parts.iter().map(|p| resolve_ast_type(scope, p)).collect()),
        // `?T` ≡ `T | null`.
        TypeKind::Nullable(inner) => Some(vec![resolve_ast_type(scope, inner), Type::Null]),
        _ => None,
    }
}

/// Whether `t` is too imprecise to reason about (forces a bail).
fn is_unknown_ish(t: &Type) -> bool {
    matches!(t, Type::Mixed | Type::Unknown(_))
}

/// Whether `t` (a *declared union member*) is the `null` type.
fn is_null_member(t: &Type) -> bool {
    matches!(t, Type::Null)
}

/// Core check, shared by all four rules. `members` are the declared union's
/// members (already resolved); `return_types` are the inferred types of every
/// `return <expr>` in the body; `may_fall_through` is true if control can reach
/// the end of the body without a value return (so an implicit `null` is
/// possible); `description` is the phpstan-style "Function foo()" prefix.
///
/// Returns one `return.unusedType` diagnostic per provably-unused member, at
/// `span`.
fn flag_unused_members(
    index: &php_reflect::ReflectionIndex,
    members: &[Type],
    return_types: &[Type],
    may_fall_through: bool,
    description: &str,
    span: php_span::Span,
) -> Vec<Diagnostic> {
    // Flatten any returned *union* types into their atomic members: a declared
    // member M is "used" if some atomic returned type is assignable to M. (A
    // whole union `int|string` is not assignable to `int`, but its `int` arm is —
    // checking the union as a unit would wrongly flag every member.)
    let mut atoms: Vec<Type> = Vec::new();
    for rt in return_types {
        match rt {
            Type::Union(parts) => atoms.extend(parts.iter().cloned()),
            Type::Nullable(inner) => {
                atoms.push((**inner).clone());
                atoms.push(Type::Null);
            }
            other => atoms.push(other.clone()),
        }
    }

    let mut out = Vec::new();
    for m in members {
        // A `null` member is "used" implicitly when the body can fall through.
        if is_null_member(m) && may_fall_through {
            continue;
        }
        // The member is used if any returned (atomic) value is assignable to it.
        let used = atoms.iter().any(|rt| crate::is_assignable(index, rt, m));
        if !used {
            out.push(
                Diagnostic::error(
                    span,
                    format!("{description} never returns {m} so it can be removed from the return type."),
                )
                .with_code("return.unusedType"),
            );
        }
    }
    out
}

/// Analyze one function-like body against a declared union return type. Returns
/// `None` (no diagnostics, skip) on any FP-risk condition; otherwise the list of
/// unused-member diagnostics.
fn check_returns(
    fa: &FileAnalysis,
    scope: &Scope,
    declared: &AstType,
    body: &[Stmt],
    description: &str,
    span: php_span::Span,
) -> Vec<Diagnostic> {
    // phpstan only fires on a declared *union* return type.
    let Some(members) = union_members(scope, declared) else { return Vec::new() };

    // Generators are typed by their yields, not their returns — bail.
    if body_has_yield(body) {
        return Vec::new();
    }

    let mut return_types = Vec::new();
    let mut bare_return = false;
    collect_returns(body, fa, &mut return_types, &mut bare_return);
    // Need at least one value return to know what is/isn't returned.
    if return_types.is_empty() {
        return Vec::new();
    }
    // Any imprecise returned type means we can't prove a member unused.
    if return_types.iter().any(is_unknown_ish) {
        return Vec::new();
    }

    let may_fall_through = bare_return || !always_terminates(body);
    flag_unused_members(fa.reflection, &members, &return_types, may_fall_through, description, span)
}

/// Collect the inferred type (via the file type map) of every `return <expr>;` in
/// `body`, *without* descending into nested function-likes (they have their own
/// return scope). Sets `bare_return` if a value-less `return;` is seen.
fn collect_returns(body: &[Stmt], fa: &FileAnalysis, out: &mut Vec<Type>, bare_return: &mut bool) {
    for s in body {
        collect_returns_stmt(s, fa, out, bare_return);
    }
}

fn collect_returns_stmt(s: &Stmt, fa: &FileAnalysis, out: &mut Vec<Type>, bare_return: &mut bool) {
    match &s.kind {
        StmtKind::Return(Some(e)) => out.push(fa.type_of(e)),
        StmtKind::Return(None) => *bare_return = true,
        StmtKind::Block(b) => collect_returns(b, fa, out, bare_return),
        StmtKind::If { then, elseifs, els, .. } => {
            collect_returns_stmt(then, fa, out, bare_return);
            for ei in elseifs {
                collect_returns_stmt(&ei.body, fa, out, bare_return);
            }
            if let Some(e) = els {
                collect_returns_stmt(e, fa, out, bare_return);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => collect_returns_stmt(body, fa, out, bare_return),
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                collect_returns(&c.body, fa, out, bare_return);
            }
        }
        StmtKind::Try { body, catches, finally } => {
            collect_returns(body, fa, out, bare_return);
            for c in catches {
                collect_returns(&c.body, fa, out, bare_return);
            }
            if let Some(f) = finally {
                collect_returns(f, fa, out, bare_return);
            }
        }
        StmtKind::Declare { body: Some(b), .. } => collect_returns_stmt(b, fa, out, bare_return),
        // Nested function/closure/class declarations have their own return scope.
        _ => {}
    }
}

/// Whether `body` is a generator (contains a `yield` / `yield from`), *not*
/// crossing into nested function-likes (which have their own generator status).
fn body_has_yield(body: &[Stmt]) -> bool {
    let mut found = false;
    for s in body {
        walk::for_each_expr_in_scope(s, &mut |e| {
            if matches!(e.kind, ExprKind::Yield { .. } | ExprKind::YieldFrom(_)) {
                found = true;
            }
        });
    }
    found
}

/// A conservative "does control definitely leave via return/throw at the end?"
/// check. Used only to decide whether an implicit `null` return is possible. If
/// we're unsure we answer `false` (⇒ may fall through ⇒ keep `null`), which is
/// the FP-safe direction.
fn always_terminates(body: &[Stmt]) -> bool {
    match body.last() {
        Some(s) => stmt_always_terminates(s),
        None => false,
    }
}

fn stmt_always_terminates(s: &Stmt) -> bool {
    match &s.kind {
        StmtKind::Return(_) => true,
        // `throw`/`exit` are expressions in PHP, used as expression statements.
        StmtKind::Expr(e) => matches!(e.kind, ExprKind::Throw(_) | ExprKind::Exit(_)),
        StmtKind::Block(b) => always_terminates(b),
        StmtKind::If { then, elseifs, els: Some(els), .. } => {
            stmt_always_terminates(then)
                && elseifs.iter().all(|ei| stmt_always_terminates(&ei.body))
                && stmt_always_terminates(els)
        }
        StmtKind::Switch { cases, .. } => {
            // Every branch (including a default) terminates.
            cases.iter().any(|c| c.test.is_none())
                && cases.iter().all(|c| c.body.last().is_some_and(stmt_always_terminates))
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// TooWideFunctionReturnTypehintRule
// ---------------------------------------------------------------------------

fn run_function_return(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            collect_function_decls(st, fa, scope, &mut out);
        }
    });
    out
}

/// Walk statements for (possibly nested/conditional) named function declarations.
fn collect_function_decls(st: &Stmt, fa: &FileAnalysis, scope: &Scope, out: &mut Vec<Diagnostic>) {
    match &st.kind {
        StmtKind::Function(f) => {
            check_named_function(f, fa, scope, out);
            for inner in &f.body {
                collect_function_decls(inner, fa, scope, out);
            }
        }
        StmtKind::Block(b) => {
            for s in b {
                collect_function_decls(s, fa, scope, out);
            }
        }
        StmtKind::If { then, elseifs, els, .. } => {
            collect_function_decls(then, fa, scope, out);
            for ei in elseifs {
                collect_function_decls(&ei.body, fa, scope, out);
            }
            if let Some(e) = els {
                collect_function_decls(e, fa, scope, out);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => collect_function_decls(body, fa, scope, out),
        StmtKind::Try { body, catches, finally } => {
            for s in body {
                collect_function_decls(s, fa, scope, out);
            }
            for c in catches {
                for s in &c.body {
                    collect_function_decls(s, fa, scope, out);
                }
            }
            if let Some(f) = finally {
                for s in f {
                    collect_function_decls(s, fa, scope, out);
                }
            }
        }
        _ => {}
    }
}

fn check_named_function(f: &FunctionDecl, fa: &FileAnalysis, scope: &Scope, out: &mut Vec<Diagnostic>) {
    let Some(ret) = &f.return_type else { return };
    let name = fa.interner.resolve(f.name);
    let desc = format!("Function {name}()");
    out.extend(check_returns(fa, scope, ret, &f.body, &desc, ret.span));
}

// ---------------------------------------------------------------------------
// TooWideMethodReturnTypehintRule (private methods only — FP-safe subset)
// ---------------------------------------------------------------------------

fn run_method_return(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            collect_method_decls(st, fa, scope, &mut out);
        }
    });
    out
}

fn collect_method_decls(st: &Stmt, fa: &FileAnalysis, scope: &Scope, out: &mut Vec<Diagnostic>) {
    match &st.kind {
        StmtKind::Class(c) => check_class_methods(c, fa, scope, out),
        StmtKind::Block(b) => {
            for s in b {
                collect_method_decls(s, fa, scope, out);
            }
        }
        StmtKind::If { then, elseifs, els, .. } => {
            collect_method_decls(then, fa, scope, out);
            for ei in elseifs {
                collect_method_decls(&ei.body, fa, scope, out);
            }
            if let Some(e) = els {
                collect_method_decls(e, fa, scope, out);
            }
        }
        StmtKind::Function(f) => {
            for s in &f.body {
                collect_method_decls(s, fa, scope, out);
            }
        }
        _ => {}
    }
}

fn check_class_methods(c: &ClassDecl, fa: &FileAnalysis, scope: &Scope, out: &mut Vec<Diagnostic>) {
    // Traits: phpstan skips them here (the method's real class is unknown).
    if c.kind == php_ast::ClassKind::Trait {
        return;
    }
    let class_desc = c
        .name
        .map(|n| scope.qualify(fa.interner.resolve(n)))
        .unwrap_or_else(|| "class@anonymous".to_string());
    for m in &c.members {
        let Member::Method(md) = m else { continue };
        check_method(md, &class_desc, fa, scope, out);
    }
}

fn check_method(md: &MethodDecl, class_desc: &str, fa: &FileAnalysis, scope: &Scope, out: &mut Vec<Diagnostic>) {
    // Only private methods are FP-safe without the full inheritance chain:
    // a protected/public method's prototype may be wider in an ancestor, and
    // phpstan gates those behind `checkProtectedAndPublicMethods` /
    // `isFirstDeclaration`. Private methods can't be overridden ⇒ always safe.
    if md.modifiers.visibility != Some(php_ast::Visibility::Private) {
        return;
    }
    let Some(body) = &md.body else { return }; // abstract/interface — nothing to analyze
    let Some(ret) = &md.return_type else { return };
    let name = fa.interner.resolve(md.name);
    let desc = format!("Method {class_desc}::{name}()");
    out.extend(check_returns(fa, scope, ret, body, &desc, ret.span));
}

// ---------------------------------------------------------------------------
// TooWideClosureReturnTypehintRule
// ---------------------------------------------------------------------------

fn run_closure_return(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        let prog = Program { stmts: region.to_vec() };
        walk::for_each_expr(&prog, &mut |e| {
            if let ExprKind::Closure(cl) = &e.kind {
                check_closure(cl, fa, scope, e.span, &mut out);
            }
        });
    });
    out
}

fn check_closure(cl: &ClosureExpr, fa: &FileAnalysis, scope: &Scope, span: php_span::Span, out: &mut Vec<Diagnostic>) {
    let Some(ret) = &cl.return_type else { return };
    let Some(members) = union_members(scope, ret) else { return };
    if body_has_yield(&cl.body) {
        return;
    }
    // The type map doesn't reach inside closures, so infer locally with a fresh
    // context seeded from the declared parameter types (captured `use` vars and
    // outer locals are `mixed` here — that only makes returns *less* precise, so
    // we bail rather than false-positive).
    let mut ctx = local_ctx(fa, scope, &cl.params);
    let mut return_types = Vec::new();
    let mut bare_return = false;
    collect_returns_ctx(&cl.body, &mut ctx, &mut return_types, &mut bare_return);
    if return_types.is_empty() || return_types.iter().any(is_unknown_ish) {
        return;
    }
    let may_fall_through = bare_return || !always_terminates(&cl.body);
    out.extend(flag_unused_members(fa.reflection, &members, &return_types, may_fall_through, "Anonymous function", span));
}

/// A fresh inference context seeded with `params`' declared types (untyped →
/// `mixed`). Used for closures/arrow-fns, which the file type map leaves opaque.
fn local_ctx<'a>(fa: &'a FileAnalysis, scope: &'a Scope, params: &[Param]) -> TypeCtx<'a> {
    let mut ctx = TypeCtx::new(fa.reflection, scope, fa.interner);
    for p in params {
        let ty = p.ty.as_ref().map(|t| resolve_ast_type(scope, t)).unwrap_or(Type::Mixed);
        ctx.vars.insert(fa.interner.resolve(p.name).to_string(), ty);
    }
    ctx
}

/// Collect returned types from a closure body, threading the flow environment so
/// a returned local carries its assigned type (mirrors `return_type.rs`).
fn collect_returns_ctx(body: &[Stmt], ctx: &mut TypeCtx, out: &mut Vec<Type>, bare_return: &mut bool) {
    for st in body {
        collect_returns_ctx_stmt(st, ctx, out, bare_return);
    }
}

fn collect_returns_ctx_stmt(st: &Stmt, ctx: &mut TypeCtx, out: &mut Vec<Type>, bare_return: &mut bool) {
    match &st.kind {
        StmtKind::Return(Some(e)) => out.push(ctx.infer(e)),
        StmtKind::Return(None) => *bare_return = true,
        StmtKind::Expr(e) => {
            ctx.apply_expr(e);
        }
        StmtKind::Block(b) => collect_returns_ctx(b, ctx, out, bare_return),
        StmtKind::If { cond, then, elseifs, els } => {
            ctx.apply_expr(cond);
            let base = ctx.vars.clone();
            collect_returns_ctx_stmt(then, ctx, out, bare_return);
            for ei in elseifs {
                ctx.vars = base.clone();
                ctx.apply_expr(&ei.cond);
                collect_returns_ctx_stmt(&ei.body, ctx, out, bare_return);
            }
            if let Some(e) = els {
                ctx.vars = base.clone();
                collect_returns_ctx_stmt(e, ctx, out, bare_return);
            }
            ctx.vars = base;
            ctx.exec_stmt(st);
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => {
            let base = ctx.vars.clone();
            collect_returns_ctx_stmt(body, ctx, out, bare_return);
            ctx.vars = base;
            ctx.exec_stmt(st);
        }
        StmtKind::Switch { cases, .. } => {
            let base = ctx.vars.clone();
            for c in cases {
                ctx.vars = base.clone();
                collect_returns_ctx(&c.body, ctx, out, bare_return);
            }
            ctx.vars = base;
            ctx.exec_stmt(st);
        }
        StmtKind::Try { body, catches, finally } => {
            let base = ctx.vars.clone();
            collect_returns_ctx(body, ctx, out, bare_return);
            for c in catches {
                ctx.vars = base.clone();
                collect_returns_ctx(&c.body, ctx, out, bare_return);
            }
            ctx.vars = base.clone();
            if let Some(f) = finally {
                collect_returns_ctx(f, ctx, out, bare_return);
            }
            ctx.vars = base;
            ctx.exec_stmt(st);
        }
        _ => {
            ctx.exec_stmt(st);
        }
    }
}

// ---------------------------------------------------------------------------
// TooWideArrowFunctionReturnTypehintRule
// ---------------------------------------------------------------------------

fn run_arrow_return(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        let prog = Program { stmts: region.to_vec() };
        walk::for_each_expr(&prog, &mut |e| {
            if let ExprKind::ArrowFn(af) = &e.kind {
                check_arrow(af, fa, scope, e.span, &mut out);
            }
        });
    });
    out
}

fn check_arrow(af: &ArrowFn, fa: &FileAnalysis, scope: &Scope, span: php_span::Span, out: &mut Vec<Diagnostic>) {
    let Some(ret) = &af.return_type else { return };
    // An arrow fn's body is a single expression that is its return value;
    // `yield`/`yield from` make it a generator — bail.
    if matches!(af.body.kind, ExprKind::Yield { .. } | ExprKind::YieldFrom(_)) {
        return;
    }
    let Some(members) = union_members(scope, ret) else { return };
    // The type map doesn't reach inside arrow-fns; infer the body locally.
    let ctx = local_ctx(fa, scope, &af.params);
    let rt = ctx.infer(&af.body);
    if is_unknown_ish(&rt) {
        return;
    }
    // An arrow fn always returns its expression (no fall-through, no bare return).
    out.extend(flag_unused_members(fa.reflection, &members, &[rt], false, "Anonymous function", span));
}

// ---------------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------------

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "return.unusedType/function", level: 4, run: run_function_return },
    RuleEntry { name: "return.unusedType/method", level: 4, run: run_method_return },
    RuleEntry { name: "return.unusedType/closure", level: 4, run: run_closure_return },
    RuleEntry { name: "return.unusedType/arrow", level: 4, run: run_arrow_return },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{codes, run};

    fn msgs(src: &str, rule: fn(&FileAnalysis) -> Vec<Diagnostic>) -> Vec<String> {
        run(src, rule).into_iter().map(|d| d.message).collect()
    }

    // --- functions -------------------------------------------------------

    #[test]
    fn function_never_returns_null_is_flagged() {
        let src = "<?php function f(): ?int { return 1; }";
        assert_eq!(
            msgs(src, run_function_return),
            ["Function f() never returns null so it can be removed from the return type."]
        );
    }

    #[test]
    fn function_union_member_unused_is_flagged() {
        let src = "<?php function f(): int|string { return 1; }";
        assert_eq!(
            msgs(src, run_function_return),
            ["Function f() never returns string so it can be removed from the return type."]
        );
    }

    #[test]
    fn function_all_union_members_used_is_clean() {
        let src = "<?php function f(bool $c): int|string { if ($c) { return 1; } return 'x'; }";
        assert!(codes(src, run_function_return).is_empty());
    }

    #[test]
    fn function_returns_null_when_declared_is_clean() {
        let src = "<?php function f(bool $c): ?int { if ($c) { return null; } return 1; }";
        assert!(codes(src, run_function_return).is_empty());
    }

    #[test]
    fn function_fall_through_keeps_null() {
        // Body can fall off the end ⇒ implicit null return ⇒ ?int is justified.
        let src = "<?php function f(bool $c): ?int { if ($c) { return 1; } }";
        assert!(codes(src, run_function_return).is_empty());
    }

    #[test]
    fn function_non_union_return_is_skipped() {
        let src = "<?php function f(): int { return 'wrong-but-not-our-rule'; }";
        assert!(codes(src, run_function_return).is_empty());
    }

    #[test]
    fn function_generator_is_skipped() {
        let src = "<?php function f(): ?int { yield 1; return 2; }";
        assert!(codes(src, run_function_return).is_empty());
    }

    #[test]
    fn function_mixed_return_value_is_skipped() {
        // Returned value type is unknown ⇒ can't prove a member unused.
        let src = "<?php function f($x): ?int { return $x; }";
        assert!(codes(src, run_function_return).is_empty());
    }

    #[test]
    fn function_no_return_type_is_skipped() {
        let src = "<?php function f() { return 1; }";
        assert!(codes(src, run_function_return).is_empty());
    }

    #[test]
    fn function_in_branches_unions_returns() {
        // null only ever returned in one branch, int in another, never string.
        let src = "<?php function f(bool $c): int|string|null { if ($c) { return 1; } return null; }";
        assert_eq!(
            msgs(src, run_function_return),
            ["Function f() never returns string so it can be removed from the return type."]
        );
    }

    // --- methods ---------------------------------------------------------

    #[test]
    fn private_method_unused_member_is_flagged() {
        let src = "<?php class C { private function m(): ?int { return 1; } }";
        assert_eq!(
            msgs(src, run_method_return),
            ["Method C::m() never returns null so it can be removed from the return type."]
        );
    }

    #[test]
    fn public_method_is_skipped() {
        // Non-private ⇒ FP-unsafe without the inheritance chain ⇒ skipped.
        let src = "<?php class C { public function m(): ?int { return 1; } }";
        assert!(codes(src, run_method_return).is_empty());
    }

    #[test]
    fn private_method_all_members_used_is_clean() {
        let src = "<?php class C { private function m(bool $c): ?int { if ($c) { return null; } return 1; } }";
        assert!(codes(src, run_method_return).is_empty());
    }

    #[test]
    fn abstract_method_is_skipped() {
        let src = "<?php abstract class C { abstract private function m(): ?int; }";
        assert!(codes(src, run_method_return).is_empty());
    }

    // --- closures --------------------------------------------------------

    #[test]
    fn closure_unused_member_is_flagged() {
        let src = "<?php $f = function (): int|string { return 1; };";
        assert_eq!(
            msgs(src, run_closure_return),
            ["Anonymous function never returns string so it can be removed from the return type."]
        );
    }

    #[test]
    fn closure_all_members_used_is_clean() {
        let src = "<?php $f = function (bool $c): int|string { if ($c) { return 1; } return 'x'; };";
        assert!(codes(src, run_closure_return).is_empty());
    }

    #[test]
    fn closure_no_return_type_is_skipped() {
        let src = "<?php $f = function () { return 1; };";
        assert!(codes(src, run_closure_return).is_empty());
    }

    // --- arrow functions -------------------------------------------------

    #[test]
    fn arrow_unused_member_is_flagged() {
        let src = "<?php $f = fn (): int|string => 1;";
        assert_eq!(
            msgs(src, run_arrow_return),
            ["Anonymous function never returns string so it can be removed from the return type."]
        );
    }

    #[test]
    fn arrow_all_members_used_is_clean() {
        // The expression is int, declared int — but int|string has a dead string.
        // Use a body whose type is genuinely the whole union via a ternary.
        let src = "<?php $f = fn (bool $c): int|string => $c ? 1 : 'x';";
        assert!(codes(src, run_arrow_return).is_empty());
    }

    #[test]
    fn arrow_nullable_never_null_is_flagged() {
        let src = "<?php $f = fn (): ?int => 1;";
        assert_eq!(
            msgs(src, run_arrow_return),
            ["Anonymous function never returns null so it can be removed from the return type."]
        );
    }

    #[test]
    fn arrow_no_return_type_is_skipped() {
        let src = "<?php $f = fn () => 1;";
        assert!(codes(src, run_arrow_return).is_empty());
    }
}
