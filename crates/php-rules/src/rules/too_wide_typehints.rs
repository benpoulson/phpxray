//! phpstan category **TooWideTypehints** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/TooWideTypehints/` — 7 rule(s) at level 4.
//! The rule set's coverage truth is `cargo run -p xtask -- rule-manifest`; for phpstan's behaviour read `phpstan-src/src/Rules/` directly. Add each rule as a `RuleEntry` to
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
//! - **TooWidePropertyTypeRule** — a private, non-promoted property whose
//!   declared native *union* type contains a member that is never assigned by its
//!   default value or by any directly-resolvable write in the declaring class.
//! - **TooWideFunctionParameterOutTypeRule** / **TooWideMethodParameterOutTypeRule**
//!   — explicit `@param-out` tags only, straight-line bodies only.
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
//! - `TooWideFunctionParameterOutTypeRule` / `TooWideMethodParameterOutTypeRule`
//!   fallback by-ref type branch and inherited/public method branch — need full
//!   final-scope/inheritance semantics to match phpstan without FPs.
//! - `TooWidePropertyHookParameterType*` — needs hook-specific param-out tracking.

use crate::members;
use crate::param_out;
use crate::{symbols, walk, FileAnalysis, RuleEntry};
use php_ast::{
    ArrowFn, ClassDecl, ClosureExpr, Expr, ExprKind, FunctionDecl, HookBody, Member, MemberName,
    MethodDecl, Param, Program, PropElem, PropertyDecl, PropertyHook, Stmt, StmtKind,
    Type as AstType, TypeKind,
};
use php_diagnostics::Diagnostic;
use php_infer::TypeCtx;
use php_reflect::{resolve_ast_type, ParamReflection};
use php_resolve::{for_each_region, Resolution, Scope};
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
    matches!(t, Type::Mixed | Type::ExplicitMixed | Type::Unknown(_))
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

fn flatten_type_atoms(ty: &Type, out: &mut Vec<Type>) {
    match ty {
        Type::Union(parts) => {
            for p in parts.iter() {
                flatten_type_atoms(p, out);
            }
        }
        Type::Nullable(inner) => {
            flatten_type_atoms(inner, out);
            out.push(Type::Null);
        }
        other => out.push(other.clone()),
    }
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
    let Some(members) = union_members(scope, declared) else {
        return Vec::new();
    };

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
    flag_unused_members(
        fa.reflection,
        &members,
        &return_types,
        may_fall_through,
        description,
        span,
    )
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
        StmtKind::If {
            then, elseifs, els, ..
        } => {
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
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
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
        StmtKind::If {
            then,
            elseifs,
            els: Some(els),
            ..
        } => {
            stmt_always_terminates(then)
                && elseifs.iter().all(|ei| stmt_always_terminates(&ei.body))
                && stmt_always_terminates(els)
        }
        StmtKind::Switch { cases, .. } => {
            // Every branch (including a default) terminates.
            cases.iter().any(|c| c.test.is_none())
                && cases
                    .iter()
                    .all(|c| c.body.last().is_some_and(stmt_always_terminates))
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
        StmtKind::If {
            then, elseifs, els, ..
        } => {
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
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
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

fn check_named_function(
    f: &FunctionDecl,
    fa: &FileAnalysis,
    scope: &Scope,
    out: &mut Vec<Diagnostic>,
) {
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
        StmtKind::If {
            then, elseifs, els, ..
        } => {
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
    let class_fqn = c
        .name
        .map(|n| scope.qualify(fa.interner.resolve(n)))
        .unwrap_or_else(|| "class@anonymous".to_string());
    let class_desc = class_fqn.trim_start_matches('\\').to_string();
    for m in &c.members {
        let Member::Method(md) = m else { continue };
        check_method(md, c, &class_fqn, &class_desc, fa, scope, out);
    }
}

fn check_method(
    md: &MethodDecl,
    class: &ClassDecl,
    class_fqn: &str,
    class_desc: &str,
    fa: &FileAnalysis,
    scope: &Scope,
    out: &mut Vec<Diagnostic>,
) {
    // Private methods can't be overridden ⇒ always FP-safe (a wider return has
    // no justification). For non-private methods, matching phpstan:
    //   - a **final** method (or a method of a **final** class) can't be
    //     overridden either, so it's checked unconditionally.
    //   - otherwise the wider type may be justified by a subclass override, so
    //     phpstan gates it behind `checkTooWideReturnTypesInProtectedAndPublicMethods`
    //     *and* the method being an override. We require the flag AND a
    //     *known-ancestor* override (FP-safe: an unindexed ancestor ⇒ skip).
    if md.modifiers.visibility != Some(php_ast::Visibility::Private) {
        let is_final = class.modifiers.is_final || md.modifiers.is_final;
        if !is_final {
            let name = fa.interner.resolve(md.name);
            if !fa.check_too_wide_return_public || !method_overrides_ancestor(fa, class_fqn, name) {
                return;
            }
        }
    }
    let Some(body) = &md.body else { return }; // abstract/interface — nothing to analyze
    let Some(ret) = &md.return_type else { return };
    let name = fa.interner.resolve(md.name);
    let desc = format!("Method {class_desc}::{name}()");
    out.extend(check_returns(fa, scope, ret, body, &desc, ret.span));
}

/// Whether `class_fqn` declares `name` as an override of a method already
/// declared by a *known* (indexed) ancestor class or interface. FP-safe: an
/// unindexed ancestor yields `false` (we can't confirm the override).
fn method_overrides_ancestor(fa: &FileAnalysis, class_fqn: &str, name: &str) -> bool {
    let Some(refl) = fa.reflection.class(class_fqn) else {
        return false;
    };
    refl.parents
        .iter()
        .chain(refl.interfaces.iter())
        .any(|t| match t {
            Type::Named { fqn, .. } => fa.reflection.find_method(fqn, name).is_some(),
            _ => false,
        })
}

// ---------------------------------------------------------------------------
// TooWideClosureReturnTypehintRule
// ---------------------------------------------------------------------------

fn run_closure_return(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        let prog = Program {
            stmts: region.to_vec(),
        };
        walk::for_each_expr(&prog, &mut |e| {
            if let ExprKind::Closure(cl) = &e.kind {
                check_closure(cl, fa, scope, e.span, &mut out);
            }
        });
    });
    out
}

fn check_closure(
    cl: &ClosureExpr,
    fa: &FileAnalysis,
    scope: &Scope,
    span: php_span::Span,
    out: &mut Vec<Diagnostic>,
) {
    let Some(ret) = &cl.return_type else { return };
    let Some(members) = union_members(scope, ret) else {
        return;
    };
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
    out.extend(flag_unused_members(
        fa.reflection,
        &members,
        &return_types,
        may_fall_through,
        "Anonymous function",
        span,
    ));
}

/// A fresh inference context seeded with `params`' declared types (untyped →
/// `mixed`), used to collect a closure/arrow-fn's returned types while threading
/// its own flow environment (the too-wide-return check needs the return set, not
/// per-node lookups).
fn local_ctx<'a>(fa: &'a FileAnalysis, scope: &'a Scope, params: &[Param]) -> TypeCtx<'a> {
    let mut ctx = TypeCtx::new(fa.reflection, scope, fa.interner);
    for p in params {
        let ty =
            p.ty.as_ref()
                .map(|t| resolve_ast_type(scope, t))
                .unwrap_or(Type::Mixed);
        ctx.vars.insert(fa.interner.resolve(p.name).to_string(), ty);
    }
    ctx
}

/// Collect returned types from a closure body, threading the flow environment so
/// a returned local carries its assigned type (mirrors `return_type.rs`).
fn collect_returns_ctx(
    body: &[Stmt],
    ctx: &mut TypeCtx,
    out: &mut Vec<Type>,
    bare_return: &mut bool,
) {
    for st in body {
        collect_returns_ctx_stmt(st, ctx, out, bare_return);
    }
}

fn collect_returns_ctx_stmt(
    st: &Stmt,
    ctx: &mut TypeCtx,
    out: &mut Vec<Type>,
    bare_return: &mut bool,
) {
    match &st.kind {
        StmtKind::Return(Some(e)) => out.push(ctx.infer(e)),
        StmtKind::Return(None) => *bare_return = true,
        StmtKind::Expr(e) => {
            ctx.apply_expr(e);
        }
        StmtKind::Block(b) => collect_returns_ctx(b, ctx, out, bare_return),
        StmtKind::If {
            cond,
            then,
            elseifs,
            els,
        } => {
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
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
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
        let prog = Program {
            stmts: region.to_vec(),
        };
        walk::for_each_expr(&prog, &mut |e| {
            if let ExprKind::ArrowFn(af) = &e.kind {
                check_arrow(af, fa, scope, e.span, &mut out);
            }
        });
    });
    out
}

fn check_arrow(
    af: &ArrowFn,
    fa: &FileAnalysis,
    scope: &Scope,
    span: php_span::Span,
    out: &mut Vec<Diagnostic>,
) {
    let Some(ret) = &af.return_type else { return };
    // An arrow fn's body is a single expression that is its return value;
    // `yield`/`yield from` make it a generator — bail.
    if matches!(
        af.body.kind,
        ExprKind::Yield { .. } | ExprKind::YieldFrom(_)
    ) {
        return;
    }
    let Some(members) = union_members(scope, ret) else {
        return;
    };
    // The type map doesn't reach inside arrow-fns; infer the body locally.
    let ctx = local_ctx(fa, scope, &af.params);
    let rt = ctx.infer(&af.body);
    if is_unknown_ish(&rt) {
        return;
    }
    // An arrow fn always returns its expression (no fall-through, no bare return).
    out.extend(flag_unused_members(
        fa.reflection,
        &members,
        &[rt],
        false,
        "Anonymous function",
        span,
    ));
}

// ---------------------------------------------------------------------------
// TooWidePropertyTypeRule (private properties, conservative assignment slice)
// ---------------------------------------------------------------------------

fn run_property_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            collect_property_decls(st, fa, scope, &mut out);
        }
    });
    out
}

fn collect_property_decls(st: &Stmt, fa: &FileAnalysis, scope: &Scope, out: &mut Vec<Diagnostic>) {
    match &st.kind {
        StmtKind::Class(c) => check_class_properties(c, fa, scope, out),
        StmtKind::Block(b) | StmtKind::Namespace { body: Some(b), .. } => {
            for s in b {
                collect_property_decls(s, fa, scope, out);
            }
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            collect_property_decls(then, fa, scope, out);
            for ei in elseifs {
                collect_property_decls(&ei.body, fa, scope, out);
            }
            if let Some(e) = els {
                collect_property_decls(e, fa, scope, out);
            }
        }
        StmtKind::Function(f) => {
            for s in &f.body {
                collect_property_decls(s, fa, scope, out);
            }
        }
        _ => {}
    }
}

fn check_class_properties(
    c: &ClassDecl,
    fa: &FileAnalysis,
    scope: &Scope,
    out: &mut Vec<Diagnostic>,
) {
    // PHPStan's rule handles native class properties. Traits are skipped because
    // the real declaring class is use-site dependent; interfaces/enums cannot
    // have ordinary writable private properties in the same sense.
    if c.kind != php_ast::ClassKind::Class {
        return;
    }
    if c.members.iter().any(|m| matches!(m, Member::TraitUse(_))) {
        return;
    }

    let Some(class_name) = c.name else {
        return;
    };
    let class_fqn = scope.qualify(fa.interner.resolve(class_name));
    for member in &c.members {
        let Member::Property(pd) = member else {
            continue;
        };
        check_property_decl(c, pd, &class_fqn, fa, scope, out);
    }
}

fn check_property_decl(
    c: &ClassDecl,
    pd: &PropertyDecl,
    class_fqn: &str,
    fa: &FileAnalysis,
    scope: &Scope,
    out: &mut Vec<Diagnostic>,
) {
    if pd.modifiers.visibility != Some(php_ast::Visibility::Private) {
        return;
    }
    let Some(declared) = &pd.ty else {
        return;
    };
    let Some(members) = union_members(scope, declared) else {
        return;
    };

    for elem in &pd.props {
        check_property_elem(c, pd, elem, class_fqn, fa, scope, declared, &members, out);
    }
}

#[allow(clippy::too_many_arguments)]
fn check_property_elem(
    c: &ClassDecl,
    pd: &PropertyDecl,
    elem: &PropElem,
    class_fqn: &str,
    fa: &FileAnalysis,
    scope: &Scope,
    declared: &AstType,
    members: &[Type],
    out: &mut Vec<Diagnostic>,
) {
    // Property hooks and promoted properties have their own specialised
    // PHPStan rules / reflection shape. Stay on plain declared properties here.
    if elem.hooks.is_some() {
        return;
    }
    let Some(default) = &elem.default else {
        return;
    };

    let prop_name = fa.interner.resolve(elem.name);
    let is_static = pd.modifiers.is_static;
    let mut assigned = Vec::new();
    assigned.push(fa.type_of_isolated_in(scope, Some(class_fqn), default));

    let Some(mut writes) = collect_property_writes(c, class_fqn, prop_name, is_static, fa, scope)
    else {
        return;
    };
    assigned.append(&mut writes);

    if assigned
        .iter()
        .any(|t| is_unknown_ish(t) || matches!(t, Type::Never))
    {
        return;
    }

    let mut atoms = Vec::new();
    for ty in &assigned {
        flatten_type_atoms(ty, &mut atoms);
    }

    let kind = if is_static {
        "Static property"
    } else {
        "Property"
    };
    let original = Type::union(members.to_vec());
    for member in members {
        let used = atoms
            .iter()
            .any(|assigned_ty| crate::is_assignable(fa.reflection, assigned_ty, member));
        if used {
            continue;
        }
        out.push(
            Diagnostic::error(
                declared.span,
                format!(
                    "{kind} {class_fqn}::${prop_name} ({original}) is never assigned {member} so it can be removed from the property type."
                ),
            )
            .with_code("property.unusedType"),
        );
    }
}

fn collect_property_writes(
    c: &ClassDecl,
    class_fqn: &str,
    prop_name: &str,
    is_static: bool,
    fa: &FileAnalysis,
    scope: &Scope,
) -> Option<Vec<Type>> {
    let mut out = Vec::new();
    let mut opaque = false;
    let mut ctx = TypeCtx::new(fa.reflection, scope, fa.interner);
    ctx.class = Some(class_fqn.to_string());

    for member in &c.members {
        match member {
            Member::Method(md) => {
                let Some(body) = &md.body else {
                    continue;
                };
                for p in &md.params {
                    let ty =
                        p.ty.as_ref()
                            .map(|t| resolve_ast_type(scope, t))
                            .unwrap_or(Type::Mixed);
                    ctx.vars.insert(fa.interner.resolve(p.name).to_string(), ty);
                }
                for st in body {
                    scan_property_writes_stmt(
                        st,
                        class_fqn,
                        prop_name,
                        is_static,
                        fa,
                        &ctx,
                        &mut out,
                        &mut opaque,
                    );
                }
                ctx.vars.clear();
            }
            Member::Property(pd) => {
                for elem in &pd.props {
                    if let Some(hooks) = &elem.hooks {
                        for hook in hooks {
                            scan_property_writes_hook(
                                hook,
                                class_fqn,
                                prop_name,
                                is_static,
                                fa,
                                &ctx,
                                &mut out,
                                &mut opaque,
                            );
                        }
                    }
                }
            }
            _ => {}
        }
    }

    (!opaque).then_some(out)
}

#[allow(clippy::too_many_arguments)]
fn scan_property_writes_stmt(
    st: &Stmt,
    class_fqn: &str,
    prop_name: &str,
    is_static: bool,
    fa: &FileAnalysis,
    ctx: &TypeCtx<'_>,
    out: &mut Vec<Type>,
    opaque: &mut bool,
) {
    walk::for_each_expr_in_scope(st, &mut |e| {
        scan_property_write_expr(e, class_fqn, prop_name, is_static, fa, ctx, out, opaque);
    });
}

#[allow(clippy::too_many_arguments)]
fn scan_property_writes_hook(
    hook: &PropertyHook,
    class_fqn: &str,
    prop_name: &str,
    is_static: bool,
    fa: &FileAnalysis,
    ctx: &TypeCtx<'_>,
    out: &mut Vec<Type>,
    opaque: &mut bool,
) {
    if let Some(params) = &hook.params {
        if params
            .iter()
            .any(|p| fa.interner.resolve(p.name) == prop_name)
        {
            // A set hook parameter named like the property is harmless, but hook
            // bodies are a separate PHPStan branch; stay conservative.
            *opaque = true;
            return;
        }
    }
    match &hook.body {
        HookBody::Block(stmts) => {
            for st in stmts {
                scan_property_writes_stmt(
                    st, class_fqn, prop_name, is_static, fa, ctx, out, opaque,
                );
            }
        }
        HookBody::Short(e) => {
            walk::for_each_subexpr(e, &mut |sub| {
                scan_property_write_expr(
                    sub, class_fqn, prop_name, is_static, fa, ctx, out, opaque,
                );
            });
        }
        HookBody::Abstract => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn scan_property_write_expr(
    e: &Expr,
    class_fqn: &str,
    prop_name: &str,
    is_static: bool,
    fa: &FileAnalysis,
    ctx: &TypeCtx<'_>,
    out: &mut Vec<Type>,
    opaque: &mut bool,
) {
    if matches!(
        e.kind,
        ExprKind::Closure(_) | ExprKind::ArrowFn(_) | ExprKind::NewAnon { .. }
    ) {
        *opaque = true;
        return;
    }

    match &e.kind {
        ExprKind::Assign { target, rhs } => {
            match property_write_match(target, class_fqn, prop_name, is_static, fa, ctx) {
                WriteMatch::ThisProperty => out.push(fa.type_of(rhs)),
                WriteMatch::MaybeThisProperty => *opaque = true,
                WriteMatch::Other => {}
            }
        }
        ExprKind::AssignRef { target, .. } | ExprKind::AssignOp { target, .. } => {
            match property_write_match(target, class_fqn, prop_name, is_static, fa, ctx) {
                WriteMatch::ThisProperty | WriteMatch::MaybeThisProperty => *opaque = true,
                WriteMatch::Other => {}
            }
        }
        _ => {}
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum WriteMatch {
    ThisProperty,
    MaybeThisProperty,
    Other,
}

fn property_write_match(
    target: &Expr,
    class_fqn: &str,
    prop_name: &str,
    is_static: bool,
    fa: &FileAnalysis,
    ctx: &TypeCtx<'_>,
) -> WriteMatch {
    match &target.kind {
        ExprKind::Prop { base, name, .. } => {
            let Some(written_name) = member_name_if_static(name, fa) else {
                return if receiver_may_be_this(base, class_fqn, fa, ctx) {
                    WriteMatch::MaybeThisProperty
                } else {
                    WriteMatch::Other
                };
            };
            if written_name != prop_name {
                return WriteMatch::Other;
            }
            if is_static {
                return WriteMatch::MaybeThisProperty;
            }
            if receiver_is_this(base, class_fqn, fa, ctx) {
                WriteMatch::ThisProperty
            } else if receiver_may_be_this(base, class_fqn, fa, ctx) {
                WriteMatch::MaybeThisProperty
            } else {
                WriteMatch::Other
            }
        }
        ExprKind::StaticProp { class, name } => {
            let Some(written_name) = static_property_name_if_static(name, fa) else {
                return if static_class_may_be_current(class, class_fqn, ctx) {
                    WriteMatch::MaybeThisProperty
                } else {
                    WriteMatch::Other
                };
            };
            if written_name != prop_name {
                return WriteMatch::Other;
            }
            if !is_static {
                return WriteMatch::MaybeThisProperty;
            }
            match static_class_matches_current(class, class_fqn, ctx) {
                Some(true) => WriteMatch::ThisProperty,
                Some(false) => WriteMatch::Other,
                None => WriteMatch::MaybeThisProperty,
            }
        }
        _ => WriteMatch::Other,
    }
}

fn member_name_if_static(name: &MemberName, fa: &FileAnalysis) -> Option<String> {
    match name {
        MemberName::Ident(sym) => Some(fa.interner.resolve(*sym).to_string()),
        MemberName::Var(_) | MemberName::Expr(_) => None,
    }
}

fn static_property_name_if_static(name: &MemberName, fa: &FileAnalysis) -> Option<String> {
    match name {
        // `C::$p` is usually `Var`, but some parser paths produce `Ident` for
        // statically-known member names. Both are literal enough for this rule.
        MemberName::Ident(sym) | MemberName::Var(sym) => {
            Some(fa.interner.resolve(*sym).to_string())
        }
        MemberName::Expr(_) => None,
    }
}

fn receiver_is_this(base: &Expr, class_fqn: &str, fa: &FileAnalysis, ctx: &TypeCtx<'_>) -> bool {
    match &base.kind {
        ExprKind::Variable(sym) if fa.interner.resolve(*sym) == "this" => true,
        _ => members::sole_class(&ctx.infer(base))
            .is_some_and(|fqn| symbols::same_fqn(&fqn, class_fqn)),
    }
}

fn receiver_may_be_this(
    base: &Expr,
    class_fqn: &str,
    fa: &FileAnalysis,
    ctx: &TypeCtx<'_>,
) -> bool {
    if receiver_is_this(base, class_fqn, fa, ctx) {
        return true;
    }
    matches!(
        ctx.infer(base),
        Type::Mixed | Type::ExplicitMixed | Type::Unknown(_)
    )
}

fn static_class_matches_current(class: &Expr, class_fqn: &str, ctx: &TypeCtx<'_>) -> Option<bool> {
    match &class.kind {
        ExprKind::Name(n) => match ctx.scope.resolve_class(n) {
            Resolution::Fqn(fqn) => Some(symbols::same_fqn(&fqn, class_fqn)),
            Resolution::LateStatic(s) if matches!(s.as_str(), "self" | "static") => Some(true),
            Resolution::LateStatic(_) => Some(false),
            Resolution::BuiltinType(_) | Resolution::Fallback { .. } => Some(false),
        },
        _ => None,
    }
}

fn static_class_may_be_current(class: &Expr, class_fqn: &str, ctx: &TypeCtx<'_>) -> bool {
    static_class_matches_current(class, class_fqn, ctx).unwrap_or(true)
}

// ---------------------------------------------------------------------------
// TooWideFunction/MethodParameterOutTypeRule — explicit @param-out subset
// ---------------------------------------------------------------------------

fn run_function_parameter_out_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            collect_function_param_out_decls(st, fa, scope, &mut out);
        }
    });
    out
}

fn collect_function_param_out_decls(
    st: &Stmt,
    fa: &FileAnalysis,
    scope: &Scope,
    out: &mut Vec<Diagnostic>,
) {
    match &st.kind {
        StmtKind::Function(f) => {
            check_function_param_out(f, fa, scope, out);
            for inner in &f.body {
                collect_function_param_out_decls(inner, fa, scope, out);
            }
        }
        StmtKind::Block(b) | StmtKind::Namespace { body: Some(b), .. } => {
            for s in b {
                collect_function_param_out_decls(s, fa, scope, out);
            }
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            collect_function_param_out_decls(then, fa, scope, out);
            for ei in elseifs {
                collect_function_param_out_decls(&ei.body, fa, scope, out);
            }
            if let Some(e) = els {
                collect_function_param_out_decls(e, fa, scope, out);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => collect_function_param_out_decls(body, fa, scope, out),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for s in body {
                collect_function_param_out_decls(s, fa, scope, out);
            }
            for c in catches {
                for s in &c.body {
                    collect_function_param_out_decls(s, fa, scope, out);
                }
            }
            if let Some(f) = finally {
                for s in f {
                    collect_function_param_out_decls(s, fa, scope, out);
                }
            }
        }
        _ => {}
    }
}

fn check_function_param_out(
    f: &FunctionDecl,
    fa: &FileAnalysis,
    scope: &Scope,
    out: &mut Vec<Diagnostic>,
) {
    let refl = fa.reflect_function(scope, f);
    let templates = crate::doctags::templates(f.doc.as_deref());
    let desc = format!("Function {}()", refl.fqn);
    check_param_out_too_wide_body(
        scope,
        f.doc.as_deref(),
        &templates,
        &f.body,
        &f.params,
        &refl.params,
        None,
        &desc,
        fa,
        out,
    );
}

fn run_method_parameter_out_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            collect_method_param_out_decls(st, fa, scope, &mut out);
        }
    });
    out
}

fn collect_method_param_out_decls(
    st: &Stmt,
    fa: &FileAnalysis,
    scope: &Scope,
    out: &mut Vec<Diagnostic>,
) {
    match &st.kind {
        StmtKind::Class(c) => check_class_param_out_methods(c, fa, scope, out),
        StmtKind::Block(b) | StmtKind::Namespace { body: Some(b), .. } => {
            for s in b {
                collect_method_param_out_decls(s, fa, scope, out);
            }
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            collect_method_param_out_decls(then, fa, scope, out);
            for ei in elseifs {
                collect_method_param_out_decls(&ei.body, fa, scope, out);
            }
            if let Some(e) = els {
                collect_method_param_out_decls(e, fa, scope, out);
            }
        }
        StmtKind::Function(f) => {
            for s in &f.body {
                collect_method_param_out_decls(s, fa, scope, out);
            }
        }
        _ => {}
    }
}

fn check_class_param_out_methods(
    c: &ClassDecl,
    fa: &FileAnalysis,
    scope: &Scope,
    out: &mut Vec<Diagnostic>,
) {
    if c.kind == php_ast::ClassKind::Trait {
        return;
    }
    let Some(class_name) = c.name else {
        return;
    };
    let class_fqn = scope.qualify(fa.interner.resolve(class_name));
    let class_refl = fa.reflect_class(scope, &class_fqn, c);
    let class_templates = crate::doctags::templates(c.doc.as_deref());
    for member in &c.members {
        let Member::Method(md) = member else {
            continue;
        };
        if md.modifiers.visibility != Some(php_ast::Visibility::Private) {
            continue;
        }
        let Some(body) = &md.body else {
            continue;
        };
        let method_name = fa.interner.resolve(md.name);
        let Some(method_refl) = class_refl
            .methods
            .iter()
            .find(|r| !r.magic && r.name.eq_ignore_ascii_case(method_name))
        else {
            continue;
        };
        let templates = crate::doctags::combined_templates(&class_templates, md.doc.as_deref());
        let desc = format!("Method {}::{}()", class_refl.fqn, method_refl.name);
        check_param_out_too_wide_body(
            scope,
            md.doc.as_deref(),
            &templates,
            body,
            &md.params,
            &method_refl.params,
            Some(class_refl.fqn.as_str()),
            &desc,
            fa,
            out,
        );
    }
}

#[allow(clippy::too_many_arguments)]
fn check_param_out_too_wide_body(
    scope: &Scope,
    doc: Option<&str>,
    templates: &[String],
    body: &[Stmt],
    ast_params: &[Param],
    params: &[ParamReflection],
    class_fqn: Option<&str>,
    function_description: &str,
    fa: &FileAnalysis,
    out: &mut Vec<Diagnostic>,
) {
    let param_outs = param_out::param_out_types(scope, doc, templates);
    if param_outs.is_empty() {
        return;
    }
    let Some(final_vars) = param_out::straight_line_final_vars(body, params, scope, class_fqn, fa)
    else {
        return;
    };

    for po in param_outs {
        if param_out::type_is_uncertain(&po.ty) {
            continue;
        }
        let Some(param) = params
            .iter()
            .find(|p| p.name == po.name && p.by_ref && !p.variadic)
        else {
            continue;
        };
        let Some(final_ty) = final_vars.get(&po.name) else {
            continue;
        };
        if param_out::type_is_uncertain(final_ty) {
            continue;
        }
        out.extend(param_out_unused_type_errors(
            &po.ty,
            final_ty,
            function_description,
            &param.name,
            param_out::param_decl_span(ast_params, &param.name, fa.interner)
                .unwrap_or_else(|| body.first().map_or(php_span::Span::at(0), |s| s.span)),
            fa,
        ));
    }
}

fn param_out_unused_type_errors(
    declared: &Type,
    actual: &Type,
    function_description: &str,
    param_name: &str,
    span: php_span::Span,
    fa: &FileAnalysis,
) -> Vec<Diagnostic> {
    let mut atoms = Vec::new();
    flatten_type_atoms(actual, &mut atoms);
    if atoms.is_empty() || atoms.iter().any(param_out::type_is_uncertain) {
        return Vec::new();
    }

    if matches!(declared, Type::Bool) {
        let all_true = atoms.iter().all(|t| matches!(t, Type::True));
        let all_false = atoms.iter().all(|t| matches!(t, Type::False));
        let (never, narrowed) = if all_true {
            ("false", "true")
        } else if all_false {
            ("true", "false")
        } else {
            return Vec::new();
        };
        return vec![
            Diagnostic::error(
                span,
                format!(
                    "{function_description} never assigns {never} to &${param_name} so the @param-out type can be changed to {narrowed}."
                ),
            )
            .with_code("paramOut.tooWideBool"),
        ];
    }

    let mut members = Vec::new();
    flatten_type_atoms(declared, &mut members);
    if members.len() < 2 {
        return Vec::new();
    }

    let mut out = Vec::new();
    for member in members {
        let used = atoms
            .iter()
            .any(|actual_ty| crate::is_assignable(fa.reflection, actual_ty, &member));
        if used {
            continue;
        }
        out.push(
            Diagnostic::error(
                span,
                format!(
                    "{function_description} never assigns {} to &${param_name} so it can be removed from the @param-out type.",
                    param_out::phpstan_type(&member),
                ),
            )
            .with_code("paramOut.unusedType"),
        );
    }
    out
}

// ---------------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------------

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "property.unusedType",
        level: 4,
        run: run_property_type,
    },
    RuleEntry {
        name: "paramOut.unusedType/function",
        level: 4,
        run: run_function_parameter_out_type,
    },
    RuleEntry {
        name: "paramOut.unusedType/method",
        level: 4,
        run: run_method_parameter_out_type,
    },
    RuleEntry {
        name: "return.unusedType/function",
        level: 4,
        run: run_function_return,
    },
    RuleEntry {
        name: "return.unusedType/method",
        level: 4,
        run: run_method_return,
    },
    RuleEntry {
        name: "return.unusedType/closure",
        level: 4,
        run: run_closure_return,
    },
    RuleEntry {
        name: "return.unusedType/arrow",
        level: 4,
        run: run_arrow_return,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{codes, codes_strict, codes_with, run};

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
        let src =
            "<?php function f(bool $c): int|string|null { if ($c) { return 1; } return null; }";
        assert_eq!(
            msgs(src, run_function_return),
            ["Function f() never returns string so it can be removed from the return type."]
        );
    }

    // --- parameter-out ---------------------------------------------------

    #[test]
    fn function_param_out_never_assigns_null_is_flagged() {
        let src = "<?php /** @param-out string|null $out */ function f(?string &$out): void { $out = 'x'; }";
        let diags = run(src, run_function_parameter_out_type);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["paramOut.unusedType"]
        );
        assert_eq!(
            diags[0].message,
            "Function f() never assigns null to &$out so it can be removed from the @param-out type."
        );
    }

    #[test]
    fn function_param_out_bool_can_be_narrowed_to_true() {
        let src = "<?php /** @param-out bool $out */ function f(bool &$out): void { $out = true; }";
        let diags = run(src, run_function_parameter_out_type);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["paramOut.tooWideBool"]
        );
        assert_eq!(
            diags[0].message,
            "Function f() never assigns false to &$out so the @param-out type can be changed to true."
        );
    }

    #[test]
    fn function_param_out_all_members_possible_is_clean() {
        let src = "<?php /** @param-out string|null $out */ function f(?string &$out): void {}";
        assert!(codes(src, run_function_parameter_out_type).is_empty());
    }

    #[test]
    fn function_param_out_branch_is_deferred() {
        let src = "<?php /** @param-out string|null $out */ function f(?string &$out, bool $c): void { if ($c) { $out = 'x'; } }";
        assert!(codes(src, run_function_parameter_out_type).is_empty());
    }

    #[test]
    fn method_param_out_private_never_assigns_null_is_flagged() {
        let src = "<?php class C { /** @param-out string|null $out */ private function m(?string &$out): void { $out = 'x'; } }";
        let diags = run(src, run_method_parameter_out_type);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["paramOut.unusedType"]
        );
        assert_eq!(
            diags[0].message,
            "Method C::m() never assigns null to &$out so it can be removed from the @param-out type."
        );
    }

    #[test]
    fn method_param_out_public_is_deferred() {
        let src = "<?php class C { /** @param-out string|null $out */ public function m(?string &$out): void { $out = 'x'; } }";
        assert!(codes(src, run_method_parameter_out_type).is_empty());
    }

    #[test]
    fn method_param_out_variadic_is_deferred() {
        let src = "<?php class C { /** @param-out string|null $out */ private function m(string &...$out): void { $out = ['x']; } }";
        assert!(codes(src, run_method_parameter_out_type).is_empty());
    }

    // --- properties ------------------------------------------------------

    #[test]
    fn private_property_default_never_assigns_union_member_is_flagged() {
        let src = "<?php class C { private int|string $p = 1; }";
        assert_eq!(
            msgs(src, run_property_type),
            ["Property C::$p (int|string) is never assigned string so it can be removed from the property type."]
        );
    }

    #[test]
    fn private_property_direct_writes_are_counted() {
        let src = "<?php class C { private int|string|null $p = 1; function set(): void { $this->p = 'x'; } }";
        assert_eq!(
            msgs(src, run_property_type),
            ["Property C::$p (int|string|null) is never assigned null so it can be removed from the property type."]
        );
    }

    #[test]
    fn private_static_property_direct_writes_are_counted() {
        let src =
            "<?php class C { private static int|string|null $p = 1; function set(): void { self::$p = 'x'; } }";
        assert_eq!(
            msgs(src, run_property_type),
            ["Static property C::$p (int|string|null) is never assigned null so it can be removed from the property type."]
        );
    }

    #[test]
    fn public_property_is_skipped() {
        let src = "<?php class C { public int|string $p = 1; }";
        assert!(codes(src, run_property_type).is_empty());
    }

    #[test]
    fn property_without_default_is_skipped() {
        let src = "<?php class C { private int|string $p; }";
        assert!(codes(src, run_property_type).is_empty());
    }

    #[test]
    fn dynamic_property_write_bails() {
        let src = "<?php class C { private int|string $p = 1; function set(string $name): void { $this->{$name} = 'x'; } }";
        assert!(codes(src, run_property_type).is_empty());
    }

    #[test]
    fn opaque_closure_in_class_bails() {
        let src = "<?php class C { private int|string $p = 1; function set(): void { $f = function (): void { $this->p = 'x'; }; } }";
        assert!(codes(src, run_property_type).is_empty());
    }

    #[test]
    fn class_using_trait_is_skipped() {
        let src = "<?php trait T { function set(): void { $this->p = 'x'; } } class C { use T; private int|string $p = 1; }";
        assert!(codes(src, run_property_type).is_empty());
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

    #[test]
    fn final_public_method_flagged_regardless_of_flag() {
        // A final method can't be overridden, so phpstan checks it by default.
        let src = "<?php class C { final public function m(): ?int { return 1; } }";
        assert_eq!(codes(src, run_method_return), ["return.unusedType"]);
        // Still flagged with the public-methods flag off (final is unconditional).
        assert_eq!(
            codes_with(src, run_method_return, |fa| fa
                .check_too_wide_return_public =
                false),
            ["return.unusedType"]
        );
    }

    #[test]
    fn public_method_in_final_class_flagged() {
        let src = "<?php final class C { public function m(): ?int { return 1; } }";
        assert_eq!(codes(src, run_method_return), ["return.unusedType"]);
    }

    #[test]
    fn non_final_override_flagged_only_with_flag() {
        let src = "<?php
            class Base { public function m(): ?int { return null; } }
            class C extends Base { public function m(): ?int { return 1; } }";
        // With the flag on, the override (narrowing a known ancestor) is checked.
        assert_eq!(codes_strict(src, run_method_return), ["return.unusedType"]);
        // ...and it is off by default, as in any run that does not configure it.
        assert!(codes(src, run_method_return).is_empty());
    }

    #[test]
    fn non_final_first_declaration_skipped_even_with_flag() {
        // No ancestor declares m(), so a subclass could justify the wider type.
        let src = "<?php class C { public function m(): ?int { return 1; } }";
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
        let src =
            "<?php $f = function (bool $c): int|string { if ($c) { return 1; } return 'x'; };";
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
