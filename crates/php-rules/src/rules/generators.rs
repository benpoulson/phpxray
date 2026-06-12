//! phpstan category **Generators** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Generators/` — 3 rule(s) at level 3.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! A function containing `yield`/`yield from` is a *generator*: at runtime PHP
//! returns a `Generator` regardless of the function body, so the declared return
//! type must be one of `Generator`/`Iterator`/`Traversable`/`iterable`. These
//! rules check that, plus that `yield from` is given something iterable.
//!
//! Implemented (all level 3):
//! - **YieldInGeneratorRule** (`generator.outOfFunction` / `generator.returnType`)
//!   — `yield`/`yield from` used at file top level (not inside any function), and
//!   `yield` inside a function whose declared return type is provably *not* a
//!   generator-compatible type.
//! - **YieldFromTypeRule** (`generator.nonIterable`) — `yield from <expr>` where
//!   `<expr>`'s inferred type is concrete and provably non-iterable.
//! - **YieldTypeRule** (`generator.keyType` / `generator.valueType` /
//!   `generator.void`) — plain `yield` key/value checks against declared
//!   generator-family generics when those slots are modeled concretely, plus
//!   result-of-`yield` usage when declared `TSend` is `void` and the AST parent
//!   context clearly consumes the expression.
//!
//! Deferred:
//! - The `generator.keyType` / `generator.valueType` / `generator.sendType` /
//!   `generator.void` parts of `YieldFromTypeRule` — `yield from` needs delegated
//!   iterable key/value and `TSend` template extraction from the yielded-from
//!   expression. We only do the non-iterable argument check for now.
//! - `YieldTypeRule` template-bound/maybe diagnostics and exact shape reasons —
//!   our assignability relation is deliberately lenient, so these under-report.

use crate::{FileAnalysis, RuleEntry};
use php_ast::{
    walk, Arg, ArrayItem, ArrowFn, ClassDecl, ClosureExpr, Expr, ExprKind, FunctionDecl, Member,
    MemberName, MethodDecl, Stmt, StmtKind,
};
use php_diagnostics::Diagnostic;
use php_reflect::resolve_ast_type;
use php_resolve::{for_each_region, Scope};
use php_types::Type;

// ---------------------------------------------------------------------------
// Generator-compatible return types
// ---------------------------------------------------------------------------

/// Whether a *resolved* declared return type allows a generator body. PHP wraps
/// any yielding function in a `Generator`, which is an `Iterator`/`Traversable`
/// and satisfies `iterable`. We are FP-safe: anything we don't recognise as a
/// definite non-generator type (mixed/unknown/union/nullable/object/unindexed
/// class) is treated as "compatible" so we never wrongly flag.
fn return_type_allows_generator(t: &Type) -> bool {
    match t {
        // Top / unknown / anything we can't pin down → assume compatible.
        Type::Mixed | Type::ExplicitMixed | Type::Unknown(_) => true,
        // Iterable shapes are fine.
        Type::Iterable(_) | Type::Array(_) | Type::List(_) => true,
        // The generator-family classes (and any other class — it may be an
        // unindexed iterator, so don't claim incompatibility for objects).
        Type::Named { .. } | Type::Object => true,
        Type::SelfType | Type::StaticType | Type::Parent | Type::TemplateVar(_) => true,
        // A union/nullable is compatible if *any* member is compatible (the
        // generator value flows into that member). Be lenient.
        Type::Union(members) => members.iter().any(return_type_allows_generator),
        Type::Nullable(inner) => return_type_allows_generator(inner),
        Type::Intersection(members) => members.iter().any(return_type_allows_generator),
        // Concrete, known non-iterable scalars / void / never: NOT compatible.
        _ => false,
    }
}

/// Whether a *resolved* type is provably **not** iterable (for `yield from`).
/// FP-safe: only concrete, known scalar/null/void/never types qualify; objects,
/// classes, unions, mixed, unknown all yield `false` (might be iterable).
fn definitely_not_iterable(t: &Type) -> bool {
    match t {
        Type::Null
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Int
        | Type::Float
        | Type::String
        | Type::Resource
        | Type::Void
        | Type::LiteralInt(_)
        | Type::LiteralString(_) => true,
        // A union is not-iterable only if *every* member is not-iterable.
        Type::Union(members) => !members.is_empty() && members.iter().all(definitely_not_iterable),
        _ => false,
    }
}

fn definitely_iterable(t: &Type) -> bool {
    match t {
        Type::Array(_) | Type::List(_) | Type::Iterable(_) | Type::Shape { .. } => true,
        Type::Named { fqn, .. } => {
            fqn.eq_ignore_ascii_case("Generator")
                || fqn.eq_ignore_ascii_case("Iterator")
                || fqn.eq_ignore_ascii_case("Traversable")
        }
        Type::Union(parts) => !parts.is_empty() && parts.iter().all(definitely_iterable),
        Type::Nullable(inner) => definitely_iterable(inner),
        _ => false,
    }
}

fn maybe_iterable(t: &Type) -> bool {
    let Type::Union(parts) = t else {
        return false;
    };
    if parts.is_empty() {
        return false;
    }
    let mut yes = false;
    let mut no = false;
    for part in parts.iter() {
        if definitely_iterable(part) {
            yes = true;
        } else if definitely_not_iterable(part) {
            no = true;
        } else {
            return false;
        }
    }
    yes && no
}

// ---------------------------------------------------------------------------
// Finding the yields that belong to a given scope
// ---------------------------------------------------------------------------

/// Collect every `yield` / `yield from` expression that belongs directly to the
/// statement list `body` (i.e. not nested inside a closure / arrow fn / nested
/// function), invoking `f` on each.
fn yields_in_body(body: &[Stmt], f: &mut impl FnMut(&Expr)) {
    for st in body {
        walk::for_each_expr_in_scope(st, &mut |e| {
            if matches!(e.kind, ExprKind::Yield { .. } | ExprKind::YieldFrom(_)) {
                f(e);
            }
        });
    }
}

/// Whether a statement list contains a yield in its own scope (i.e. is a
/// generator). Cheap early-out for the return-type rule.
fn is_generator_body(body: &[Stmt]) -> bool {
    let mut found = false;
    yields_in_body(body, &mut |_| found = true);
    found
}

// ---------------------------------------------------------------------------
// Visiting every function-like scope with its resolved return type
// ---------------------------------------------------------------------------

/// A function-like scope: its body statements, declaring scope, and resolved
/// declared return type (`None` when no return type is written — then the rules
/// stay silent).
struct FnScope<'a> {
    body: &'a [Stmt],
    return_type: Option<Type>,
    scope: &'a Scope,
}

/// Walk every function-like scope in the file (top-level functions, methods,
/// closures, arrow fns — including nested ones), resolving each declared return
/// type against the scope it is written in, and invoke `f` on each.
fn for_each_fn_scope(fa: &FileAnalysis, mut f: impl FnMut(&FnScope)) {
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            visit_stmt(st, fa, scope, &mut f);
        }
    });
}

fn visit_stmt(st: &Stmt, fa: &FileAnalysis, scope: &Scope, f: &mut impl FnMut(&FnScope)) {
    match &st.kind {
        StmtKind::Function(fd) => visit_function(fd, fa, scope, f),
        StmtKind::Class(c) => visit_class(c, fa, scope, f),
        StmtKind::Namespace { body: Some(b), .. } => {
            for s in b {
                visit_stmt(s, fa, scope, f);
            }
        }
        _ => {
            // Closures / arrow fns can appear in any nested expression of a
            // top-level statement; scan this statement's own-scope expressions.
            scan_exprs_for_inline_fns(st, fa, scope, f);
        }
    }
}

/// Find closures / arrow fns inside the *own-scope* expressions of `st` (the
/// global region is the enclosing scope) and visit them.
fn scan_exprs_for_inline_fns(
    st: &Stmt,
    fa: &FileAnalysis,
    scope: &Scope,
    f: &mut impl FnMut(&FnScope),
) {
    walk::for_each_expr_in_scope(st, &mut |e| match &e.kind {
        ExprKind::Closure(c) => visit_closure(c, fa, scope, f),
        ExprKind::ArrowFn(a) => visit_arrow(a, fa, scope, f),
        _ => {}
    });
}

fn visit_function(
    fd: &FunctionDecl,
    fa: &FileAnalysis,
    scope: &Scope,
    f: &mut impl FnMut(&FnScope),
) {
    let return_type = function_decl_return_type(fd, fa, scope);
    f(&FnScope {
        body: &fd.body,
        return_type,
        scope,
    });
    // Descend into nested closures / arrow fns / nested function decls in the body.
    visit_body_inline_fns(&fd.body, fa, scope, f);
}

fn visit_class(c: &ClassDecl, fa: &FileAnalysis, scope: &Scope, f: &mut impl FnMut(&FnScope)) {
    let reflected = c.name.map(|name| {
        let fqn = scope.qualify(fa.interner.resolve(name));
        fa.reflect_class(scope, &fqn, c)
    });
    let mut reflected_methods = reflected.as_ref().map(|r| r.methods.iter());

    for m in &c.members {
        if let Member::Method(md) = m {
            let modeled_return = reflected_methods
                .as_mut()
                .and_then(|methods| methods.next())
                .and_then(|m| m.explicit_return.then(|| m.return_type.clone()))
                .or_else(|| md.return_type.as_ref().map(|t| resolve_ast_type(scope, t)));
            visit_method(md, fa, scope, modeled_return, f);
        }
    }
}

fn visit_method(
    md: &MethodDecl,
    fa: &FileAnalysis,
    scope: &Scope,
    return_type: Option<Type>,
    f: &mut impl FnMut(&FnScope),
) {
    let Some(body) = &md.body else { return };
    f(&FnScope {
        body,
        return_type,
        scope,
    });
    visit_body_inline_fns(body, fa, scope, f);
}

fn visit_closure(c: &ClosureExpr, fa: &FileAnalysis, scope: &Scope, f: &mut impl FnMut(&FnScope)) {
    let return_type = c.return_type.as_ref().map(|t| resolve_ast_type(scope, t));
    f(&FnScope {
        body: &c.body,
        return_type,
        scope,
    });
    visit_body_inline_fns(&c.body, fa, scope, f);
}

fn visit_arrow(a: &ArrowFn, fa: &FileAnalysis, scope: &Scope, f: &mut impl FnMut(&FnScope)) {
    // An arrow fn's body is a single expression; wrap it so the inline-fn scan
    // and yield detection can reuse the statement-list helpers.
    let body = [Stmt::new(
        a.body.span,
        StmtKind::Return(Some((*a.body).clone())),
    )];
    let return_type = a.return_type.as_ref().map(|t| resolve_ast_type(scope, t));
    f(&FnScope {
        body: &body,
        return_type,
        scope,
    });
    visit_body_inline_fns(&body, fa, scope, f);
}

/// Descend into closures / arrow fns / nested function & class declarations that
/// live inside a function body (each is its own scope, reusing `scope` for name
/// resolution — good enough for resolving native return types).
fn visit_body_inline_fns(
    body: &[Stmt],
    fa: &FileAnalysis,
    scope: &Scope,
    f: &mut impl FnMut(&FnScope),
) {
    for st in body {
        // Nested function / class declarations.
        walk::for_each_stmt_in_stmt(st, &mut |s| match &s.kind {
            StmtKind::Function(fd) => {
                let rt = function_decl_return_type(fd, fa, scope);
                f(&FnScope {
                    body: &fd.body,
                    return_type: rt,
                    scope,
                });
            }
            StmtKind::Class(c) => visit_class(c, fa, scope, f),
            _ => {}
        });
        // Closures / arrow fns in this body's own scope.
        walk::for_each_expr_in_scope(st, &mut |e| match &e.kind {
            ExprKind::Closure(c) => visit_closure(c, fa, scope, f),
            ExprKind::ArrowFn(a) => visit_arrow(a, fa, scope, f),
            _ => {}
        });
    }
}

fn function_decl_return_type(fd: &FunctionDecl, fa: &FileAnalysis, scope: &Scope) -> Option<Type> {
    if fd.return_type.is_none() && !doc_has_return(fd.doc.as_deref()) {
        return None;
    }
    Some(fa.reflect_function(scope, fd).return_type.clone())
}

fn doc_has_return(doc: Option<&str>) -> bool {
    php_phpdoc::query::has_return_conservative(doc)
}

// ---------------------------------------------------------------------------
// YieldInGeneratorRule — `generator.outOfFunction` / `generator.returnType`
// ---------------------------------------------------------------------------

const GENERATOR_RETURN_TYPES: &str = "Generator, Iterator, Traversable, iterable";

fn run_yield_in_generator(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();

    // `generator.outOfFunction`: a yield in the file's top-level region (not in
    // any function-like scope).
    for_each_region(&fa.program.stmts, fa.interner, |_scope, region| {
        for st in region {
            // Only the region's *own-scope* yields (closures have their own scope).
            if matches!(st.kind, StmtKind::Function(_) | StmtKind::Class(_)) {
                continue;
            }
            walk::for_each_expr_in_scope(st, &mut |e| {
                if matches!(e.kind, ExprKind::Yield { .. } | ExprKind::YieldFrom(_)) {
                    out.push(
                        Diagnostic::error(e.span, "Yield can be used only inside a function.")
                            .with_code("generator.outOfFunction"),
                    );
                }
            });
        }
    });

    // `generator.returnType`: a generator body whose declared return type is
    // provably not generator-compatible.
    for_each_fn_scope(fa, |fs| {
        let Some(rt) = &fs.return_type else { return };
        if !is_generator_body(fs.body) {
            return;
        }
        if return_type_allows_generator(rt) {
            return;
        }
        // Anchor the diagnostic at the first yield in the body.
        let mut anchor = None;
        yields_in_body(fs.body, &mut |e| {
            if anchor.is_none() {
                anchor = Some(e.span);
            }
        });
        if let Some(span) = anchor {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "Yield can be used only with these return types: {GENERATOR_RETURN_TYPES}."
                    ),
                )
                .with_code("generator.returnType"),
            );
        }
    });

    out
}

// ---------------------------------------------------------------------------
// YieldFromTypeRule — `generator.nonIterable`
// ---------------------------------------------------------------------------

fn run_yield_from_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::YieldFrom(inner) = &e.kind else {
            return;
        };
        let t = fa.type_of(inner);
        if definitely_not_iterable(&t) {
            out.push(
                Diagnostic::error(
                    inner.span,
                    format!(
                        "Argument of an invalid type {t} passed to yield from, only iterables are supported."
                    ),
                )
                .with_code("generator.nonIterable"),
            );
        }
    });
    out
}

fn run_yield_from_maybe_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::YieldFrom(inner) = &e.kind else {
            return;
        };
        let t = fa.type_of(inner);
        if maybe_iterable(&t) {
            out.push(
                Diagnostic::error(
                    inner.span,
                    format!(
                        "Argument of an invalid type {t} passed to yield from, only iterables are supported."
                    ),
                )
                .with_code("generator.nonIterable"),
            );
        }
    });
    out
}

// ---------------------------------------------------------------------------
// YieldTypeRule — `generator.keyType` / `generator.valueType` / `generator.void`
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct YieldExpectation {
    key: Option<Type>,
    value: Option<Type>,
    send: Option<Type>,
}

fn run_yield_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();

    for_each_fn_scope(fa, |fs| {
        let Some(return_type) = &fs.return_type else {
            return;
        };
        let Some(expected) = yield_expectation(return_type) else {
            return;
        };

        if expected.key.is_some() || expected.value.is_some() {
            yields_in_body(fs.body, &mut |e| match &e.kind {
                ExprKind::Yield { key, value } => {
                    check_yield_key_value(
                        fa,
                        fs.scope,
                        e,
                        key.as_deref(),
                        value.as_deref(),
                        &expected,
                        &mut out,
                    );
                }
                ExprKind::YieldFrom(inner) => {
                    check_yield_from_key_value(fa, fs.scope, e, inner, &expected, &mut out);
                }
                _ => {}
            });
        }

        if matches!(expected.send, Some(Type::Void)) {
            collect_void_yield_uses(fs.body, &mut out);
        }
    });

    out
}

fn check_yield_key_value(
    fa: &FileAnalysis,
    scope: &Scope,
    yield_expr: &Expr,
    key: Option<&Expr>,
    value: Option<&Expr>,
    expected: &YieldExpectation,
    out: &mut Vec<Diagnostic>,
) {
    if let Some(expected_key) = &expected.key {
        let given = key.map_or(Type::Int, |e| yield_operand_type(fa, scope, e));
        check_yield_slot(fa, yield_expr, "key", expected_key, given, out);
    }

    if let Some(expected_value) = &expected.value {
        let given = value.map_or(Type::Null, |e| yield_operand_type(fa, scope, e));
        check_yield_slot(fa, yield_expr, "value", expected_value, given, out);
    }
}

fn check_yield_from_key_value(
    fa: &FileAnalysis,
    scope: &Scope,
    yield_expr: &Expr,
    delegated: &Expr,
    expected: &YieldExpectation,
    out: &mut Vec<Diagnostic>,
) {
    let delegated = yield_operand_type(fa, scope, delegated);
    let Some((given_key, given_value)) = fa.reflection.iterable_key_value_on_type(&delegated)
    else {
        return;
    };

    if let Some(expected_key) = &expected.key {
        check_yield_slot(fa, yield_expr, "key", expected_key, given_key, out);
    }

    if let Some(expected_value) = &expected.value {
        check_yield_slot(fa, yield_expr, "value", expected_value, given_value, out);
    }
}

fn yield_operand_type(fa: &FileAnalysis, scope: &Scope, e: &Expr) -> Type {
    let mapped = fa.type_of(e);
    if !matches!(mapped, Type::Mixed | Type::ExplicitMixed) {
        return mapped;
    }

    // `php_infer::type_map` currently records a `yield` expression as a leaf, so
    // its key/value children can be absent from the map. A local expression
    // inference with an empty variable environment recovers concrete literals,
    // arrays, calls, and `new` expressions while leaving variables as `mixed`.
    php_infer::TypeCtx::new(fa.reflection, scope, fa.interner).infer(e)
}

fn check_yield_slot(
    fa: &FileAnalysis,
    yield_expr: &Expr,
    slot: &str,
    expected: &Type,
    given: Type,
    out: &mut Vec<Diagnostic>,
) {
    if !slot_checkable(expected) || !slot_checkable(&given) {
        return;
    }

    let checked_given = fa.lenient_src(given.clone());
    if php_infer::is_assignable(fa.reflection, &checked_given, expected) {
        return;
    }

    out.push(
        Diagnostic::error(
            yield_expr.span,
            format!("Generator expects {slot} type {expected}, {given} given."),
        )
        .with_code(match slot {
            "key" => "generator.keyType",
            _ => "generator.valueType",
        }),
    );
}

fn yield_expectation(return_type: &Type) -> Option<YieldExpectation> {
    match return_type {
        Type::Nullable(inner) => yield_expectation(inner),
        Type::Iterable(Some(kv)) => Some(YieldExpectation {
            key: Some(kv.0.clone()),
            value: Some(kv.1.clone()),
            send: None,
        }),
        Type::Named { fqn, args } if is_generator_family(fqn) => match args.as_slice() {
            [] => None,
            [value] => Some(YieldExpectation {
                key: None,
                value: Some(value.clone()),
                send: None,
            }),
            [key, value, rest @ ..] => Some(YieldExpectation {
                key: Some(key.clone()),
                value: Some(value.clone()),
                send: is_generator_fqn(fqn)
                    .then(|| rest.first().cloned())
                    .flatten(),
            }),
        },
        _ => None,
    }
}

fn is_generator_family(fqn: &str) -> bool {
    is_generator_fqn(fqn)
        || fqn.eq_ignore_ascii_case("Iterator")
        || fqn.eq_ignore_ascii_case("Traversable")
}

fn is_generator_fqn(fqn: &str) -> bool {
    fqn.eq_ignore_ascii_case("Generator")
}

fn slot_checkable(t: &Type) -> bool {
    match t {
        Type::Mixed
        | Type::Unknown(_)
        | Type::TemplateVar(_)
        | Type::SelfType
        | Type::StaticType
        | Type::Parent
        | Type::Conditional { .. } => false,
        Type::Nullable(inner) | Type::List(inner) | Type::ClassString(Some(inner)) => {
            slot_checkable(inner)
        }
        Type::Union(parts) | Type::Intersection(parts) => {
            !parts.is_empty() && parts.iter().all(slot_checkable)
        }
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            slot_checkable(&kv.0) && slot_checkable(&kv.1)
        }
        Type::Callable(Some(sig)) => {
            sig.params.iter().all(slot_checkable) && slot_checkable(&sig.ret)
        }
        Type::Named { args, .. } => args.iter().all(slot_checkable),
        Type::Shape { fields, .. } => fields.iter().all(|f| slot_checkable(&f.ty)),
        _ => true,
    }
}

fn collect_void_yield_uses(body: &[Stmt], out: &mut Vec<Diagnostic>) {
    for st in body {
        collect_void_yield_uses_stmt(st, out);
    }
}

fn collect_void_yield_uses_stmt(st: &Stmt, out: &mut Vec<Diagnostic>) {
    match &st.kind {
        StmtKind::Expr(e) => collect_void_yield_uses_expr(e, false, out),
        StmtKind::Echo(es) => es
            .iter()
            .for_each(|e| collect_void_yield_uses_expr(e, true, out)),
        StmtKind::Return(Some(e)) => collect_void_yield_uses_expr(e, true, out),
        StmtKind::Return(None) => {}
        StmtKind::Block(b) => collect_void_yield_uses(b, out),
        StmtKind::If {
            cond,
            then,
            elseifs,
            els,
        } => {
            collect_void_yield_uses_expr(cond, true, out);
            collect_void_yield_uses_stmt(then, out);
            for ei in elseifs {
                collect_void_yield_uses_expr(&ei.cond, true, out);
                collect_void_yield_uses_stmt(&ei.body, out);
            }
            if let Some(els) = els {
                collect_void_yield_uses_stmt(els, out);
            }
        }
        StmtKind::While { cond, body } => {
            collect_void_yield_uses_expr(cond, true, out);
            collect_void_yield_uses_stmt(body, out);
        }
        StmtKind::DoWhile { body, cond } => {
            collect_void_yield_uses_stmt(body, out);
            collect_void_yield_uses_expr(cond, true, out);
        }
        StmtKind::For {
            init,
            cond,
            update,
            body,
        } => {
            init.iter()
                .chain(cond)
                .chain(update)
                .for_each(|e| collect_void_yield_uses_expr(e, true, out));
            collect_void_yield_uses_stmt(body, out);
        }
        StmtKind::Foreach {
            subject,
            key,
            value,
            body,
            ..
        } => {
            collect_void_yield_uses_expr(subject, true, out);
            if let Some(k) = key {
                collect_void_yield_uses_expr(k, true, out);
            }
            collect_void_yield_uses_expr(value, true, out);
            collect_void_yield_uses_stmt(body, out);
        }
        StmtKind::Switch { subject, cases } => {
            collect_void_yield_uses_expr(subject, true, out);
            for case in cases {
                if let Some(test) = &case.test {
                    collect_void_yield_uses_expr(test, true, out);
                }
                collect_void_yield_uses(&case.body, out);
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            collect_void_yield_uses(body, out);
            for catch in catches {
                collect_void_yield_uses(&catch.body, out);
            }
            if let Some(finally) = finally {
                collect_void_yield_uses(finally, out);
            }
        }
        StmtKind::Break(Some(e)) | StmtKind::Continue(Some(e)) => {
            collect_void_yield_uses_expr(e, true, out);
        }
        StmtKind::Break(None) | StmtKind::Continue(None) => {}
        StmtKind::Global(es) | StmtKind::Unset(es) => {
            es.iter()
                .for_each(|e| collect_void_yield_uses_expr(e, true, out));
        }
        StmtKind::StaticVars(vars) => {
            for var in vars {
                if let Some(default) = &var.default {
                    collect_void_yield_uses_expr(default, true, out);
                }
            }
        }
        StmtKind::Declare { directives, body } => {
            for (_, value) in directives {
                collect_void_yield_uses_expr(value, true, out);
            }
            if let Some(body) = body {
                collect_void_yield_uses_stmt(body, out);
            }
        }
        StmtKind::Namespace {
            body: Some(body), ..
        } => collect_void_yield_uses(body, out),
        StmtKind::ConstDecl { consts, .. } => {
            consts
                .iter()
                .for_each(|c| collect_void_yield_uses_expr(&c.value, true, out));
        }
        // Nested function-like scopes have their own `TSend`.
        StmtKind::Function(_)
        | StmtKind::Class(_)
        | StmtKind::Namespace { body: None, .. }
        | StmtKind::Use(_)
        | StmtKind::GroupUse { .. }
        | StmtKind::Goto(_)
        | StmtKind::Label(_)
        | StmtKind::HaltCompiler(_)
        | StmtKind::InlineHtml(_)
        | StmtKind::Nop
        | StmtKind::Error => {}
    }
}

fn collect_void_yield_uses_expr(e: &Expr, consumed: bool, out: &mut Vec<Diagnostic>) {
    match &e.kind {
        ExprKind::Yield { key, value } => {
            if consumed {
                out.push(
                    Diagnostic::error(e.span, "Result of yield (void) is used.")
                        .with_code("generator.void"),
                );
            }
            if let Some(k) = key {
                collect_void_yield_uses_expr(k, true, out);
            }
            if let Some(v) = value {
                collect_void_yield_uses_expr(v, true, out);
            }
        }
        ExprKind::Paren(inner) => collect_void_yield_uses_expr(inner, consumed, out),
        ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Variable(_)
        | ExprKind::Name(_)
        | ExprKind::Closure(_)
        | ExprKind::ArrowFn(_)
        | ExprKind::Error => {}
        ExprKind::Interpolated(parts) | ExprKind::ShellExec(parts) => {
            parts
                .iter()
                .for_each(|p| collect_void_yield_uses_expr(p, true, out));
        }
        ExprKind::VariableVariable(inner) | ExprKind::DollarBrace(inner) => {
            collect_void_yield_uses_expr(inner, true, out);
        }
        ExprKind::Array { items, .. } => {
            items
                .iter()
                .for_each(|item| collect_void_yield_uses_array_item(item, out));
        }
        ExprKind::Call { callee, args } => {
            collect_void_yield_uses_expr(callee, true, out);
            collect_void_yield_uses_args(args, out);
        }
        ExprKind::MethodCall {
            recv, method, args, ..
        } => {
            collect_void_yield_uses_expr(recv, true, out);
            collect_void_yield_uses_member(method, out);
            collect_void_yield_uses_args(args, out);
        }
        ExprKind::StaticCall {
            class,
            method,
            args,
        } => {
            collect_void_yield_uses_expr(class, true, out);
            collect_void_yield_uses_member(method, out);
            collect_void_yield_uses_args(args, out);
        }
        ExprKind::New { class, args } => {
            collect_void_yield_uses_expr(class, true, out);
            collect_void_yield_uses_args(args, out);
        }
        ExprKind::NewAnon { args, .. } => {
            collect_void_yield_uses_args(args, out);
        }
        ExprKind::Index { base, index } => {
            collect_void_yield_uses_expr(base, true, out);
            if let Some(index) = index {
                collect_void_yield_uses_expr(index, true, out);
            }
        }
        ExprKind::Prop { base, name, .. } => {
            collect_void_yield_uses_expr(base, true, out);
            collect_void_yield_uses_member(name, out);
        }
        ExprKind::StaticProp { class, name } | ExprKind::ClassConst { class, name } => {
            collect_void_yield_uses_expr(class, true, out);
            collect_void_yield_uses_member(name, out);
        }
        ExprKind::Unary { expr, .. } | ExprKind::Cast { expr, .. } => {
            collect_void_yield_uses_expr(expr, true, out);
        }
        ExprKind::Binary { lhs, rhs, .. }
        | ExprKind::Assign { target: lhs, rhs }
        | ExprKind::AssignOp {
            target: lhs, rhs, ..
        }
        | ExprKind::AssignRef { target: lhs, rhs }
        | ExprKind::Coalesce { lhs, rhs } => {
            collect_void_yield_uses_expr(lhs, true, out);
            collect_void_yield_uses_expr(rhs, true, out);
        }
        ExprKind::Ternary { cond, then, els } => {
            collect_void_yield_uses_expr(cond, true, out);
            if let Some(then) = then {
                collect_void_yield_uses_expr(then, true, out);
            }
            collect_void_yield_uses_expr(els, true, out);
        }
        ExprKind::PreInc(inner)
        | ExprKind::PreDec(inner)
        | ExprKind::PostInc(inner)
        | ExprKind::PostDec(inner)
        | ExprKind::Clone(inner)
        | ExprKind::Print(inner)
        | ExprKind::Throw(inner)
        | ExprKind::ErrorSuppress(inner)
        | ExprKind::YieldFrom(inner)
        | ExprKind::Eval(inner)
        | ExprKind::Empty(inner) => collect_void_yield_uses_expr(inner, true, out),
        ExprKind::Instanceof { expr, class } => {
            collect_void_yield_uses_expr(expr, true, out);
            collect_void_yield_uses_expr(class, true, out);
        }
        ExprKind::Exit(Some(inner)) => collect_void_yield_uses_expr(inner, true, out),
        ExprKind::Exit(None) => {}
        ExprKind::Match { subject, arms } => {
            collect_void_yield_uses_expr(subject, true, out);
            for arm in arms {
                if let Some(conds) = &arm.conds {
                    conds
                        .iter()
                        .for_each(|c| collect_void_yield_uses_expr(c, true, out));
                }
                collect_void_yield_uses_expr(&arm.body, true, out);
            }
        }
        ExprKind::Include { expr, .. } => collect_void_yield_uses_expr(expr, true, out),
        ExprKind::Isset(es) => es
            .iter()
            .for_each(|e| collect_void_yield_uses_expr(e, true, out)),
    }
}

fn collect_void_yield_uses_args(args: &[Arg], out: &mut Vec<Diagnostic>) {
    args.iter()
        .for_each(|arg| collect_void_yield_uses_expr(&arg.value, true, out));
}

fn collect_void_yield_uses_array_item(item: &ArrayItem, out: &mut Vec<Diagnostic>) {
    if let Some(key) = &item.key {
        collect_void_yield_uses_expr(key, true, out);
    }
    if let Some(value) = &item.value {
        collect_void_yield_uses_expr(value, true, out);
    }
}

fn collect_void_yield_uses_member(member: &MemberName, out: &mut Vec<Diagnostic>) {
    if let MemberName::Expr(expr) = member {
        collect_void_yield_uses_expr(expr, true, out);
    }
}

// ---------------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------------

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "generators.yieldInGenerator",
        level: 3,
        run: run_yield_in_generator,
    },
    RuleEntry {
        name: "generators.yieldFromType",
        level: 3,
        run: run_yield_from_type,
    },
    RuleEntry {
        name: "generators.yieldFromMaybeType",
        level: 7,
        run: run_yield_from_maybe_type,
    },
    RuleEntry {
        name: "generators.yieldType",
        level: 3,
        run: run_yield_type,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- generator.outOfFunction ---

    #[test]
    fn yield_at_top_level_is_flagged() {
        assert_eq!(
            codes("<?php yield 1;", run_yield_in_generator),
            ["generator.outOfFunction"]
        );
    }

    #[test]
    fn yield_from_at_top_level_is_flagged() {
        assert_eq!(
            codes("<?php yield from [1, 2];", run_yield_in_generator),
            ["generator.outOfFunction"]
        );
    }

    #[test]
    fn yield_inside_function_is_not_out_of_function() {
        // Compatible return type → no diagnostic at all.
        let src = "<?php function g(): Generator { yield 1; }";
        assert!(codes(src, run_yield_in_generator).is_empty());
    }

    // --- generator.returnType ---

    #[test]
    fn yield_with_int_return_type_is_flagged() {
        let src = "<?php function g(): int { yield 1; }";
        assert_eq!(codes(src, run_yield_in_generator), ["generator.returnType"]);
    }

    #[test]
    fn yield_with_string_return_type_is_flagged() {
        let src = "<?php function g(): string { yield 1; }";
        assert_eq!(codes(src, run_yield_in_generator), ["generator.returnType"]);
    }

    #[test]
    fn yield_with_generator_return_type_is_clean() {
        let src = "<?php function g(): Generator { yield 1; }";
        assert!(codes(src, run_yield_in_generator).is_empty());
    }

    #[test]
    fn yield_with_iterable_return_type_is_clean() {
        let src = "<?php function g(): iterable { yield 1; }";
        assert!(codes(src, run_yield_in_generator).is_empty());
    }

    #[test]
    fn yield_with_iterator_return_type_is_clean() {
        let src = "<?php function g(): Iterator { yield 1; }";
        assert!(codes(src, run_yield_in_generator).is_empty());
    }

    #[test]
    fn yield_without_return_type_is_clean() {
        // No declared return type → no return-type diagnostic.
        let src = "<?php function g() { yield 1; }";
        assert!(codes(src, run_yield_in_generator).is_empty());
    }

    #[test]
    fn non_generator_function_with_int_return_is_clean() {
        let src = "<?php function g(): int { return 1; }";
        assert!(codes(src, run_yield_in_generator).is_empty());
    }

    #[test]
    fn yield_in_method_with_bad_return_type_is_flagged() {
        let src = "<?php class C { function g(): int { yield 1; } }";
        assert_eq!(codes(src, run_yield_in_generator), ["generator.returnType"]);
    }

    #[test]
    fn yield_in_closure_with_bad_return_type_is_flagged() {
        let src = "<?php $f = function (): int { yield 1; };";
        assert_eq!(codes(src, run_yield_in_generator), ["generator.returnType"]);
    }

    #[test]
    fn nullable_generator_return_type_is_clean() {
        let src = "<?php function g(): ?Generator { yield 1; }";
        assert!(codes(src, run_yield_in_generator).is_empty());
    }

    #[test]
    fn nested_function_yield_uses_its_own_return_type() {
        // Outer is a clean generator; inner has a bad return type.
        let src =
            "<?php function outer(): Generator { function inner(): int { yield 1; } yield 2; }";
        assert_eq!(codes(src, run_yield_in_generator), ["generator.returnType"]);
    }

    // --- generator.nonIterable ---

    #[test]
    fn yield_from_int_literal_is_flagged() {
        let src = "<?php function g(): Generator { yield from 5; }";
        assert_eq!(codes(src, run_yield_from_type), ["generator.nonIterable"]);
    }

    #[test]
    fn yield_from_string_literal_is_flagged() {
        let src = "<?php function g(): Generator { yield from 'x'; }";
        assert_eq!(codes(src, run_yield_from_type), ["generator.nonIterable"]);
    }

    #[test]
    fn yield_from_array_is_clean() {
        let src = "<?php function g(): Generator { yield from [1, 2]; }";
        assert!(codes(src, run_yield_from_type).is_empty());
    }

    #[test]
    fn yield_from_typed_int_param_is_flagged() {
        let src = "<?php function g(int $n): Generator { yield from $n; }";
        assert_eq!(codes(src, run_yield_from_type), ["generator.nonIterable"]);
    }

    #[test]
    fn yield_from_array_or_int_param_is_maybe_non_iterable() {
        let src = r#"<?php
            /** @param array<int>|int $x */
            function g($x): Generator { yield from $x; }"#;
        assert!(codes(src, run_yield_from_type).is_empty());
        assert_eq!(
            codes(src, run_yield_from_maybe_type),
            ["generator.nonIterable"]
        );
    }

    #[test]
    fn yield_from_array_or_unknown_object_is_not_reported_as_safe_maybe() {
        let src = r#"<?php
            /** @param array<int>|\ArrayObject $x */
            function g($x): Generator { yield from $x; }"#;
        assert!(codes(src, run_yield_from_maybe_type).is_empty());
    }

    #[test]
    fn yield_from_unknown_param_is_clean() {
        // Untyped param → mixed → not provably non-iterable.
        let src = "<?php function g($x): Generator { yield from $x; }";
        assert!(codes(src, run_yield_from_type).is_empty());
    }

    #[test]
    fn yield_from_object_is_clean() {
        // A typed object could be a Traversable; don't flag.
        let src = "<?php function g(\\ArrayObject $a): Generator { yield from $a; }";
        assert!(codes(src, run_yield_from_type).is_empty());
    }

    // --- generator.keyType / generator.valueType ---

    #[test]
    fn yield_key_and_value_mismatch_are_flagged_from_phpdoc_generator() {
        let src = r#"<?php
        /** @return \Generator<string, int> */
        function g(): \Generator { yield 1 => 'x'; }"#;
        assert_eq!(
            codes(src, run_yield_type),
            ["generator.keyType", "generator.valueType"]
        );
    }

    #[test]
    fn yield_key_and_value_match_phpdoc_generator_are_clean() {
        let src = r#"<?php
        /** @return \Generator<string, int> */
        function g(): \Generator { yield 'k' => 1; }"#;
        assert!(codes(src, run_yield_type).is_empty());
    }

    #[test]
    fn yield_without_value_checks_default_null_value() {
        let src = r#"<?php
        /** @return \Generator<string, int> */
        function g(): \Generator { yield; }"#;
        assert_eq!(
            codes(src, run_yield_type),
            ["generator.keyType", "generator.valueType"]
        );
    }

    #[test]
    fn one_arg_generator_checks_value_only() {
        let src = r#"<?php
        /** @return \Generator<string> */
        function g(): \Generator { yield 1; }"#;
        assert_eq!(codes(src, run_yield_type), ["generator.valueType"]);
    }

    #[test]
    fn iterable_generics_are_checked_for_generator_body() {
        let src = r#"<?php
        /** @return iterable<int, string> */
        function g(): iterable { yield 'k' => 1; }"#;
        assert_eq!(
            codes(src, run_yield_type),
            ["generator.keyType", "generator.valueType"]
        );
    }

    #[test]
    fn method_phpdoc_generator_generics_are_checked() {
        let src = r#"<?php
        class C {
            /** @return \Generator<int, string> */
            function g(): \Generator { yield 'k' => 1; }
        }"#;
        assert_eq!(
            codes(src, run_yield_type),
            ["generator.keyType", "generator.valueType"]
        );
    }

    #[test]
    fn mixed_yield_key_or_value_is_clean() {
        let src = r#"<?php
        /** @return \Generator<string, int> */
        function g($x): \Generator { yield $x => $x; }"#;
        assert!(codes(src, run_yield_type).is_empty());
    }

    #[test]
    fn bare_generator_return_type_has_no_generic_slots_to_check() {
        let src = "<?php function g(): \\Generator { yield 'k' => 'v'; }";
        assert!(codes(src, run_yield_type).is_empty());
    }

    #[test]
    fn yield_from_delegated_key_and_value_mismatch_are_flagged() {
        let src = r#"<?php
        class User {}
        /** @return \Generator<string, User, void, void> */
        function child(): \Generator { yield 'k' => new User(); }
        /** @return \Generator<int, string, void, void> */
        function parent_gen(): \Generator { yield from child(); }"#;
        assert_eq!(
            codes(src, run_yield_type),
            ["generator.keyType", "generator.valueType"]
        );
    }

    #[test]
    fn yield_from_delegated_key_and_value_match_are_clean() {
        let src = r#"<?php
        class User {}
        /** @return \Generator<int, User, void, void> */
        function child(): \Generator { yield new User(); }
        /** @return \Generator<int, User, void, void> */
        function parent_gen(): \Generator { yield from child(); }"#;
        assert!(codes(src, run_yield_type).is_empty());
    }

    #[test]
    fn yield_from_unknown_iterable_slots_are_clean() {
        let src = r#"<?php
        /** @return \Generator<int, string, void, void> */
        function parent_gen($x): \Generator { yield from $x; }"#;
        assert!(codes(src, run_yield_type).is_empty());
    }

    // --- generator.void ---

    #[test]
    fn used_yield_result_with_void_send_type_is_flagged() {
        let src = r#"<?php
        /** @return \Generator<int, int, void, void> */
        function g(): \Generator {
            yield 1;
            $x = yield 1;
            var_dump(yield 1);
            (yield 1);
        }"#;
        assert_eq!(
            codes(src, run_yield_type),
            ["generator.void", "generator.void"]
        );
    }

    #[test]
    fn used_yield_result_with_non_void_send_type_is_clean() {
        let src = r#"<?php
        /** @return \Generator<int, int, int, void> */
        function g(): \Generator { $x = yield 1; }"#;
        assert!(codes(src, run_yield_type).is_empty());
    }

    #[test]
    fn used_yield_result_without_send_type_is_clean() {
        let src = r#"<?php
        /** @return \Generator<int, int> */
        function g(): \Generator { $x = yield 1; }"#;
        assert!(codes(src, run_yield_type).is_empty());
    }

    #[test]
    fn nested_yield_result_with_void_send_type_is_flagged() {
        let src = r#"<?php
        /** @return \Generator<int, int, void, void> */
        function g(): \Generator { yield (yield 1); }"#;
        assert_eq!(codes(src, run_yield_type), ["generator.void"]);
    }
}
