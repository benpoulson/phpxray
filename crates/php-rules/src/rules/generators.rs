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
//!
//! Deferred:
//! - The `generator.keyType` / `generator.valueType` / `generator.sendType` parts
//!   of `YieldTypeRule` / `YieldFromTypeRule` — need to extract the `Generator`/
//!   `iterable` key/value generic arguments from the declared return type and run
//!   the assignability check against the yielded key/value types. The generic-arg
//!   plumbing (and `TSend` template resolution) is fragile to do FP-safely from
//!   the reflected return type alone; deferred until generic inference deepens.
//! - `generator.void` (result of `yield`/`yield from` used in a non-void position)
//!   — needs first-level-statement tracking, which we don't model.

use crate::{FileAnalysis, RuleEntry};
use php_ast::{
    walk, ArrowFn, ClassDecl, ClosureExpr, Expr, ExprKind, FunctionDecl, Member, MethodDecl, Stmt,
    StmtKind,
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
        Type::Mixed | Type::Unknown(_) => true,
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

/// A function-like scope: its body statements and resolved declared return type
/// (`None` when no return type is written — then the rules stay silent).
struct FnScope<'a> {
    body: &'a [Stmt],
    return_type: Option<Type>,
}

/// Walk every function-like scope in the file (top-level functions, methods,
/// closures, arrow fns — including nested ones), resolving each declared return
/// type against the scope it is written in, and invoke `f` on each.
fn for_each_fn_scope(fa: &FileAnalysis, mut f: impl FnMut(&FnScope)) {
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            visit_stmt(st, scope, &mut f);
        }
    });
}

fn visit_stmt(st: &Stmt, scope: &Scope, f: &mut impl FnMut(&FnScope)) {
    match &st.kind {
        StmtKind::Function(fd) => visit_function(fd, scope, f),
        StmtKind::Class(c) => visit_class(c, scope, f),
        StmtKind::Namespace { body: Some(b), .. } => {
            for s in b {
                visit_stmt(s, scope, f);
            }
        }
        _ => {
            // Closures / arrow fns can appear in any nested expression of a
            // top-level statement; scan this statement's own-scope expressions.
            scan_exprs_for_inline_fns(st, scope, f);
        }
    }
}

/// Find closures / arrow fns inside the *own-scope* expressions of `st` (the
/// global region is the enclosing scope) and visit them.
fn scan_exprs_for_inline_fns(st: &Stmt, scope: &Scope, f: &mut impl FnMut(&FnScope)) {
    walk::for_each_expr_in_scope(st, &mut |e| match &e.kind {
        ExprKind::Closure(c) => visit_closure(c, scope, f),
        ExprKind::ArrowFn(a) => visit_arrow(a, scope, f),
        _ => {}
    });
}

fn visit_function(fd: &FunctionDecl, scope: &Scope, f: &mut impl FnMut(&FnScope)) {
    let return_type = fd.return_type.as_ref().map(|t| resolve_ast_type(scope, t));
    f(&FnScope { body: &fd.body, return_type });
    // Descend into nested closures / arrow fns / nested function decls in the body.
    visit_body_inline_fns(&fd.body, scope, f);
}

fn visit_class(c: &ClassDecl, scope: &Scope, f: &mut impl FnMut(&FnScope)) {
    for m in &c.members {
        if let Member::Method(md) = m {
            visit_method(md, scope, f);
        }
    }
}

fn visit_method(md: &MethodDecl, scope: &Scope, f: &mut impl FnMut(&FnScope)) {
    let Some(body) = &md.body else { return };
    let return_type = md.return_type.as_ref().map(|t| resolve_ast_type(scope, t));
    f(&FnScope { body, return_type });
    visit_body_inline_fns(body, scope, f);
}

fn visit_closure(c: &ClosureExpr, scope: &Scope, f: &mut impl FnMut(&FnScope)) {
    let return_type = c.return_type.as_ref().map(|t| resolve_ast_type(scope, t));
    f(&FnScope { body: &c.body, return_type });
    visit_body_inline_fns(&c.body, scope, f);
}

fn visit_arrow(a: &ArrowFn, scope: &Scope, f: &mut impl FnMut(&FnScope)) {
    // An arrow fn's body is a single expression; wrap it so the inline-fn scan
    // and yield detection can reuse the statement-list helpers.
    let body = [Stmt::new(a.body.span, StmtKind::Return(Some((*a.body).clone())))];
    let return_type = a.return_type.as_ref().map(|t| resolve_ast_type(scope, t));
    f(&FnScope { body: &body, return_type });
    visit_body_inline_fns(&body, scope, f);
}

/// Descend into closures / arrow fns / nested function & class declarations that
/// live inside a function body (each is its own scope, reusing `scope` for name
/// resolution — good enough for resolving native return types).
fn visit_body_inline_fns(body: &[Stmt], scope: &Scope, f: &mut impl FnMut(&FnScope)) {
    for st in body {
        // Nested function / class declarations.
        walk::for_each_stmt_in_stmt(st, &mut |s| match &s.kind {
            StmtKind::Function(fd) => {
                let rt = fd.return_type.as_ref().map(|t| resolve_ast_type(scope, t));
                f(&FnScope { body: &fd.body, return_type: rt });
            }
            StmtKind::Class(c) => visit_class(c, scope, f),
            _ => {}
        });
        // Closures / arrow fns in this body's own scope.
        walk::for_each_expr_in_scope(st, &mut |e| match &e.kind {
            ExprKind::Closure(c) => visit_closure(c, scope, f),
            ExprKind::ArrowFn(a) => visit_arrow(a, scope, f),
            _ => {}
        });
    }
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
                    format!("Yield can be used only with these return types: {GENERATOR_RETURN_TYPES}."),
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
        let ExprKind::YieldFrom(inner) = &e.kind else { return };
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

// ---------------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------------

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "generators.yieldInGenerator", level: 3, run: run_yield_in_generator },
    RuleEntry { name: "generators.yieldFromType", level: 3, run: run_yield_from_type },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- generator.outOfFunction ---

    #[test]
    fn yield_at_top_level_is_flagged() {
        assert_eq!(codes("<?php yield 1;", run_yield_in_generator), ["generator.outOfFunction"]);
    }

    #[test]
    fn yield_from_at_top_level_is_flagged() {
        assert_eq!(codes("<?php yield from [1, 2];", run_yield_in_generator), ["generator.outOfFunction"]);
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
        let src = "<?php function outer(): Generator { function inner(): int { yield 1; } yield 2; }";
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
}
