//! Shared semantic AST queries built on top of the traversal policy.

use crate::{walk, Expr, ExprKind, Stmt};

/// Whether `body` contains `yield` or `yield from` in its current scope.
///
/// Nested function-like scopes are intentionally skipped: closures, arrow
/// functions, named functions/classes, and anonymous-class bodies carry their
/// own generator flags. Expressions in the current scope, including anonymous
/// class constructor arguments and computed member names, are still visited.
pub fn contains_yield_in_scope(body: &[Stmt]) -> bool {
    body.iter().any(contains_yield_in_stmt_scope)
}

/// Whether `stmt` contains `yield` or `yield from` in its current scope.
pub fn contains_yield_in_stmt_scope(stmt: &Stmt) -> bool {
    let mut found = false;
    walk::for_each_expr_in_scope(stmt, &mut |expr| {
        if matches!(expr.kind, ExprKind::Yield { .. } | ExprKind::YieldFrom(_)) {
            found = true;
        }
    });
    found
}

/// Whether `expr` contains `yield` or `yield from` in its current scope.
pub fn contains_yield_in_expr_scope(expr: &Expr) -> bool {
    let mut found = false;
    walk::for_each_subexpr(expr, &mut |sub| {
        if matches!(sub.kind, ExprKind::Yield { .. } | ExprKind::YieldFrom(_)) {
            found = true;
        }
    });
    found
}

#[cfg(test)]
mod tests {
    use crate::{
        queries::{contains_yield_in_expr_scope, contains_yield_in_scope},
        Arg, ClassDecl, ClassKind, ClosureExpr, Expr, ExprKind, MemberName, Modifiers, Span, Stmt,
        StmtKind,
    };

    fn e(kind: ExprKind) -> Expr {
        Expr::new(Span::new(0, 0), kind)
    }

    fn stmt(kind: StmtKind) -> Stmt {
        Stmt::new(Span::new(0, 0), kind)
    }

    #[test]
    fn finds_yield_in_anonymous_class_constructor_args() {
        let anon = ClassDecl {
            attrs: vec![],
            doc: None,
            kind: ClassKind::Class,
            name: None,
            name_span: Span::new(0, 0),
            modifiers: Modifiers::default(),
            extends: vec![],
            implements: vec![],
            backing: None,
            members: vec![],
        };
        let expr = e(ExprKind::NewAnon {
            class: Box::new(anon),
            args: vec![Arg {
                span: Span::new(0, 0),
                name: None,
                value: e(ExprKind::Yield {
                    key: None,
                    value: None,
                }),
                spread: false,
                placeholder: false,
            }],
        });
        assert!(contains_yield_in_expr_scope(&expr));
    }

    #[test]
    fn finds_yield_in_computed_member_name() {
        let expr = e(ExprKind::Prop {
            base: Box::new(e(ExprKind::Int(1))),
            nullsafe: false,
            name: MemberName::Expr(Box::new(e(ExprKind::YieldFrom(Box::new(e(
                ExprKind::Int(2),
            )))))),
        });
        assert!(contains_yield_in_expr_scope(&expr));
    }

    #[test]
    fn skips_nested_closure_scope() {
        let nested = stmt(StmtKind::Expr(e(ExprKind::Closure(Box::new(
            ClosureExpr {
                attrs: vec![],
                is_static: false,
                by_ref: false,
                params: vec![],
                uses: vec![],
                return_type: None,
                body: vec![stmt(StmtKind::Expr(e(ExprKind::Yield {
                    key: None,
                    value: None,
                })))],
            },
        )))));
        assert!(!contains_yield_in_scope(&[nested]));
    }
}

/// Strip redundant parentheses: `((expr))` → `expr`.
///
/// The AST keeps `Paren` nodes because PHP's own AST records parenthesization
/// (it is load-bearing for a few `attr` flags in the differential dump), so
/// every consumer that pattern-matches on an expression's *shape* has to peel
/// them first. Shared here rather than re-implemented per crate — this had six
/// copies across `php-infer` and `php-rules`.
pub fn peel_paren(e: &Expr) -> &Expr {
    match &e.kind {
        ExprKind::Paren(inner) => peel_paren(inner),
        _ => e,
    }
}

#[cfg(test)]
mod peel_tests {
    use super::peel_paren;
    use crate::{Expr, ExprKind};
    use php_span::Span;

    // Built by hand: `php-ast` must not depend on the parser/lexer (CLAUDE.md
    // §3 — the AST is the stable contract and never pulls in the tokenizer),
    // not even as a dev-dependency.
    fn expr(kind: ExprKind) -> Expr {
        Expr {
            span: Span::new(0, 0),
            kind,
        }
    }

    #[test]
    fn peels_nested_parens_to_the_inner_expression() {
        let inner = expr(ExprKind::Int(1));
        let wrapped = expr(ExprKind::Paren(Box::new(expr(ExprKind::Paren(Box::new(
            inner,
        ))))));
        assert!(matches!(peel_paren(&wrapped).kind, ExprKind::Int(1)));
    }

    #[test]
    fn leaves_a_bare_expression_alone() {
        let bare = expr(ExprKind::Int(7));
        assert!(matches!(peel_paren(&bare).kind, ExprKind::Int(7)));
    }
}
