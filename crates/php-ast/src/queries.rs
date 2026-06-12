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
