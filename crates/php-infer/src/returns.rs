//! Shared return collection/refinement for interprocedural inference.

use crate::TypeCtx;
use php_ast::{BinOp, Expr, ExprKind, Stmt, StmtKind, UnOp};
use php_resolve::Scope;
use php_types::Type;
use std::collections::HashMap;

/// Conservative per-call return refinement.
pub(crate) fn refine_return(
    caller: &TypeCtx<'_>,
    declared: &Type,
    body: Option<(&[Stmt], &Scope)>,
    params: &[String],
    args: &[php_ast::Arg],
    callee_class: Option<String>,
) -> Type {
    let Some((body, callee_scope)) = body else {
        return declared.clone();
    };
    let refinable = matches!(declared, Type::Nullable(_))
        || matches!(declared, Type::Union(parts) if parts.contains(&Type::Null));
    if caller.depth >= 2 || !refinable {
        return declared.clone();
    }
    let mut sub = TypeCtx {
        index: caller.index,
        scope: callee_scope,
        interner: caller.interner,
        class: callee_class,
        vars: HashMap::new(),
        callables: HashMap::new(),
        depth: caller.depth + 1,
        native: caller.native,
        generator_send: None,
        terminators: caller.terminators.clone(),
    };
    for (name, arg) in params.iter().zip(args) {
        sub.vars.insert(name.clone(), caller.infer(&arg.value));
    }
    let mut returns = Vec::new();
    collect_returns(&mut sub, body, &mut returns);
    let collected = Type::union(returns);
    if collected != Type::Never && crate::is_assignable(caller.index, &collected, declared) {
        collected
    } else {
        declared.clone()
    }
}

/// Collect the types of reachable `return <expr>` statements, pruning branches
/// whose conditions are statically known from bound parameter types.
pub(crate) fn collect_returns(ctx: &mut TypeCtx<'_>, stmts: &[Stmt], out: &mut Vec<Type>) {
    for s in stmts {
        match &s.kind {
            StmtKind::Return(Some(e)) => out.push(ctx.infer(e)),
            StmtKind::Block(b) => collect_returns(ctx, b, out),
            StmtKind::If {
                cond,
                then,
                elseifs,
                els,
            } => collect_if_returns(ctx, cond, then, elseifs, els.as_deref(), out),
            StmtKind::While { body, .. }
            | StmtKind::DoWhile { body, .. }
            | StmtKind::For { body, .. }
            | StmtKind::Foreach { body, .. } => {
                collect_returns(ctx, std::slice::from_ref(body), out)
            }
            StmtKind::Switch { cases, .. } => {
                for c in cases {
                    collect_returns(ctx, &c.body, out);
                }
            }
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                collect_returns(ctx, body, out);
                for c in catches {
                    collect_returns(ctx, &c.body, out);
                }
                if let Some(f) = finally {
                    collect_returns(ctx, f, out);
                }
            }
            _ => {}
        }
    }
}

fn collect_if_returns(
    ctx: &mut TypeCtx<'_>,
    cond: &Expr,
    then: &Stmt,
    elseifs: &[php_ast::ElseIf],
    els: Option<&Stmt>,
    out: &mut Vec<Type>,
) {
    match static_truth(ctx, cond) {
        Some(true) => collect_returns(ctx, std::slice::from_ref(then), out),
        Some(false) => {
            if let Some((first, rest)) = elseifs.split_first() {
                collect_if_returns(ctx, &first.cond, &first.body, rest, els, out)
            } else if let Some(e) = els {
                collect_returns(ctx, std::slice::from_ref(e), out)
            }
        }
        None => {
            collect_returns(ctx, std::slice::from_ref(then), out);
            for ei in elseifs {
                collect_returns(ctx, std::slice::from_ref(&ei.body), out);
            }
            if let Some(e) = els {
                collect_returns(ctx, std::slice::from_ref(e), out);
            }
        }
    }
}

/// Sound static truth evaluation for branch pruning.
pub(crate) fn static_truth(ctx: &TypeCtx<'_>, cond: &Expr) -> Option<bool> {
    match &cond.kind {
        ExprKind::Paren(inner) => static_truth(ctx, inner),
        ExprKind::Unary {
            op: UnOp::Not,
            expr,
        } => static_truth(ctx, expr).map(|b| !b),
        ExprKind::Binary {
            op: BinOp::BoolAnd | BinOp::LogicalAnd,
            lhs,
            rhs,
        } => match (static_truth(ctx, lhs), static_truth(ctx, rhs)) {
            (Some(false), _) | (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            _ => None,
        },
        ExprKind::Binary {
            op: BinOp::BoolOr | BinOp::LogicalOr,
            lhs,
            rhs,
        } => match (static_truth(ctx, lhs), static_truth(ctx, rhs)) {
            (Some(true), _) | (_, Some(true)) => Some(true),
            (Some(false), Some(false)) => Some(false),
            _ => None,
        },
        ExprKind::Binary {
            op: op @ (BinOp::Identical | BinOp::Eq | BinOp::NotIdentical | BinOp::NotEq),
            lhs,
            rhs,
        } => {
            let eq = matches!(op, BinOp::Identical | BinOp::Eq);
            if crate::is_null_literal(lhs) || crate::is_null_literal(rhs) {
                let other = if crate::is_null_literal(lhs) {
                    rhs
                } else {
                    lhs
                };
                return crate::null_truth(&ctx.infer(other)).map(|n| if eq { n } else { !n });
            }
            if let (Type::LiteralInt(a), Type::LiteralInt(b)) = (ctx.infer(lhs), ctx.infer(rhs)) {
                let same = a == b;
                return Some(if eq { same } else { !same });
            }
            None
        }
        ExprKind::Binary {
            op: op @ (BinOp::Lt | BinOp::LtEq | BinOp::Gt | BinOp::GtEq),
            lhs,
            rhs,
        } => {
            let a = crate::int_bounds(&ctx.infer(lhs))?;
            let b = crate::int_bounds(&ctx.infer(rhs))?;
            crate::cmp_ranges(*op, a, b)
        }
        ExprKind::Call { callee, args } => {
            let ExprKind::Name(n) = &callee.kind else {
                return None;
            };
            if !n
                .text
                .trim_start_matches('\\')
                .eq_ignore_ascii_case("is_null")
            {
                return None;
            }
            crate::null_truth(&ctx.infer(&args.first()?.value))
        }
        _ => None,
    }
}
