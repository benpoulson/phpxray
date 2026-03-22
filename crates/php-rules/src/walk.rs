//! A reusable AST traversal for syntactic rules — the analogue of phpstan's
//! "node type + processNode" dispatch. [`walk`] visits every statement and
//! expression in a program (pre-order, descending into all bodies including
//! closures/arrow-fns and class members); [`for_each_expr`] / [`for_each_stmt`]
//! are the common single-callback wrappers.

use php_ast::*;

/// Visit every statement and expression in `program`.
pub(crate) fn walk<S, E>(program: &Program, on_stmt: &mut S, on_expr: &mut E)
where
    S: FnMut(&Stmt),
    E: FnMut(&Expr),
{
    for s in &program.stmts {
        walk_stmt(s, on_stmt, on_expr);
    }
}

/// Visit every expression in `program`.
pub(crate) fn for_each_expr<E: FnMut(&Expr)>(program: &Program, f: &mut E) {
    walk(program, &mut |_| {}, f);
}

/// Visit every statement in `program`.
pub(crate) fn for_each_stmt<S: FnMut(&Stmt)>(program: &Program, f: &mut S) {
    walk(program, f, &mut |_| {});
}

fn walk_stmt<S, E>(s: &Stmt, on_s: &mut S, on_e: &mut E)
where
    S: FnMut(&Stmt),
    E: FnMut(&Expr),
{
    on_s(s);
    match &s.kind {
        StmtKind::Expr(e) => walk_expr(e, on_s, on_e),
        StmtKind::Echo(es) => es.iter().for_each(|e| walk_expr(e, on_s, on_e)),
        StmtKind::Return(Some(e)) => walk_expr(e, on_s, on_e),
        StmtKind::Block(b) => b.iter().for_each(|st| walk_stmt(st, on_s, on_e)),
        StmtKind::If { cond, then, elseifs, els } => {
            walk_expr(cond, on_s, on_e);
            walk_stmt(then, on_s, on_e);
            for ei in elseifs {
                walk_expr(&ei.cond, on_s, on_e);
                walk_stmt(&ei.body, on_s, on_e);
            }
            if let Some(e) = els {
                walk_stmt(e, on_s, on_e);
            }
        }
        StmtKind::While { cond, body } => {
            walk_expr(cond, on_s, on_e);
            walk_stmt(body, on_s, on_e);
        }
        StmtKind::DoWhile { body, cond } => {
            walk_stmt(body, on_s, on_e);
            walk_expr(cond, on_s, on_e);
        }
        StmtKind::For { init, cond, update, body } => {
            for e in init.iter().chain(cond).chain(update) {
                walk_expr(e, on_s, on_e);
            }
            walk_stmt(body, on_s, on_e);
        }
        StmtKind::Foreach { subject, key, value, body, .. } => {
            walk_expr(subject, on_s, on_e);
            if let Some(k) = key {
                walk_expr(k, on_s, on_e);
            }
            walk_expr(value, on_s, on_e);
            walk_stmt(body, on_s, on_e);
        }
        StmtKind::Switch { subject, cases } => {
            walk_expr(subject, on_s, on_e);
            for c in cases {
                if let Some(t) = &c.test {
                    walk_expr(t, on_s, on_e);
                }
                c.body.iter().for_each(|st| walk_stmt(st, on_s, on_e));
            }
        }
        StmtKind::Try { body, catches, finally } => {
            body.iter().for_each(|st| walk_stmt(st, on_s, on_e));
            for c in catches {
                c.body.iter().for_each(|st| walk_stmt(st, on_s, on_e));
            }
            if let Some(f) = finally {
                f.iter().for_each(|st| walk_stmt(st, on_s, on_e));
            }
        }
        StmtKind::Break(o) | StmtKind::Continue(o) => {
            if let Some(e) = o {
                walk_expr(e, on_s, on_e);
            }
        }
        StmtKind::Global(es) | StmtKind::Unset(es) => es.iter().for_each(|e| walk_expr(e, on_s, on_e)),
        StmtKind::StaticVars(vars) => {
            for v in vars {
                if let Some(e) = &v.default {
                    walk_expr(e, on_s, on_e);
                }
            }
        }
        StmtKind::Declare { directives, body } => {
            for (_, e) in directives {
                walk_expr(e, on_s, on_e);
            }
            if let Some(b) = body {
                walk_stmt(b, on_s, on_e);
            }
        }
        StmtKind::Namespace { body: Some(b), .. } => b.iter().for_each(|st| walk_stmt(st, on_s, on_e)),
        StmtKind::Function(fd) => {
            walk_params(&fd.params, on_s, on_e);
            fd.body.iter().for_each(|st| walk_stmt(st, on_s, on_e));
        }
        StmtKind::Class(c) => walk_class(c, on_s, on_e),
        StmtKind::ConstDecl { consts, .. } => consts.iter().for_each(|c| walk_expr(&c.value, on_s, on_e)),
        // No nested expressions/statements: Use, GroupUse, Goto, Label,
        // HaltCompiler, InlineHtml, Nop, Error.
        _ => {}
    }
}

fn walk_params<S, E>(params: &[Param], on_s: &mut S, on_e: &mut E)
where
    S: FnMut(&Stmt),
    E: FnMut(&Expr),
{
    for p in params {
        if let Some(d) = &p.default {
            walk_expr(d, on_s, on_e);
        }
        walk_attrs(&p.attrs, on_s, on_e);
    }
}

fn walk_attrs<S, E>(attrs: &[AttributeGroup], on_s: &mut S, on_e: &mut E)
where
    S: FnMut(&Stmt),
    E: FnMut(&Expr),
{
    for group in attrs {
        for attr in &group.attrs {
            if let Some(args) = &attr.args {
                args.iter().for_each(|a| walk_expr(&a.value, on_s, on_e));
            }
        }
    }
}

fn walk_class<S, E>(c: &ClassDecl, on_s: &mut S, on_e: &mut E)
where
    S: FnMut(&Stmt),
    E: FnMut(&Expr),
{
    walk_attrs(&c.attrs, on_s, on_e);
    for m in &c.members {
        match m {
            Member::Method(md) => {
                walk_params(&md.params, on_s, on_e);
                if let Some(body) = &md.body {
                    body.iter().for_each(|st| walk_stmt(st, on_s, on_e));
                }
            }
            Member::Property(pd) => {
                for elem in &pd.props {
                    if let Some(d) = &elem.default {
                        walk_expr(d, on_s, on_e);
                    }
                    if let Some(hooks) = &elem.hooks {
                        for h in hooks {
                            walk_hook(h, on_s, on_e);
                        }
                    }
                }
            }
            Member::ClassConst(cd) => cd.consts.iter().for_each(|c| walk_expr(&c.value, on_s, on_e)),
            Member::EnumCase(ec) => {
                if let Some(v) = &ec.value {
                    walk_expr(v, on_s, on_e);
                }
            }
            Member::TraitUse(_) => {}
        }
    }
}

fn walk_hook<S, E>(h: &PropertyHook, on_s: &mut S, on_e: &mut E)
where
    S: FnMut(&Stmt),
    E: FnMut(&Expr),
{
    if let Some(params) = &h.params {
        walk_params(params, on_s, on_e);
    }
    match &h.body {
        HookBody::Block(stmts) => stmts.iter().for_each(|st| walk_stmt(st, on_s, on_e)),
        HookBody::Short(e) => walk_expr(e, on_s, on_e),
        HookBody::Abstract => {}
    }
}

fn walk_expr<S, E>(e: &Expr, on_s: &mut S, on_e: &mut E)
where
    S: FnMut(&Stmt),
    E: FnMut(&Expr),
{
    on_e(e);
    let go = |x: &Expr, on_s: &mut S, on_e: &mut E| walk_expr(x, on_s, on_e);
    match &e.kind {
        ExprKind::Int(_) | ExprKind::Float(_) | ExprKind::Str(_) | ExprKind::Variable(_) | ExprKind::Name(_) | ExprKind::Error => {}
        ExprKind::Interpolated(parts) | ExprKind::ShellExec(parts) => parts.iter().for_each(|p| go(p, on_s, on_e)),
        ExprKind::VariableVariable(x) | ExprKind::DollarBrace(x) => go(x, on_s, on_e),
        ExprKind::Array { items, .. } => {
            for it in items {
                if let Some(k) = &it.key {
                    go(k, on_s, on_e);
                }
                if let Some(v) = &it.value {
                    go(v, on_s, on_e);
                }
            }
        }
        ExprKind::Call { callee, args } => {
            go(callee, on_s, on_e);
            walk_args(args, on_s, on_e);
        }
        ExprKind::MethodCall { recv, method, args, .. } => {
            go(recv, on_s, on_e);
            walk_member(method, on_s, on_e);
            walk_args(args, on_s, on_e);
        }
        ExprKind::StaticCall { class, method, args } => {
            go(class, on_s, on_e);
            walk_member(method, on_s, on_e);
            walk_args(args, on_s, on_e);
        }
        ExprKind::New { class, args } => {
            go(class, on_s, on_e);
            walk_args(args, on_s, on_e);
        }
        ExprKind::NewAnon { class, args } => {
            walk_class(class, on_s, on_e);
            walk_args(args, on_s, on_e);
        }
        ExprKind::Index { base, index } => {
            go(base, on_s, on_e);
            if let Some(i) = index {
                go(i, on_s, on_e);
            }
        }
        ExprKind::Prop { base, name, .. } => {
            go(base, on_s, on_e);
            walk_member(name, on_s, on_e);
        }
        ExprKind::StaticProp { class, name } => {
            go(class, on_s, on_e);
            walk_member(name, on_s, on_e);
        }
        ExprKind::ClassConst { class, name } => {
            go(class, on_s, on_e);
            walk_member(name, on_s, on_e);
        }
        ExprKind::Unary { expr, .. } | ExprKind::Cast { expr, .. } => go(expr, on_s, on_e),
        ExprKind::Binary { lhs, rhs, .. }
        | ExprKind::Assign { target: lhs, rhs }
        | ExprKind::AssignOp { target: lhs, rhs, .. }
        | ExprKind::AssignRef { target: lhs, rhs }
        | ExprKind::Coalesce { lhs, rhs } => {
            go(lhs, on_s, on_e);
            go(rhs, on_s, on_e);
        }
        ExprKind::Ternary { cond, then, els } => {
            go(cond, on_s, on_e);
            if let Some(t) = then {
                go(t, on_s, on_e);
            }
            go(els, on_s, on_e);
        }
        ExprKind::PreInc(x) | ExprKind::PreDec(x) | ExprKind::PostInc(x) | ExprKind::PostDec(x) => go(x, on_s, on_e),
        ExprKind::Instanceof { expr, class } => {
            go(expr, on_s, on_e);
            go(class, on_s, on_e);
        }
        ExprKind::Clone(x) | ExprKind::Print(x) | ExprKind::Throw(x) | ExprKind::ErrorSuppress(x) | ExprKind::YieldFrom(x) | ExprKind::Eval(x) | ExprKind::Empty(x) => {
            go(x, on_s, on_e)
        }
        ExprKind::Yield { key, value } => {
            if let Some(k) = key {
                go(k, on_s, on_e);
            }
            if let Some(v) = value {
                go(v, on_s, on_e);
            }
        }
        ExprKind::Exit(Some(x)) => go(x, on_s, on_e),
        ExprKind::Match { subject, arms } => {
            go(subject, on_s, on_e);
            for arm in arms {
                if let Some(conds) = &arm.conds {
                    conds.iter().for_each(|c| go(c, on_s, on_e));
                }
                go(&arm.body, on_s, on_e);
            }
        }
        ExprKind::Include { expr, .. } => go(expr, on_s, on_e),
        ExprKind::Isset(es) => es.iter().for_each(|e| go(e, on_s, on_e)),
        ExprKind::Closure(c) => {
            walk_params(&c.params, on_s, on_e);
            c.body.iter().for_each(|st| walk_stmt(st, on_s, on_e));
        }
        ExprKind::ArrowFn(a) => {
            walk_params(&a.params, on_s, on_e);
            walk_expr(&a.body, on_s, on_e);
        }
        ExprKind::Paren(x) => go(x, on_s, on_e),
        // `#[non_exhaustive]`: anything new is visited but not descended into.
        _ => {}
    }
}

fn walk_args<S, E>(args: &[Arg], on_s: &mut S, on_e: &mut E)
where
    S: FnMut(&Stmt),
    E: FnMut(&Expr),
{
    args.iter().for_each(|a| walk_expr(&a.value, on_s, on_e));
}

fn walk_member<S, E>(m: &MemberName, on_s: &mut S, on_e: &mut E)
where
    S: FnMut(&Stmt),
    E: FnMut(&Expr),
{
    if let MemberName::Expr(e) = m {
        walk_expr(e, on_s, on_e);
    }
}
