//! A reusable AST traversal — the analogue of phpstan's "node type + processNode"
//! dispatch. [`walk`] visits every statement and expression in a program
//! (pre-order). The `cross` flag controls whether traversal descends into nested
//! *function-like scopes* (named functions, class member bodies, closures, arrow
//! fns, anonymous-class bodies): `for_each_expr`/`for_each_stmt` cross every
//! boundary; [`for_each_expr_in_scope`] stops at them (the expressions that
//! belong to one scope), which is what flow-sensitive passes need.

use crate::*;

/// Visit every statement and expression in `program` (crossing all scopes).
pub fn walk<'a, S, E>(program: &'a Program, on_stmt: &mut S, on_expr: &mut E)
where
    S: FnMut(&'a Stmt),
    E: FnMut(&'a Expr),
{
    for s in &program.stmts {
        walk_stmt(s, on_stmt, on_expr, true);
    }
}

/// Visit every expression in `program` (crossing all scopes).
pub fn for_each_expr<'a, E: FnMut(&'a Expr)>(program: &'a Program, f: &mut E) {
    walk(program, &mut |_| {}, f);
}

/// Visit every statement in `program` (crossing all scopes).
pub fn for_each_stmt<'a, S: FnMut(&'a Stmt)>(program: &'a Program, f: &mut S) {
    walk(program, f, &mut |_| {});
}

/// Visit every statement within a single `stmt` (crossing all scopes).
pub fn for_each_stmt_in_stmt<'a, S: FnMut(&'a Stmt)>(stmt: &'a Stmt, f: &mut S) {
    walk_stmt(stmt, f, &mut |_| {}, true);
}

/// Visit every expression within a single `stmt` (crossing all scopes).
pub fn for_each_expr_in_stmt<'a, E: FnMut(&'a Expr)>(stmt: &'a Stmt, f: &mut E) {
    walk_stmt(stmt, &mut |_| {}, f, true);
}

/// Visit the expressions of `stmt` that belong to its *own* scope — descends
/// control flow but stops at nested function-like scopes (closures, arrow fns,
/// anonymous classes, nested function/class declarations). The closure/anon-class
/// node itself is visited; its body is not.
pub fn for_each_expr_in_scope<'a, E: FnMut(&'a Expr)>(stmt: &'a Stmt, f: &mut E) {
    walk_stmt(stmt, &mut |_| {}, f, false);
}

/// Visit `e` and every sub-expression in its *own* scope (stops at nested
/// closures / arrow-fn bodies). Used by flow-sensitive passes to record the
/// expressions at a single flow point (one statement's environment), without
/// descending into child-statement blocks the caller handles separately.
pub fn for_each_subexpr<'a, E: FnMut(&'a Expr)>(e: &'a Expr, f: &mut E) {
    walk_expr(e, &mut |_| {}, f, false);
}

fn walk_stmt<'a, S, E>(s: &'a Stmt, on_s: &mut S, on_e: &mut E, cross: bool)
where
    S: FnMut(&'a Stmt),
    E: FnMut(&'a Expr),
{
    on_s(s);
    match &s.kind {
        StmtKind::Expr(e) => walk_expr(e, on_s, on_e, cross),
        StmtKind::Echo(es) => es.iter().for_each(|e| walk_expr(e, on_s, on_e, cross)),
        StmtKind::Return(Some(e)) => walk_expr(e, on_s, on_e, cross),
        StmtKind::Block(b) => b.iter().for_each(|st| walk_stmt(st, on_s, on_e, cross)),
        StmtKind::If {
            cond,
            then,
            elseifs,
            els,
        } => {
            walk_expr(cond, on_s, on_e, cross);
            walk_stmt(then, on_s, on_e, cross);
            for ei in elseifs {
                walk_expr(&ei.cond, on_s, on_e, cross);
                walk_stmt(&ei.body, on_s, on_e, cross);
            }
            if let Some(e) = els {
                walk_stmt(e, on_s, on_e, cross);
            }
        }
        StmtKind::While { cond, body } => {
            walk_expr(cond, on_s, on_e, cross);
            walk_stmt(body, on_s, on_e, cross);
        }
        StmtKind::DoWhile { body, cond } => {
            walk_stmt(body, on_s, on_e, cross);
            walk_expr(cond, on_s, on_e, cross);
        }
        StmtKind::For {
            init,
            cond,
            update,
            body,
        } => {
            for e in init.iter().chain(cond).chain(update) {
                walk_expr(e, on_s, on_e, cross);
            }
            walk_stmt(body, on_s, on_e, cross);
        }
        StmtKind::Foreach {
            subject,
            key,
            value,
            body,
            ..
        } => {
            walk_expr(subject, on_s, on_e, cross);
            if let Some(k) = key {
                walk_expr(k, on_s, on_e, cross);
            }
            walk_expr(value, on_s, on_e, cross);
            walk_stmt(body, on_s, on_e, cross);
        }
        StmtKind::Switch { subject, cases } => {
            walk_expr(subject, on_s, on_e, cross);
            for c in cases {
                if let Some(t) = &c.test {
                    walk_expr(t, on_s, on_e, cross);
                }
                c.body
                    .iter()
                    .for_each(|st| walk_stmt(st, on_s, on_e, cross));
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter().for_each(|st| walk_stmt(st, on_s, on_e, cross));
            for c in catches {
                c.body
                    .iter()
                    .for_each(|st| walk_stmt(st, on_s, on_e, cross));
            }
            if let Some(f) = finally {
                f.iter().for_each(|st| walk_stmt(st, on_s, on_e, cross));
            }
        }
        StmtKind::Break(o) | StmtKind::Continue(o) => {
            if let Some(e) = o {
                walk_expr(e, on_s, on_e, cross);
            }
        }
        StmtKind::Global(es) | StmtKind::Unset(es) => {
            es.iter().for_each(|e| walk_expr(e, on_s, on_e, cross))
        }
        StmtKind::StaticVars(vars) => {
            for v in vars {
                if let Some(e) = &v.default {
                    walk_expr(e, on_s, on_e, cross);
                }
            }
        }
        StmtKind::Declare { directives, body } => {
            for (_, e) in directives {
                walk_expr(e, on_s, on_e, cross);
            }
            if let Some(b) = body {
                walk_stmt(b, on_s, on_e, cross);
            }
        }
        StmtKind::Namespace { body: Some(b), .. } => {
            b.iter().for_each(|st| walk_stmt(st, on_s, on_e, cross))
        }
        // Nested declarations introduce new scopes: only descend when crossing.
        StmtKind::Function(fd) if cross => {
            walk_params(&fd.params, on_s, on_e);
            fd.body
                .iter()
                .for_each(|st| walk_stmt(st, on_s, on_e, true));
        }
        StmtKind::Class(c) if cross => walk_class(c, on_s, on_e),
        StmtKind::ConstDecl { consts, .. } => consts
            .iter()
            .for_each(|c| walk_expr(&c.value, on_s, on_e, cross)),
        StmtKind::Return(None)
        | StmtKind::Function(_)
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

fn walk_params<'a, S, E>(params: &'a [Param], on_s: &mut S, on_e: &mut E)
where
    S: FnMut(&'a Stmt),
    E: FnMut(&'a Expr),
{
    for p in params {
        if let Some(d) = &p.default {
            walk_expr(d, on_s, on_e, true);
        }
        walk_attrs(&p.attrs, on_s, on_e);
    }
}

fn walk_attrs<'a, S, E>(attrs: &'a [AttributeGroup], on_s: &mut S, on_e: &mut E)
where
    S: FnMut(&'a Stmt),
    E: FnMut(&'a Expr),
{
    for group in attrs {
        for attr in &group.attrs {
            if let Some(args) = &attr.args {
                args.iter()
                    .for_each(|a| walk_expr(&a.value, on_s, on_e, true));
            }
        }
    }
}

fn walk_class<'a, S, E>(c: &'a ClassDecl, on_s: &mut S, on_e: &mut E)
where
    S: FnMut(&'a Stmt),
    E: FnMut(&'a Expr),
{
    walk_attrs(&c.attrs, on_s, on_e);
    for m in &c.members {
        match m {
            Member::Method(md) => {
                walk_params(&md.params, on_s, on_e);
                if let Some(body) = &md.body {
                    body.iter().for_each(|st| walk_stmt(st, on_s, on_e, true));
                }
            }
            Member::Property(pd) => {
                for elem in &pd.props {
                    if let Some(d) = &elem.default {
                        walk_expr(d, on_s, on_e, true);
                    }
                    if let Some(hooks) = &elem.hooks {
                        for h in hooks {
                            walk_hook(h, on_s, on_e);
                        }
                    }
                }
            }
            Member::ClassConst(cd) => cd
                .consts
                .iter()
                .for_each(|c| walk_expr(&c.value, on_s, on_e, true)),
            Member::EnumCase(ec) => {
                if let Some(v) = &ec.value {
                    walk_expr(v, on_s, on_e, true);
                }
            }
            Member::TraitUse(_) => {}
        }
    }
}

fn walk_hook<'a, S, E>(h: &'a PropertyHook, on_s: &mut S, on_e: &mut E)
where
    S: FnMut(&'a Stmt),
    E: FnMut(&'a Expr),
{
    if let Some(params) = &h.params {
        walk_params(params, on_s, on_e);
    }
    match &h.body {
        HookBody::Block(stmts) => stmts.iter().for_each(|st| walk_stmt(st, on_s, on_e, true)),
        HookBody::Short(e) => walk_expr(e, on_s, on_e, true),
        HookBody::Abstract => {}
    }
}

fn walk_expr<'a, S, E>(e: &'a Expr, on_s: &mut S, on_e: &mut E, cross: bool)
where
    S: FnMut(&'a Stmt),
    E: FnMut(&'a Expr),
{
    on_e(e);
    let go = |x: &'a Expr, on_s: &mut S, on_e: &mut E| walk_expr(x, on_s, on_e, cross);
    match &e.kind {
        ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Variable(_)
        | ExprKind::Name(_)
        | ExprKind::Error => {}
        ExprKind::Interpolated(parts) | ExprKind::ShellExec(parts) => {
            parts.iter().for_each(|p| go(p, on_s, on_e))
        }
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
            walk_args(args, on_s, on_e, cross);
        }
        ExprKind::MethodCall {
            recv, method, args, ..
        } => {
            go(recv, on_s, on_e);
            walk_member(method, on_s, on_e, cross);
            walk_args(args, on_s, on_e, cross);
        }
        ExprKind::StaticCall {
            class,
            method,
            args,
        } => {
            go(class, on_s, on_e);
            walk_member(method, on_s, on_e, cross);
            walk_args(args, on_s, on_e, cross);
        }
        ExprKind::New { class, args } => {
            go(class, on_s, on_e);
            walk_args(args, on_s, on_e, cross);
        }
        ExprKind::NewAnon { class, args } => {
            // The constructor arguments are in the current scope; the anonymous
            // class body is its own scope (only descend when crossing).
            walk_args(args, on_s, on_e, cross);
            if cross {
                walk_class(class, on_s, on_e);
            }
        }
        ExprKind::Index { base, index } => {
            go(base, on_s, on_e);
            if let Some(i) = index {
                go(i, on_s, on_e);
            }
        }
        ExprKind::Prop { base, name, .. } => {
            go(base, on_s, on_e);
            walk_member(name, on_s, on_e, cross);
        }
        ExprKind::StaticProp { class, name } => {
            go(class, on_s, on_e);
            walk_member(name, on_s, on_e, cross);
        }
        ExprKind::ClassConst { class, name } => {
            go(class, on_s, on_e);
            walk_member(name, on_s, on_e, cross);
        }
        ExprKind::Unary { expr, .. } | ExprKind::Cast { expr, .. } => go(expr, on_s, on_e),
        ExprKind::Binary { lhs, rhs, .. }
        | ExprKind::Assign { target: lhs, rhs }
        | ExprKind::AssignOp {
            target: lhs, rhs, ..
        }
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
        ExprKind::PreInc(x) | ExprKind::PreDec(x) | ExprKind::PostInc(x) | ExprKind::PostDec(x) => {
            go(x, on_s, on_e)
        }
        ExprKind::Instanceof { expr, class } => {
            go(expr, on_s, on_e);
            go(class, on_s, on_e);
        }
        ExprKind::Clone(x)
        | ExprKind::Print(x)
        | ExprKind::Throw(x)
        | ExprKind::ErrorSuppress(x)
        | ExprKind::YieldFrom(x)
        | ExprKind::Eval(x)
        | ExprKind::Empty(x) => go(x, on_s, on_e),
        ExprKind::Yield { key, value } => {
            if let Some(k) = key {
                go(k, on_s, on_e);
            }
            if let Some(v) = value {
                go(v, on_s, on_e);
            }
        }
        ExprKind::Exit(Some(x)) => go(x, on_s, on_e),
        ExprKind::Exit(None) => {}
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
            if cross {
                walk_params(&c.params, on_s, on_e);
                c.body.iter().for_each(|st| walk_stmt(st, on_s, on_e, true));
            }
        }
        ExprKind::ArrowFn(a) => {
            if cross {
                walk_params(&a.params, on_s, on_e);
                walk_expr(&a.body, on_s, on_e, true);
            }
        }
        ExprKind::Paren(x) => go(x, on_s, on_e),
    }
}

fn walk_args<'a, S, E>(args: &'a [Arg], on_s: &mut S, on_e: &mut E, cross: bool)
where
    S: FnMut(&'a Stmt),
    E: FnMut(&'a Expr),
{
    args.iter()
        .for_each(|a| walk_expr(&a.value, on_s, on_e, cross));
}

fn walk_member<'a, S, E>(m: &'a MemberName, on_s: &mut S, on_e: &mut E, cross: bool)
where
    S: FnMut(&'a Stmt),
    E: FnMut(&'a Expr),
{
    if let MemberName::Expr(e) = m {
        walk_expr(e, on_s, on_e, cross);
    }
}
