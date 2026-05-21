//! Shared declaration traversal for rules.

use crate::FileAnalysis;
use php_ast::{
    ClassDecl, Expr, FunctionDecl, Member, MethodDecl, Program, PropElem, PropertyDecl, Stmt,
    StmtKind,
};
use php_intern::Interner;
use php_resolve::{for_each_region, Scope};

/// Visit every named class-like declaration with its namespace scope and FQN.
pub(crate) fn for_each_class_like(fa: &FileAnalysis, mut f: impl FnMut(&Scope, &str, &ClassDecl)) {
    for_each_class_like_in(fa.program, fa.interner, &mut f);
}

/// Visit every named class-like declaration in `program`.
pub(crate) fn for_each_class_like_in(
    program: &Program,
    interner: &Interner,
    f: &mut impl FnMut(&Scope, &str, &ClassDecl),
) {
    for_each_region(&program.stmts, interner, |scope, region| {
        for st in region {
            visit_class_like_stmt(interner, scope, st, f);
        }
    });
}

/// Visit every named function declaration with its namespace scope.
pub(crate) fn for_each_named_function(fa: &FileAnalysis, mut f: impl FnMut(&Scope, &FunctionDecl)) {
    for_each_named_function_in(fa.program, fa.interner, &mut f);
}

/// Visit every named function declaration in `program`.
pub(crate) fn for_each_named_function_in(
    program: &Program,
    interner: &Interner,
    f: &mut impl FnMut(&Scope, &FunctionDecl),
) {
    for_each_region(&program.stmts, interner, |scope, region| {
        for st in region {
            visit_function_stmt(st, scope, f);
        }
    });
}

/// Visit every method declaration, paired with its class scope and FQN.
pub(crate) fn for_each_method(
    fa: &FileAnalysis,
    mut f: impl FnMut(&Scope, &str, &ClassDecl, &MethodDecl),
) {
    for_each_class_like(fa, |scope, fqn, class| {
        for member in &class.members {
            if let Member::Method(method) = member {
                f(scope, fqn, class, method);
            }
        }
    });
}

/// Visit every property declaration.
pub(crate) fn for_each_property(
    fa: &FileAnalysis,
    mut f: impl FnMut(&str, &ClassDecl, &PropertyDecl),
) {
    for_each_class_like(fa, |_scope, fqn, class| {
        for member in &class.members {
            if let Member::Property(property) = member {
                f(fqn, class, property);
            }
        }
    });
}

/// Visit every property element.
pub(crate) fn for_each_property_elem(
    fa: &FileAnalysis,
    mut f: impl FnMut(&str, &ClassDecl, &PropertyDecl, &PropElem),
) {
    for_each_property(fa, |fqn, class, property| {
        for elem in &property.props {
            f(fqn, class, property, elem);
        }
    });
}

/// Visit every return statement in `body`, descending control-flow statements
/// but not nested function/class scopes.
pub(crate) fn collect_returns_in_body<'a>(body: &'a [Stmt], f: &mut impl FnMut(Option<&'a Expr>)) {
    for st in body {
        collect_returns_in_stmt(st, f);
    }
}

fn collect_returns_in_stmt<'a>(st: &'a Stmt, f: &mut impl FnMut(Option<&'a Expr>)) {
    match &st.kind {
        StmtKind::Return(expr) => f(expr.as_ref()),
        StmtKind::Block(body) => collect_returns_in_body(body, f),
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            collect_returns_in_stmt(then, f);
            for elseif in elseifs {
                collect_returns_in_stmt(&elseif.body, f);
            }
            if let Some(els) = els {
                collect_returns_in_stmt(els, f);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => collect_returns_in_stmt(body, f),
        StmtKind::Switch { cases, .. } => {
            for case in cases {
                collect_returns_in_body(&case.body, f);
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            collect_returns_in_body(body, f);
            for catch in catches {
                collect_returns_in_body(&catch.body, f);
            }
            if let Some(finally) = finally {
                collect_returns_in_body(finally, f);
            }
        }
        StmtKind::Declare {
            body: Some(body), ..
        } => collect_returns_in_stmt(body, f),
        StmtKind::Expr(_)
        | StmtKind::Echo(_)
        | StmtKind::Break(_)
        | StmtKind::Continue(_)
        | StmtKind::Goto(_)
        | StmtKind::Label(_)
        | StmtKind::Global(_)
        | StmtKind::StaticVars(_)
        | StmtKind::Unset(_)
        | StmtKind::Declare { body: None, .. }
        | StmtKind::Namespace { .. }
        | StmtKind::Use(_)
        | StmtKind::GroupUse { .. }
        | StmtKind::Function(_)
        | StmtKind::Class(_)
        | StmtKind::ConstDecl { .. }
        | StmtKind::HaltCompiler(_)
        | StmtKind::InlineHtml(_)
        | StmtKind::Nop
        | StmtKind::Error => {}
    }
}

fn visit_class_like_stmt(
    interner: &Interner,
    scope: &Scope,
    st: &Stmt,
    f: &mut impl FnMut(&Scope, &str, &ClassDecl),
) {
    visit_decl_stmt(st, &mut |decl| match decl {
        Decl::Class(class) => {
            if let Some(name) = class.name {
                let fqn = scope.qualify(interner.resolve(name));
                f(scope, &fqn, class);
            }
        }
        Decl::Function(_) => {}
    });
}

fn visit_function_stmt(st: &Stmt, scope: &Scope, f: &mut impl FnMut(&Scope, &FunctionDecl)) {
    visit_decl_stmt(st, &mut |decl| match decl {
        Decl::Function(func) => f(scope, func),
        Decl::Class(_) => {}
    });
}

enum Decl<'a> {
    Function(&'a FunctionDecl),
    Class(&'a ClassDecl),
}

fn visit_decl_stmt<'a>(st: &'a Stmt, f: &mut impl FnMut(Decl<'a>)) {
    match &st.kind {
        StmtKind::Function(func) => {
            f(Decl::Function(func));
            for st in &func.body {
                visit_decl_stmt(st, f);
            }
        }
        StmtKind::Class(class) => {
            f(Decl::Class(class));
            for member in &class.members {
                if let Member::Method(method) = member {
                    if let Some(body) = &method.body {
                        for st in body {
                            visit_decl_stmt(st, f);
                        }
                    }
                }
            }
        }
        StmtKind::Block(body) => {
            for st in body {
                visit_decl_stmt(st, f);
            }
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            visit_decl_stmt(then, f);
            for elseif in elseifs {
                visit_decl_stmt(&elseif.body, f);
            }
            if let Some(els) = els {
                visit_decl_stmt(els, f);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => visit_decl_stmt(body, f),
        StmtKind::Switch { cases, .. } => {
            for case in cases {
                for st in &case.body {
                    visit_decl_stmt(st, f);
                }
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for st in body {
                visit_decl_stmt(st, f);
            }
            for catch in catches {
                for st in &catch.body {
                    visit_decl_stmt(st, f);
                }
            }
            if let Some(finally) = finally {
                for st in finally {
                    visit_decl_stmt(st, f);
                }
            }
        }
        StmtKind::Declare {
            body: Some(body), ..
        } => visit_decl_stmt(body, f),
        StmtKind::Expr(_)
        | StmtKind::Echo(_)
        | StmtKind::Return(_)
        | StmtKind::Break(_)
        | StmtKind::Continue(_)
        | StmtKind::Goto(_)
        | StmtKind::Label(_)
        | StmtKind::Global(_)
        | StmtKind::StaticVars(_)
        | StmtKind::Unset(_)
        | StmtKind::Declare { body: None, .. }
        | StmtKind::Namespace { .. }
        | StmtKind::Use(_)
        | StmtKind::GroupUse { .. }
        | StmtKind::ConstDecl { .. }
        | StmtKind::HaltCompiler(_)
        | StmtKind::InlineHtml(_)
        | StmtKind::Nop
        | StmtKind::Error => {}
    }
}
