//! Shared declaration traversal for rules.

use crate::FileAnalysis;
use php_ast::{
    ClassDecl, Expr, ExprKind, FunctionDecl, Member, MethodDecl, Program, PropElem, PropertyDecl,
    Stmt, StmtKind,
};
use php_intern::Interner;
use php_resolve::{for_each_region, Scope};

/// Visit every named class-like declaration with its namespace scope and FQN.
pub(crate) fn for_each_class_like(fa: &FileAnalysis, mut f: impl FnMut(&Scope, &str, &ClassDecl)) {
    for fact in fa.facts.classes() {
        f(&fact.scope, &fact.fqn, fact.decl);
    }
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
            visit_decls_in_exprs(st, &mut |decl| {
                if let Decl::Class(class) = decl {
                    f(scope, &class_like_fqn(interner, scope, class), class);
                }
            });
        }
    });
}

/// Visit every named function declaration with its namespace scope.
pub(crate) fn for_each_named_function(fa: &FileAnalysis, mut f: impl FnMut(&Scope, &FunctionDecl)) {
    for fact in fa.facts.functions() {
        f(&fact.scope, fact.decl);
    }
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
            visit_decls_in_exprs(st, &mut |decl| {
                if let Decl::Function(func) = decl {
                    f(scope, func);
                }
            });
        }
    });
}

/// Visit every method declaration, paired with its class scope and FQN.
pub(crate) fn for_each_method(
    fa: &FileAnalysis,
    mut f: impl FnMut(&Scope, &str, &ClassDecl, &MethodDecl),
) {
    for fact in fa.facts.methods() {
        f(&fact.scope, &fact.class_fqn, fact.class, fact.decl);
    }
}

/// Visit every property declaration.
pub(crate) fn for_each_property(
    fa: &FileAnalysis,
    mut f: impl FnMut(&str, &ClassDecl, &PropertyDecl),
) {
    for fact in fa.facts.properties() {
        f(&fact.class_fqn, fact.class, fact.decl);
    }
}

/// Visit every property element.
pub(crate) fn for_each_property_elem(
    fa: &FileAnalysis,
    mut f: impl FnMut(&str, &ClassDecl, &PropertyDecl, &PropElem),
) {
    for fact in fa.facts.property_elems() {
        f(&fact.class_fqn, fact.class, fact.property, fact.elem);
    }
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

/// The name a class-like is keyed by. Anonymous classes share the placeholder
/// PHP itself uses in messages; it deliberately matches nothing in the
/// reflection index, so the rules that gate on a class being indexed (member
/// existence, hierarchy checks) skip them rather than judging them against a
/// definition they cannot see.
fn class_like_fqn(interner: &Interner, scope: &Scope, class: &ClassDecl) -> String {
    match class.name {
        Some(name) => scope.qualify(interner.resolve(name)),
        None => crate::symbols::ANONYMOUS_CLASS.to_string(),
    }
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

/// Report `class` and every declaration nested in its method bodies.
fn visit_class_decl<'a>(class: &'a ClassDecl, f: &mut impl FnMut(Decl<'a>)) {
    f(Decl::Class(class));
    for member in &class.members {
        if let Member::Method(method) = member {
            if let Some(body) = &method.body {
                for st in body.iter() {
                    visit_decl_stmt(st, f);
                }
            }
        }
    }
}

/// Report the declarations that live in *expression* position, which
/// [`visit_decl_stmt`] cannot reach: anonymous classes, and anything declared
/// inside a closure body.
///
/// Without this, `new class { … }` and `function () { class C {} }` were
/// invisible to every declaration-driven rule — no `return.type`, no
/// `missingType.*`, nothing — which silently excluded idioms as common as
/// Laravel's anonymous migrations from analysis entirely.
///
/// This walk **crosses** scopes, so one call per top-level statement finds
/// closures and anonymous classes at any depth. Its results are disjoint from
/// the statement walk's (that one never descends into expressions), so the two
/// together visit each declaration exactly once.
fn visit_decls_in_exprs<'a>(st: &'a Stmt, f: &mut impl FnMut(Decl<'a>)) {
    php_ast::walk::for_each_expr_in_stmt(st, &mut |e| match &e.kind {
        ExprKind::NewAnon { class, .. } => visit_class_decl(class, f),
        // Only statement positions here: the body's own expressions are already
        // covered by this same crossing walk.
        ExprKind::Closure(c) => {
            for st in &c.body {
                visit_decl_stmt(st, f);
            }
        }
        _ => {}
    });
}

fn visit_decl_stmt<'a>(st: &'a Stmt, f: &mut impl FnMut(Decl<'a>)) {
    match &st.kind {
        StmtKind::Function(func) => {
            f(Decl::Function(func));
            for st in func.body.iter() {
                visit_decl_stmt(st, f);
            }
        }
        StmtKind::Class(class) => visit_class_decl(class, f),
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

#[cfg(test)]
mod tests {
    /// Declarations that live in expression position — anonymous classes, and
    /// anything declared inside a closure body — must reach the shared
    /// traversal, or every declaration-driven rule is blind to them.
    #[test]
    fn expression_position_declarations_are_visited() {
        let src = "<?php
            $a = new class { public function m(): int { return 1; } };
            $f = function () { class InClosure {} function in_closure() {} };
            function named() {}
            class Named {}";
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "{:?}", r.diagnostics);

        let mut classes = Vec::new();
        super::for_each_class_like_in(&r.program, &r.interner, &mut |_s, fqn, _c| {
            classes.push(fqn.to_string());
        });
        classes.sort();
        assert_eq!(classes, ["InClosure", "Named", "class@anonymous"]);

        let mut functions = Vec::new();
        super::for_each_named_function_in(&r.program, &r.interner, &mut |_s, f| {
            functions.push(r.interner.resolve(f.name).to_string());
        });
        functions.sort();
        assert_eq!(functions, ["in_closure", "named"]);
    }

    /// The statement walk and the expression walk must not both report the same
    /// declaration — a duplicate here becomes a duplicate diagnostic.
    #[test]
    fn nested_declarations_are_visited_exactly_once() {
        let src = "<?php
            $a = new class {
                public function m() {
                    $b = new class { public function inner() {} };
                    class DeepNamed {}
                }
            };
            $f = function () { $g = function () { class Deeper {} }; };";
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "{:?}", r.diagnostics);
        // Compare by identity, not name: two distinct anonymous classes share
        // the same placeholder FQN, so names cannot tell "two classes" from
        // "one class visited twice".
        let mut seen: Vec<(*const php_ast::ClassDecl, String)> = Vec::new();
        super::for_each_class_like_in(&r.program, &r.interner, &mut |_s, fqn, c| {
            seen.push((c as *const _, fqn.to_string()));
        });
        let mut ptrs: Vec<_> = seen.iter().map(|(p, _)| *p).collect();
        let total = ptrs.len();
        ptrs.sort();
        ptrs.dedup();
        assert_eq!(
            ptrs.len(),
            total,
            "a declaration was visited twice: {:?}",
            seen.iter().map(|(_, n)| n).collect::<Vec<_>>()
        );
        let names: Vec<_> = seen.iter().map(|(_, n)| n.as_str()).collect();
        assert!(names.contains(&"DeepNamed"), "{names:?}");
        assert!(names.contains(&"Deeper"), "{names:?}");
        assert_eq!(
            names.iter().filter(|n| **n == "class@anonymous").count(),
            2,
            "both anonymous classes should be visited: {names:?}"
        );
    }
}
