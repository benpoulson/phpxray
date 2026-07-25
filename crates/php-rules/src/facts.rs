//! Shared per-file facts for rules.
//!
//! This is intentionally a lightweight index over borrowed AST nodes. It gives
//! rule families common whole-file views without repeatedly walking the AST, but
//! it does not replace flow-sensitive per-scope walkers.

use php_ast::{
    Arg, ArrayItem, BinOp, CastKind, ClassDecl, Expr, ExprKind, FunctionDecl, Member, MemberName,
    MethodDecl, Program, PropElem, PropertyDecl, Stmt, StmtKind, UnOp,
};
use php_intern::Interner;
use php_resolve::{for_each_region, Scope};

/// Borrowed facts collected once for an analyzed file.
pub struct FileFacts<'a> {
    statements: Vec<&'a Stmt>,
    expressions: Vec<&'a Expr>,
    functions: Vec<FunctionDeclFact<'a>>,
    classes: Vec<ClassDeclFact<'a>>,
    methods: Vec<MethodDeclFact<'a>>,
    properties: Vec<PropertyDeclFact<'a>>,
    property_elems: Vec<PropertyElemFact<'a>>,
    function_calls: Vec<CallFact<'a>>,
    method_calls: Vec<MethodCallFact<'a>>,
    scoped_function_calls: Vec<ScopedCallFact<'a>>,
    scoped_method_calls: Vec<ScopedMethodCallFact<'a>>,
    static_calls: Vec<StaticCallFact<'a>>,
    property_fetches: Vec<PropertyFetchFact<'a>>,
    class_consts: Vec<ClassConstFact<'a>>,
    indexes: Vec<IndexFact<'a>>,
    binaries: Vec<BinaryFact<'a>>,
    unaries: Vec<UnaryFact<'a>>,
    casts: Vec<CastFact<'a>>,
    prints: Vec<PrintFact<'a>>,
    arrays: Vec<ArrayFact<'a>>,
    assignments: Vec<AssignmentFact<'a>>,
    news: Vec<NewFact<'a>>,
    clones: Vec<CloneFact<'a>>,
    echoes: Vec<EchoFact<'a>>,
    foreaches: Vec<ForeachFact<'a>>,
    issets: Vec<IssetFact<'a>>,
    empties: Vec<EmptyFact<'a>>,
    coalesces: Vec<CoalesceFact<'a>>,
}

pub(crate) struct FunctionDeclFact<'a> {
    pub(crate) scope: Scope,
    pub(crate) decl: &'a FunctionDecl,
}

pub(crate) struct ClassDeclFact<'a> {
    pub(crate) scope: Scope,
    pub(crate) fqn: String,
    pub(crate) decl: &'a ClassDecl,
}

pub(crate) struct MethodDeclFact<'a> {
    pub(crate) scope: Scope,
    pub(crate) class_fqn: String,
    pub(crate) class: &'a ClassDecl,
    pub(crate) decl: &'a MethodDecl,
}

pub(crate) struct PropertyDeclFact<'a> {
    pub(crate) class_fqn: String,
    pub(crate) class: &'a ClassDecl,
    pub(crate) decl: &'a PropertyDecl,
}

pub(crate) struct PropertyElemFact<'a> {
    pub(crate) class_fqn: String,
    pub(crate) class: &'a ClassDecl,
    pub(crate) property: &'a PropertyDecl,
    pub(crate) elem: &'a PropElem,
}

pub(crate) struct CallFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) callee: &'a Expr,
    pub(crate) args: &'a [Arg],
}

pub(crate) struct MethodCallFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) recv: &'a Expr,
    pub(crate) method: &'a MemberName,
    pub(crate) args: &'a [Arg],
    pub(crate) nullsafe: bool,
}

pub(crate) struct ScopedCallFact<'a> {
    pub(crate) scope: Scope,
    pub(crate) callee: &'a Expr,
    pub(crate) args: &'a [Arg],
}

pub(crate) struct ScopedMethodCallFact<'a> {
    pub(crate) scope: Scope,
    pub(crate) recv: &'a Expr,
    pub(crate) method: &'a MemberName,
    pub(crate) args: &'a [Arg],
}

pub(crate) struct StaticCallFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) class: &'a Expr,
    pub(crate) method: &'a MemberName,
    pub(crate) args: &'a [Arg],
}

pub(crate) struct PropertyFetchFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) base: &'a Expr,
    pub(crate) name: &'a MemberName,
    pub(crate) nullsafe: bool,
}

pub(crate) struct ClassConstFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) name: &'a MemberName,
}

pub(crate) struct IndexFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) base: &'a Expr,
    pub(crate) index: Option<&'a Expr>,
}

pub(crate) struct BinaryFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) op: BinOp,
    pub(crate) lhs: &'a Expr,
    pub(crate) rhs: &'a Expr,
}

pub(crate) struct UnaryFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) op: UnOp,
    pub(crate) inner: &'a Expr,
}

pub(crate) struct CastFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) kind: CastKind,
    pub(crate) inner: &'a Expr,
}

pub(crate) struct PrintFact<'a> {
    pub(crate) inner: &'a Expr,
}

pub(crate) struct ArrayFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) items: &'a [ArrayItem],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AssignmentKind {
    Plain,
    Op(BinOp),
    Ref,
}

pub(crate) struct AssignmentFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) kind: AssignmentKind,
    pub(crate) target: &'a Expr,
    pub(crate) rhs: &'a Expr,
}

pub(crate) struct NewFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) args: &'a [Arg],
}

pub(crate) struct CloneFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) inner: &'a Expr,
}

pub(crate) struct EchoFact<'a> {
    pub(crate) exprs: &'a [Expr],
}

pub(crate) struct ForeachFact<'a> {
    pub(crate) subject: &'a Expr,
    pub(crate) key: Option<&'a Expr>,
    pub(crate) value: &'a Expr,
}

pub(crate) struct IssetFact<'a> {
    pub(crate) vars: &'a [Expr],
}

pub(crate) struct EmptyFact<'a> {
    pub(crate) inner: &'a Expr,
}

pub(crate) struct CoalesceFact<'a> {
    pub(crate) lhs: &'a Expr,
}

impl<'a> FileFacts<'a> {
    pub fn new(program: &'a Program, interner: &'a Interner) -> Self {
        let mut facts = Self {
            statements: Vec::new(),
            expressions: Vec::new(),
            functions: Vec::new(),
            classes: Vec::new(),
            methods: Vec::new(),
            properties: Vec::new(),
            property_elems: Vec::new(),
            function_calls: Vec::new(),
            method_calls: Vec::new(),
            scoped_function_calls: Vec::new(),
            scoped_method_calls: Vec::new(),
            static_calls: Vec::new(),
            property_fetches: Vec::new(),
            class_consts: Vec::new(),
            indexes: Vec::new(),
            binaries: Vec::new(),
            unaries: Vec::new(),
            casts: Vec::new(),
            prints: Vec::new(),
            arrays: Vec::new(),
            assignments: Vec::new(),
            news: Vec::new(),
            clones: Vec::new(),
            echoes: Vec::new(),
            foreaches: Vec::new(),
            issets: Vec::new(),
            empties: Vec::new(),
            coalesces: Vec::new(),
        };

        for_each_region(&program.stmts, interner, |scope, region| {
            for st in region {
                facts.collect_decls(interner, scope, st);
                php_ast::walk::for_each_expr_in_stmt(st, &mut |expr| {
                    facts.collect_scoped_expr(scope, expr);
                });
            }
        });

        php_ast::walk::for_each_stmt(program, &mut |stmt| facts.collect_stmt(stmt));
        php_ast::walk::for_each_expr(program, &mut |expr| facts.collect_expr(expr));
        facts
    }

    pub(crate) fn statements(&self) -> &[&'a Stmt] {
        &self.statements
    }

    pub(crate) fn expressions(&self) -> &[&'a Expr] {
        &self.expressions
    }

    pub(crate) fn functions(&self) -> &[FunctionDeclFact<'a>] {
        &self.functions
    }

    pub(crate) fn classes(&self) -> &[ClassDeclFact<'a>] {
        &self.classes
    }

    pub(crate) fn methods(&self) -> &[MethodDeclFact<'a>] {
        &self.methods
    }

    pub(crate) fn properties(&self) -> &[PropertyDeclFact<'a>] {
        &self.properties
    }

    pub(crate) fn property_elems(&self) -> &[PropertyElemFact<'a>] {
        &self.property_elems
    }

    pub(crate) fn function_calls(&self) -> &[CallFact<'a>] {
        &self.function_calls
    }

    pub(crate) fn method_calls(&self) -> &[MethodCallFact<'a>] {
        &self.method_calls
    }

    pub(crate) fn scoped_function_calls(&self) -> &[ScopedCallFact<'a>] {
        &self.scoped_function_calls
    }

    pub(crate) fn scoped_method_calls(&self) -> &[ScopedMethodCallFact<'a>] {
        &self.scoped_method_calls
    }

    pub(crate) fn static_calls(&self) -> &[StaticCallFact<'a>] {
        &self.static_calls
    }

    pub(crate) fn property_fetches(&self) -> &[PropertyFetchFact<'a>] {
        &self.property_fetches
    }

    pub(crate) fn class_consts(&self) -> &[ClassConstFact<'a>] {
        &self.class_consts
    }

    pub(crate) fn indexes(&self) -> &[IndexFact<'a>] {
        &self.indexes
    }

    pub(crate) fn binaries(&self) -> &[BinaryFact<'a>] {
        &self.binaries
    }

    pub(crate) fn unaries(&self) -> &[UnaryFact<'a>] {
        &self.unaries
    }

    pub(crate) fn casts(&self) -> &[CastFact<'a>] {
        &self.casts
    }

    pub(crate) fn prints(&self) -> &[PrintFact<'a>] {
        &self.prints
    }

    pub(crate) fn arrays(&self) -> &[ArrayFact<'a>] {
        &self.arrays
    }

    pub(crate) fn assignments(&self) -> &[AssignmentFact<'a>] {
        &self.assignments
    }

    pub(crate) fn news(&self) -> &[NewFact<'a>] {
        &self.news
    }

    pub(crate) fn clones(&self) -> &[CloneFact<'a>] {
        &self.clones
    }

    pub(crate) fn echoes(&self) -> &[EchoFact<'a>] {
        &self.echoes
    }

    pub(crate) fn foreaches(&self) -> &[ForeachFact<'a>] {
        &self.foreaches
    }

    pub(crate) fn issets(&self) -> &[IssetFact<'a>] {
        &self.issets
    }

    pub(crate) fn empties(&self) -> &[EmptyFact<'a>] {
        &self.empties
    }

    pub(crate) fn coalesces(&self) -> &[CoalesceFact<'a>] {
        &self.coalesces
    }

    fn collect_stmt(&mut self, stmt: &'a Stmt) {
        self.statements.push(stmt);
        match &stmt.kind {
            StmtKind::Echo(exprs) => self.echoes.push(EchoFact { exprs }),
            StmtKind::Foreach {
                subject,
                key,
                value,
                ..
            } => self.foreaches.push(ForeachFact {
                subject,
                key: key.as_ref(),
                value,
            }),
            _ => {}
        }
    }

    fn collect_expr(&mut self, expr: &'a Expr) {
        self.expressions.push(expr);
        match &expr.kind {
            ExprKind::Call { callee, args } => {
                self.function_calls.push(CallFact { expr, callee, args });
            }
            ExprKind::MethodCall {
                recv,
                method,
                args,
                nullsafe,
            } => {
                self.method_calls.push(MethodCallFact {
                    expr,
                    recv,
                    method,
                    args,
                    nullsafe: *nullsafe,
                });
            }
            ExprKind::StaticCall {
                class,
                method,
                args,
            } => {
                self.static_calls.push(StaticCallFact {
                    expr,
                    class,
                    method,
                    args,
                });
            }
            ExprKind::Prop {
                base,
                name,
                nullsafe,
            } => {
                self.property_fetches.push(PropertyFetchFact {
                    expr,
                    base,
                    name,
                    nullsafe: *nullsafe,
                });
            }
            ExprKind::ClassConst { name, .. } => {
                self.class_consts.push(ClassConstFact { expr, name });
            }
            ExprKind::Index { base, index } => {
                self.indexes.push(IndexFact {
                    expr,
                    base,
                    index: index.as_deref(),
                });
            }
            ExprKind::Binary { op, lhs, rhs } => {
                self.binaries.push(BinaryFact {
                    expr,
                    op: *op,
                    lhs,
                    rhs,
                });
            }
            ExprKind::Unary { op, expr: inner } => {
                self.unaries.push(UnaryFact {
                    expr,
                    op: *op,
                    inner,
                });
            }
            ExprKind::Cast { kind, expr: inner } => {
                self.casts.push(CastFact {
                    expr,
                    kind: *kind,
                    inner,
                });
            }
            ExprKind::Print(inner) => {
                self.prints.push(PrintFact { inner });
            }
            ExprKind::Array { items, .. } => {
                self.arrays.push(ArrayFact { expr, items });
            }
            ExprKind::Assign { target, rhs } => {
                self.assignments.push(AssignmentFact {
                    expr,
                    kind: AssignmentKind::Plain,
                    target,
                    rhs,
                });
            }
            ExprKind::AssignOp { target, rhs, op } => {
                self.assignments.push(AssignmentFact {
                    expr,
                    kind: AssignmentKind::Op(*op),
                    target,
                    rhs,
                });
            }
            ExprKind::AssignRef { target, rhs } => {
                self.assignments.push(AssignmentFact {
                    expr,
                    kind: AssignmentKind::Ref,
                    target,
                    rhs,
                });
            }
            ExprKind::New { args, .. } => {
                self.news.push(NewFact { expr, args });
            }
            ExprKind::Clone(inner) => {
                self.clones.push(CloneFact { expr, inner });
            }
            ExprKind::Isset(vars) => {
                self.issets.push(IssetFact { vars });
            }
            ExprKind::Empty(inner) => {
                self.empties.push(EmptyFact { inner });
            }
            ExprKind::Coalesce { lhs, .. } => {
                self.coalesces.push(CoalesceFact { lhs });
            }
            _ => {}
        }
    }

    fn collect_scoped_expr(&mut self, scope: &Scope, expr: &'a Expr) {
        match &expr.kind {
            ExprKind::Call { callee, args } => {
                self.scoped_function_calls.push(ScopedCallFact {
                    scope: scope.clone(),
                    callee,
                    args,
                });
            }
            ExprKind::MethodCall {
                recv, method, args, ..
            } => {
                self.scoped_method_calls.push(ScopedMethodCallFact {
                    scope: scope.clone(),
                    recv,
                    method,
                    args,
                });
            }
            _ => {}
        }
    }

    fn collect_decls(&mut self, interner: &Interner, scope: &Scope, stmt: &'a Stmt) {
        match &stmt.kind {
            StmtKind::Function(function) => {
                self.functions.push(FunctionDeclFact {
                    scope: scope.clone(),
                    decl: function,
                });
                for child in &function.body {
                    self.collect_decls(interner, scope, child);
                }
            }
            StmtKind::Class(class) => {
                if let Some(name) = class.name {
                    let fqn = scope.qualify(interner.resolve(name));
                    self.classes.push(ClassDeclFact {
                        scope: scope.clone(),
                        fqn: fqn.clone(),
                        decl: class,
                    });
                    for member in &class.members {
                        match member {
                            Member::Method(method) => {
                                self.methods.push(MethodDeclFact {
                                    scope: scope.clone(),
                                    class_fqn: fqn.clone(),
                                    class,
                                    decl: method,
                                });
                                if let Some(body) = &method.body {
                                    for child in body {
                                        self.collect_decls(interner, scope, child);
                                    }
                                }
                            }
                            Member::Property(property) => {
                                self.properties.push(PropertyDeclFact {
                                    class_fqn: fqn.clone(),
                                    class,
                                    decl: property,
                                });
                                for elem in &property.props {
                                    self.property_elems.push(PropertyElemFact {
                                        class_fqn: fqn.clone(),
                                        class,
                                        property,
                                        elem,
                                    });
                                }
                            }
                            Member::ClassConst(_) | Member::EnumCase(_) | Member::TraitUse(_) => {}
                        }
                    }
                }
            }
            StmtKind::Block(body)
            | StmtKind::Namespace {
                body: Some(body), ..
            } => {
                for child in body {
                    self.collect_decls(interner, scope, child);
                }
            }
            StmtKind::If {
                then, elseifs, els, ..
            } => {
                self.collect_decls(interner, scope, then);
                for elseif in elseifs {
                    self.collect_decls(interner, scope, &elseif.body);
                }
                if let Some(els) = els {
                    self.collect_decls(interner, scope, els);
                }
            }
            StmtKind::While { body, .. }
            | StmtKind::DoWhile { body, .. }
            | StmtKind::For { body, .. }
            | StmtKind::Foreach { body, .. }
            | StmtKind::Declare {
                body: Some(body), ..
            } => self.collect_decls(interner, scope, body),
            StmtKind::Switch { cases, .. } => {
                for case in cases {
                    for child in &case.body {
                        self.collect_decls(interner, scope, child);
                    }
                }
            }
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                for child in body {
                    self.collect_decls(interner, scope, child);
                }
                for catch in catches {
                    for child in &catch.body {
                        self.collect_decls(interner, scope, child);
                    }
                }
                if let Some(finally) = finally {
                    for child in finally {
                        self.collect_decls(interner, scope, child);
                    }
                }
            }
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
            | StmtKind::Namespace { body: None, .. }
            | StmtKind::Use(_)
            | StmtKind::GroupUse { .. }
            | StmtKind::ConstDecl { .. }
            | StmtKind::HaltCompiler(_)
            | StmtKind::InlineHtml(_)
            | StmtKind::Nop
            | StmtKind::Error => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_ast::ExprKind;

    fn facts(src: &str) -> FileFacts<'static> {
        let parsed = php_parser::parse(src);
        assert!(!parsed.has_errors(), "parse errors in test source");
        let program_ref: &'static Program = Box::leak(Box::new(parsed.program));
        let interner_ref: &'static Interner = Box::leak(Box::new(parsed.interner));
        FileFacts::new(program_ref, interner_ref)
    }

    #[test]
    fn namespace_scopes_are_preserved_for_regions_calls_and_declarations() {
        let facts = facts(
            r#"<?php
            namespace App;
            function run($o): void { helper(); $o->go(); }
            class User { public function go(): void { helper(); } }
            "#,
        );
        assert_eq!(facts.functions()[0].scope.namespace(), Some("App"));
        assert_eq!(facts.classes()[0].fqn, "App\\User");
        assert!(facts
            .function_calls()
            .iter()
            .any(|c| matches!(c.callee.kind, ExprKind::Name(_))));
        assert!(facts
            .scoped_function_calls()
            .iter()
            .all(|c| c.scope.namespace() == Some("App")));
        assert!(facts
            .scoped_method_calls()
            .iter()
            .all(|c| c.scope.namespace() == Some("App")));
    }

    #[test]
    fn nested_declarations_match_existing_decl_discovery() {
        let facts = facts(
            r#"<?php
            function outer(): void {
                function inner(): void {}
                class InnerClass { public string $name; public function m(): void {} }
            }
            "#,
        );
        assert_eq!(facts.functions().len(), 2);
        assert_eq!(facts.classes().len(), 1);
        assert_eq!(facts.methods().len(), 1);
        assert_eq!(facts.properties().len(), 1);
        assert_eq!(facts.property_elems().len(), 1);
    }

    #[test]
    fn facts_cross_scopes_but_scope_sensitive_walkers_remain_separate() {
        let facts = facts(
            r#"<?php
            function outer(): void {
                $f = fn() => missing();
            }
            "#,
        );
        assert_eq!(facts.function_calls().len(), 1);
        assert_eq!(facts.functions().len(), 1);
    }

    #[test]
    fn fact_nodes_are_borrowed_from_original_ast() {
        let facts = facts("<?php $x = clone $y; isset($x); $z = $x ?? $y;");
        let assign = facts.assignments().first().unwrap();
        assert_eq!(assign.expr.span, assign.target.span.to(assign.rhs.span));
        assert_eq!(facts.clones().len(), 1);
        assert_eq!(facts.issets().len(), 1);
        assert_eq!(facts.coalesces().len(), 1);
    }

    #[test]
    fn expression_fact_views_classify_common_nodes() {
        let facts = facts(
            r#"<?php
            $arr = [1, 2];
            $cc = C::X;
            $idx = $arr[0];
            $bin = 1 + 2;
            $un = -$bin;
            $cast = (int) $un;
            include 'file.php';
            throw new RuntimeException();
            print $idx;
            exit($idx);
            function gen($xs) {
                yield 1 => 2;
                yield from $xs;
            }
            "#,
        );

        assert_eq!(facts.arrays().len(), 1);
        assert_eq!(facts.class_consts().len(), 1);
        assert_eq!(facts.indexes().len(), 1);
        assert!(facts
            .binaries()
            .iter()
            .any(|b| matches!(b.op, php_ast::BinOp::Add)));
        assert!(facts
            .unaries()
            .iter()
            .any(|u| matches!(u.op, php_ast::UnOp::Minus)));
        assert!(facts
            .casts()
            .iter()
            .any(|c| matches!(c.kind, php_ast::CastKind::Int)));
        assert_eq!(facts.prints().len(), 1);
    }

    #[test]
    fn statement_fact_views_classify_control_nodes() {
        let facts = facts(
            r#"<?php
            echo $x;
            foreach ($xs as $k => &$v) { echo $v; }
            try { foo(); } catch (\RuntimeException $e) { echo $e; } finally { echo 'done'; }
            "#,
        );

        assert_eq!(facts.echoes().len(), 4);
        let foreach = facts.foreaches().first().unwrap();
        assert!(foreach.key.is_some());
    }
}
