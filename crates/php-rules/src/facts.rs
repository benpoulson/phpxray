//! Shared per-file facts for rules.
//!
//! This is intentionally a lightweight index over borrowed AST nodes. It gives
//! rule families common whole-file views without repeatedly walking the AST, but
//! it does not replace flow-sensitive per-scope walkers.

use php_ast::{
    Arg, ArrayItem, ArraySyntax, BinOp, CastKind, Catch, ClassDecl, Expr, ExprKind, FunctionDecl,
    IncludeKind, Member, MemberName, MethodDecl, Program, PropElem, PropertyDecl, Stmt, StmtKind,
    UnOp,
};
use php_intern::Interner;
use php_resolve::{for_each_region, Scope};

/// Borrowed facts collected once for an analyzed file.
pub struct FileFacts<'a> {
    regions: Vec<RegionFact<'a>>,
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
    static_property_fetches: Vec<StaticPropertyFetchFact<'a>>,
    class_consts: Vec<ClassConstFact<'a>>,
    indexes: Vec<IndexFact<'a>>,
    binaries: Vec<BinaryFact<'a>>,
    unaries: Vec<UnaryFact<'a>>,
    casts: Vec<CastFact<'a>>,
    includes: Vec<IncludeFact<'a>>,
    throws: Vec<ThrowFact<'a>>,
    yields: Vec<YieldFact<'a>>,
    yield_froms: Vec<YieldFromFact<'a>>,
    exits: Vec<ExitFact<'a>>,
    prints: Vec<PrintFact<'a>>,
    arrays: Vec<ArrayFact<'a>>,
    assignments: Vec<AssignmentFact<'a>>,
    news: Vec<NewFact<'a>>,
    clones: Vec<CloneFact<'a>>,
    echoes: Vec<EchoFact<'a>>,
    returns: Vec<ReturnFact<'a>>,
    foreaches: Vec<ForeachFact<'a>>,
    tries: Vec<TryFact<'a>>,
    catches: Vec<CatchFact<'a>>,
    issets: Vec<IssetFact<'a>>,
    empties: Vec<EmptyFact<'a>>,
    coalesces: Vec<CoalesceFact<'a>>,
}

#[allow(dead_code)]
pub(crate) struct RegionFact<'a> {
    pub(crate) scope: Scope,
    pub(crate) statements: Vec<&'a Stmt>,
}

#[allow(dead_code)]
pub(crate) struct FunctionDeclFact<'a> {
    pub(crate) scope: Scope,
    pub(crate) decl: &'a FunctionDecl,
}

#[allow(dead_code)]
pub(crate) struct ClassDeclFact<'a> {
    pub(crate) scope: Scope,
    pub(crate) fqn: String,
    pub(crate) decl: &'a ClassDecl,
}

#[allow(dead_code)]
pub(crate) struct MethodDeclFact<'a> {
    pub(crate) scope: Scope,
    pub(crate) class_fqn: String,
    pub(crate) class: &'a ClassDecl,
    pub(crate) decl: &'a MethodDecl,
}

#[allow(dead_code)]
pub(crate) struct PropertyDeclFact<'a> {
    pub(crate) class_fqn: String,
    pub(crate) class: &'a ClassDecl,
    pub(crate) decl: &'a PropertyDecl,
}

#[allow(dead_code)]
pub(crate) struct PropertyElemFact<'a> {
    pub(crate) class_fqn: String,
    pub(crate) class: &'a ClassDecl,
    pub(crate) property: &'a PropertyDecl,
    pub(crate) elem: &'a PropElem,
}

#[allow(dead_code)]
pub(crate) struct CallFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) callee: &'a Expr,
    pub(crate) args: &'a [Arg],
}

#[allow(dead_code)]
pub(crate) struct MethodCallFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) recv: &'a Expr,
    pub(crate) method: &'a MemberName,
    pub(crate) args: &'a [Arg],
    pub(crate) nullsafe: bool,
}

#[allow(dead_code)]
pub(crate) struct ScopedCallFact<'a> {
    pub(crate) scope: Scope,
    pub(crate) expr: &'a Expr,
    pub(crate) callee: &'a Expr,
    pub(crate) args: &'a [Arg],
}

#[allow(dead_code)]
pub(crate) struct ScopedMethodCallFact<'a> {
    pub(crate) scope: Scope,
    pub(crate) expr: &'a Expr,
    pub(crate) recv: &'a Expr,
    pub(crate) method: &'a MemberName,
    pub(crate) args: &'a [Arg],
    pub(crate) nullsafe: bool,
}

#[allow(dead_code)]
pub(crate) struct StaticCallFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) class: &'a Expr,
    pub(crate) method: &'a MemberName,
    pub(crate) args: &'a [Arg],
}

#[allow(dead_code)]
pub(crate) struct PropertyFetchFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) base: &'a Expr,
    pub(crate) name: &'a MemberName,
    pub(crate) nullsafe: bool,
}

#[allow(dead_code)]
pub(crate) struct StaticPropertyFetchFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) class: &'a Expr,
    pub(crate) name: &'a MemberName,
}

#[allow(dead_code)]
pub(crate) struct ClassConstFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) class: &'a Expr,
    pub(crate) name: &'a MemberName,
}

#[allow(dead_code)]
pub(crate) struct IndexFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) base: &'a Expr,
    pub(crate) index: Option<&'a Expr>,
}

#[allow(dead_code)]
pub(crate) struct BinaryFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) op: BinOp,
    pub(crate) lhs: &'a Expr,
    pub(crate) rhs: &'a Expr,
}

#[allow(dead_code)]
pub(crate) struct UnaryFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) op: UnOp,
    pub(crate) inner: &'a Expr,
}

#[allow(dead_code)]
pub(crate) struct CastFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) kind: CastKind,
    pub(crate) inner: &'a Expr,
}

#[allow(dead_code)]
pub(crate) struct IncludeFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) kind: IncludeKind,
    pub(crate) inner: &'a Expr,
}

#[allow(dead_code)]
pub(crate) struct ThrowFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) inner: &'a Expr,
}

#[allow(dead_code)]
pub(crate) struct YieldFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) key: Option<&'a Expr>,
    pub(crate) value: Option<&'a Expr>,
}

#[allow(dead_code)]
pub(crate) struct YieldFromFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) inner: &'a Expr,
}

#[allow(dead_code)]
pub(crate) struct ExitFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) inner: Option<&'a Expr>,
}

#[allow(dead_code)]
pub(crate) struct PrintFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) inner: &'a Expr,
}

#[allow(dead_code)]
pub(crate) struct ArrayFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) items: &'a [ArrayItem],
    pub(crate) syntax: ArraySyntax,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AssignmentKind {
    Plain,
    Op(BinOp),
    Ref,
}

#[allow(dead_code)]
pub(crate) struct AssignmentFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) kind: AssignmentKind,
    pub(crate) target: &'a Expr,
    pub(crate) rhs: &'a Expr,
}

#[allow(dead_code)]
pub(crate) struct NewFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) class: &'a Expr,
    pub(crate) args: &'a [Arg],
}

#[allow(dead_code)]
pub(crate) struct CloneFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) inner: &'a Expr,
}

#[allow(dead_code)]
pub(crate) struct EchoFact<'a> {
    pub(crate) stmt: &'a Stmt,
    pub(crate) exprs: &'a [Expr],
}

#[allow(dead_code)]
pub(crate) struct ReturnFact<'a> {
    pub(crate) stmt: &'a Stmt,
    pub(crate) expr: Option<&'a Expr>,
}

#[allow(dead_code)]
pub(crate) struct ForeachFact<'a> {
    pub(crate) stmt: &'a Stmt,
    pub(crate) subject: &'a Expr,
    pub(crate) key: Option<&'a Expr>,
    pub(crate) value: &'a Expr,
    pub(crate) by_ref: bool,
    pub(crate) key_by_ref: bool,
    pub(crate) body: &'a Stmt,
}

#[allow(dead_code)]
pub(crate) struct TryFact<'a> {
    pub(crate) stmt: &'a Stmt,
    pub(crate) body: &'a [Stmt],
    pub(crate) catches: &'a [Catch],
    pub(crate) finally: Option<&'a [Stmt]>,
}

#[allow(dead_code)]
pub(crate) struct CatchFact<'a> {
    pub(crate) try_stmt: &'a Stmt,
    pub(crate) catch: &'a Catch,
}

#[allow(dead_code)]
pub(crate) struct IssetFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) vars: &'a [Expr],
}

#[allow(dead_code)]
pub(crate) struct EmptyFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) inner: &'a Expr,
}

#[allow(dead_code)]
pub(crate) struct CoalesceFact<'a> {
    pub(crate) expr: &'a Expr,
    pub(crate) lhs: &'a Expr,
    pub(crate) rhs: &'a Expr,
}

#[allow(dead_code)]
impl<'a> FileFacts<'a> {
    pub fn new(program: &'a Program, interner: &'a Interner) -> Self {
        let mut facts = Self {
            regions: Vec::new(),
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
            static_property_fetches: Vec::new(),
            class_consts: Vec::new(),
            indexes: Vec::new(),
            binaries: Vec::new(),
            unaries: Vec::new(),
            casts: Vec::new(),
            includes: Vec::new(),
            throws: Vec::new(),
            yields: Vec::new(),
            yield_froms: Vec::new(),
            exits: Vec::new(),
            prints: Vec::new(),
            arrays: Vec::new(),
            assignments: Vec::new(),
            news: Vec::new(),
            clones: Vec::new(),
            echoes: Vec::new(),
            returns: Vec::new(),
            foreaches: Vec::new(),
            tries: Vec::new(),
            catches: Vec::new(),
            issets: Vec::new(),
            empties: Vec::new(),
            coalesces: Vec::new(),
        };

        for_each_region(&program.stmts, interner, |scope, region| {
            facts.regions.push(RegionFact {
                scope: scope.clone(),
                statements: region.iter().collect(),
            });
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

    pub(crate) fn regions(&self) -> &[RegionFact<'a>] {
        &self.regions
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

    pub(crate) fn static_property_fetches(&self) -> &[StaticPropertyFetchFact<'a>] {
        &self.static_property_fetches
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

    pub(crate) fn includes(&self) -> &[IncludeFact<'a>] {
        &self.includes
    }

    pub(crate) fn throws(&self) -> &[ThrowFact<'a>] {
        &self.throws
    }

    pub(crate) fn yields(&self) -> &[YieldFact<'a>] {
        &self.yields
    }

    pub(crate) fn yield_froms(&self) -> &[YieldFromFact<'a>] {
        &self.yield_froms
    }

    pub(crate) fn exits(&self) -> &[ExitFact<'a>] {
        &self.exits
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

    pub(crate) fn returns(&self) -> &[ReturnFact<'a>] {
        &self.returns
    }

    pub(crate) fn foreaches(&self) -> &[ForeachFact<'a>] {
        &self.foreaches
    }

    pub(crate) fn tries(&self) -> &[TryFact<'a>] {
        &self.tries
    }

    pub(crate) fn catches(&self) -> &[CatchFact<'a>] {
        &self.catches
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
            StmtKind::Echo(exprs) => self.echoes.push(EchoFact { stmt, exprs }),
            StmtKind::Return(expr) => {
                self.returns.push(ReturnFact {
                    stmt,
                    expr: expr.as_ref(),
                });
            }
            StmtKind::Foreach {
                subject,
                key,
                value,
                by_ref,
                key_by_ref,
                body,
            } => self.foreaches.push(ForeachFact {
                stmt,
                subject,
                key: key.as_ref(),
                value,
                by_ref: *by_ref,
                key_by_ref: *key_by_ref,
                body,
            }),
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                self.tries.push(TryFact {
                    stmt,
                    body,
                    catches,
                    finally: finally.as_deref(),
                });
                for catch in catches {
                    self.catches.push(CatchFact {
                        try_stmt: stmt,
                        catch,
                    });
                }
            }
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
            ExprKind::StaticProp { class, name } => {
                self.static_property_fetches
                    .push(StaticPropertyFetchFact { expr, class, name });
            }
            ExprKind::ClassConst { class, name } => {
                self.class_consts.push(ClassConstFact { expr, class, name });
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
            ExprKind::Include { kind, expr: inner } => {
                self.includes.push(IncludeFact {
                    expr,
                    kind: *kind,
                    inner,
                });
            }
            ExprKind::Throw(inner) => {
                self.throws.push(ThrowFact { expr, inner });
            }
            ExprKind::Yield { key, value } => {
                self.yields.push(YieldFact {
                    expr,
                    key: key.as_deref(),
                    value: value.as_deref(),
                });
            }
            ExprKind::YieldFrom(inner) => {
                self.yield_froms.push(YieldFromFact { expr, inner });
            }
            ExprKind::Exit(inner) => {
                self.exits.push(ExitFact {
                    expr,
                    inner: inner.as_deref(),
                });
            }
            ExprKind::Print(inner) => {
                self.prints.push(PrintFact { expr, inner });
            }
            ExprKind::Array { items, syntax } => {
                self.arrays.push(ArrayFact {
                    expr,
                    items,
                    syntax: *syntax,
                });
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
            ExprKind::New { class, args } => {
                self.news.push(NewFact { expr, class, args });
            }
            ExprKind::Clone(inner) => {
                self.clones.push(CloneFact { expr, inner });
            }
            ExprKind::Isset(vars) => {
                self.issets.push(IssetFact { expr, vars });
            }
            ExprKind::Empty(inner) => {
                self.empties.push(EmptyFact { expr, inner });
            }
            ExprKind::Coalesce { lhs, rhs } => {
                self.coalesces.push(CoalesceFact { expr, lhs, rhs });
            }
            _ => {}
        }
    }

    fn collect_scoped_expr(&mut self, scope: &Scope, expr: &'a Expr) {
        match &expr.kind {
            ExprKind::Call { callee, args } => {
                self.scoped_function_calls.push(ScopedCallFact {
                    scope: scope.clone(),
                    expr,
                    callee,
                    args,
                });
            }
            ExprKind::MethodCall {
                recv,
                method,
                args,
                nullsafe,
            } => {
                self.scoped_method_calls.push(ScopedMethodCallFact {
                    scope: scope.clone(),
                    expr,
                    recv,
                    method,
                    args,
                    nullsafe: *nullsafe,
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
        assert_eq!(facts.regions()[0].scope.namespace(), Some("App"));
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
        assert!(facts
            .includes()
            .iter()
            .any(|i| matches!(i.kind, php_ast::IncludeKind::Include)));
        assert_eq!(facts.throws().len(), 1);
        assert_eq!(facts.prints().len(), 1);
        assert_eq!(facts.exits().len(), 1);
        assert_eq!(facts.yields().len(), 1);
        assert_eq!(facts.yield_froms().len(), 1);
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
        assert!(foreach.by_ref);
        assert!(!foreach.key_by_ref);
        assert_eq!(facts.tries().len(), 1);
        assert_eq!(facts.catches().len(), 1);
        assert_eq!(facts.tries()[0].catches.len(), 1);
        assert!(facts.tries()[0].finally.is_some());
    }
}
