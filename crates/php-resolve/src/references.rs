//! M-R2: resolve every **name reference** in a file to what it points to.
//!
//! Walks the whole program (reusing the namespace-region machinery from
//! [`crate::index`]) and, at each name occurrence, records its [`Resolution`]
//! keyed by the name's span. A name's *role* is determined by its syntactic
//! position: the callee of a call is a function, the class of `new`/`::`/
//! `instanceof`/a type hint/`catch`/an attribute is a class, and a bare name in
//! expression position is a constant. Built-in type names (`int`, …) and the
//! language constants `true`/`false`/`null` are not user references and are
//! skipped.

use crate::index::for_each_region;
use crate::{Resolution, Scope};
use php_ast::*;
use php_intern::Interner;
use php_span::Span;

/// What a referenced name denotes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefKind {
    Class,
    Function,
    Const,
}

/// A single resolved name reference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedRef {
    /// The span of the name occurrence.
    pub span: Span,
    pub kind: RefKind,
    pub resolution: Resolution,
    /// The name exactly as written (e.g. `Str`, `Support\Arr`, `\Foo\bar`).
    pub name: String,
    pub fq: NameFq,
}

/// Resolve every name reference in a parsed file, in source order.
pub fn resolve_references(program: &Program, interner: &Interner) -> Vec<ResolvedRef> {
    let mut refs = Vec::new();
    for_each_region(&program.stmts, interner, |scope, region| {
        refs.extend(collect_region(scope, region));
    });
    refs.sort_by_key(|r| r.span.start);
    refs
}

/// Collect the references in one namespace region (its statements share `scope`).
pub(crate) fn collect_region(scope: &Scope, stmts: &[Stmt]) -> Vec<ResolvedRef> {
    let mut c = Collector { refs: Vec::new() };
    for st in stmts {
        c.stmt(scope, st);
    }
    c.refs
}

struct Collector {
    refs: Vec<ResolvedRef>,
}

impl Collector {
    // --- reference recording --------------------------------------------

    fn push(&mut self, name: &Name, kind: RefKind, resolution: Resolution) {
        self.refs.push(ResolvedRef {
            span: name.span,
            kind,
            resolution,
            name: name.text.clone(),
            fq: name.fq,
        });
    }

    fn class_ref(&mut self, scope: &Scope, name: &Name) {
        let resolution = scope.resolve_class(name);
        // Built-in scalar/compound types are not user symbols.
        if !matches!(resolution, Resolution::BuiltinType(_)) {
            self.push(name, RefKind::Class, resolution);
        }
    }

    fn function_ref(&mut self, scope: &Scope, name: &Name) {
        let resolution = scope.resolve_function(name);
        self.push(name, RefKind::Function, resolution);
    }

    fn const_ref(&mut self, scope: &Scope, name: &Name) {
        // `true`/`false`/`null` and the magic `__X__` constants resolve specially
        // and are never namespaced — not user constant references.
        if name.fq == NameFq::NotFq && is_reserved_const(&name.text) {
            return;
        }
        let resolution = scope.resolve_const(name);
        self.push(name, RefKind::Const, resolution);
    }

    /// A class position that may hold a name (`new X`) or an expression
    /// (`new $cls`, `new (expr)`).
    fn class_or_expr(&mut self, scope: &Scope, e: &Expr) {
        match &e.kind {
            ExprKind::Name(n) => self.class_ref(scope, n),
            _ => self.expr(scope, e),
        }
    }

    // --- types ----------------------------------------------------------

    fn ty(&mut self, scope: &Scope, t: &Type) {
        match &t.kind {
            TypeKind::Simple(n) => self.class_ref(scope, n),
            TypeKind::Nullable(inner) => self.ty(scope, inner),
            TypeKind::Union(parts) | TypeKind::Intersection(parts) => {
                parts.iter().for_each(|p| self.ty(scope, p));
            }
        }
    }

    fn opt_ty(&mut self, scope: &Scope, t: &Option<Type>) {
        if let Some(t) = t {
            self.ty(scope, t);
        }
    }

    // --- attributes -----------------------------------------------------

    fn attrs(&mut self, scope: &Scope, groups: &[AttributeGroup]) {
        for g in groups {
            for a in &g.attrs {
                self.class_ref(scope, &a.name);
                if let Some(args) = &a.args {
                    self.args(scope, args);
                }
            }
        }
    }

    // --- expressions ----------------------------------------------------

    fn opt_expr(&mut self, scope: &Scope, e: &Option<Box<Expr>>) {
        if let Some(e) = e {
            self.expr(scope, e);
        }
    }

    fn args(&mut self, scope: &Scope, args: &[Arg]) {
        for a in args {
            self.expr(scope, &a.value);
        }
    }

    fn expr(&mut self, scope: &Scope, e: &Expr) {
        match &e.kind {
            // Leaves.
            ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Str(_)
            | ExprKind::Variable(_)
            | ExprKind::CallablePlaceholder
            | ExprKind::Error => {}

            // A bare name in expression position is a constant fetch.
            ExprKind::Name(n) => self.const_ref(scope, n),

            ExprKind::VariableVariable(inner)
            | ExprKind::DollarBrace(inner)
            | ExprKind::Unary { expr: inner, .. }
            | ExprKind::Cast { expr: inner, .. }
            | ExprKind::Clone(inner)
            | ExprKind::Print(inner)
            | ExprKind::Throw(inner)
            | ExprKind::ErrorSuppress(inner)
            | ExprKind::Empty(inner)
            | ExprKind::PreInc(inner)
            | ExprKind::PreDec(inner)
            | ExprKind::PostInc(inner)
            | ExprKind::PostDec(inner)
            | ExprKind::YieldFrom(inner)
            | ExprKind::Eval(inner)
            | ExprKind::Include { expr: inner, .. }
            | ExprKind::Paren(inner) => self.expr(scope, inner),

            ExprKind::Interpolated(parts) | ExprKind::ShellExec(parts) => {
                parts.iter().for_each(|p| self.expr(scope, p));
            }
            ExprKind::Isset(parts) => parts.iter().for_each(|p| self.expr(scope, p)),

            ExprKind::Array { items, .. } => {
                for it in items {
                    if let Some(k) = &it.key {
                        self.expr(scope, k);
                    }
                    if let Some(v) = &it.value {
                        self.expr(scope, v);
                    }
                }
            }

            // A constant-string callee resolves to a function name, but only the
            // parser's `Name` callees are real function references here.
            ExprKind::Call { callee, args } => {
                match &callee.kind {
                    ExprKind::Name(n) => self.function_ref(scope, n),
                    _ => self.expr(scope, callee),
                }
                self.args(scope, args);
            }
            ExprKind::MethodCall { recv, args, .. } => {
                self.expr(scope, recv);
                self.args(scope, args);
            }
            ExprKind::StaticCall { class, args, .. } => {
                self.class_or_expr(scope, class);
                self.args(scope, args);
            }
            ExprKind::New { class, args } => {
                self.class_or_expr(scope, class);
                self.args(scope, args);
            }
            ExprKind::NewAnon { class, args } => {
                self.class_decl(scope, class);
                self.args(scope, args);
            }
            ExprKind::Index { base, index } => {
                self.expr(scope, base);
                if let Some(i) = index {
                    self.expr(scope, i);
                }
            }
            ExprKind::Prop { base, .. } => self.expr(scope, base),
            ExprKind::StaticProp { class, .. } | ExprKind::ClassConst { class, .. } => {
                self.class_or_expr(scope, class);
            }
            ExprKind::Instanceof { expr, class } => {
                self.expr(scope, expr);
                self.class_or_expr(scope, class);
            }

            ExprKind::Binary { lhs, rhs, .. }
            | ExprKind::Assign { target: lhs, rhs }
            | ExprKind::AssignOp {
                target: lhs, rhs, ..
            }
            | ExprKind::AssignRef { target: lhs, rhs }
            | ExprKind::Coalesce { lhs, rhs } => {
                self.expr(scope, lhs);
                self.expr(scope, rhs);
            }

            ExprKind::Ternary { cond, then, els } => {
                self.expr(scope, cond);
                if let Some(t) = then {
                    self.expr(scope, t);
                }
                self.expr(scope, els);
            }
            ExprKind::Yield { key, value } => {
                self.opt_expr(scope, key);
                self.opt_expr(scope, value);
            }
            ExprKind::Exit(arg) => self.opt_expr(scope, arg),

            ExprKind::Match { subject, arms } => {
                self.expr(scope, subject);
                for arm in arms {
                    if let Some(conds) = &arm.conds {
                        conds.iter().for_each(|c| self.expr(scope, c));
                    }
                    self.expr(scope, &arm.body);
                }
            }

            ExprKind::Closure(c) => {
                self.attrs(scope, &c.attrs);
                self.params(scope, &c.params);
                self.opt_ty(scope, &c.return_type);
                self.stmts(scope, &c.body);
            }
            ExprKind::ArrowFn(a) => {
                self.attrs(scope, &a.attrs);
                self.params(scope, &a.params);
                self.opt_ty(scope, &a.return_type);
                self.expr(scope, &a.body);
            }
        }
    }

    // --- declarations ---------------------------------------------------

    fn params(&mut self, scope: &Scope, params: &[Param]) {
        for p in params {
            self.attrs(scope, &p.attrs);
            self.opt_ty(scope, &p.ty);
            if let Some(d) = &p.default {
                self.expr(scope, d);
            }
            for h in &p.hooks {
                self.hook(scope, h);
            }
        }
    }

    fn hook(&mut self, scope: &Scope, h: &PropertyHook) {
        self.attrs(scope, &h.attrs);
        if let Some(ps) = &h.params {
            self.params(scope, ps);
        }
        match &h.body {
            HookBody::Abstract => {}
            HookBody::Block(b) => self.stmts(scope, b),
            HookBody::Short(e) => self.expr(scope, e),
        }
    }

    fn class_decl(&mut self, scope: &Scope, c: &ClassDecl) {
        self.attrs(scope, &c.attrs);
        c.extends.iter().for_each(|n| self.class_ref(scope, n));
        c.implements.iter().for_each(|n| self.class_ref(scope, n));
        self.opt_ty(scope, &c.backing);
        for m in &c.members {
            match m {
                Member::Method(meth) => {
                    self.attrs(scope, &meth.attrs);
                    self.params(scope, &meth.params);
                    self.opt_ty(scope, &meth.return_type);
                    if let Some(body) = &meth.body {
                        self.stmts(scope, body);
                    }
                }
                Member::Property(p) => {
                    self.attrs(scope, &p.attrs);
                    self.opt_ty(scope, &p.ty);
                    for el in &p.props {
                        if let Some(d) = &el.default {
                            self.expr(scope, d);
                        }
                        if let Some(hooks) = &el.hooks {
                            hooks.iter().for_each(|h| self.hook(scope, h));
                        }
                    }
                }
                Member::ClassConst(cc) => {
                    self.attrs(scope, &cc.attrs);
                    self.opt_ty(scope, &cc.ty);
                    cc.consts.iter().for_each(|el| self.expr(scope, &el.value));
                }
                Member::EnumCase(case) => {
                    self.attrs(scope, &case.attrs);
                    if let Some(v) = &case.value {
                        self.expr(scope, v);
                    }
                }
                Member::TraitUse(tu) => tu.traits.iter().for_each(|n| self.class_ref(scope, n)),
            }
        }
    }

    // --- statements -----------------------------------------------------

    fn stmts(&mut self, scope: &Scope, stmts: &[Stmt]) {
        for st in stmts {
            self.stmt(scope, st);
        }
    }

    fn stmt(&mut self, scope: &Scope, st: &Stmt) {
        match &st.kind {
            StmtKind::Expr(e) => self.expr(scope, e),
            StmtKind::Echo(es) => es.iter().for_each(|e| self.expr(scope, e)),
            StmtKind::Return(e) | StmtKind::Break(e) | StmtKind::Continue(e) => {
                if let Some(e) = e {
                    self.expr(scope, e);
                }
            }
            StmtKind::Block(b) => self.stmts(scope, b),
            StmtKind::If {
                cond,
                then,
                elseifs,
                els,
            } => {
                self.expr(scope, cond);
                self.stmt(scope, then);
                for e in elseifs {
                    self.expr(scope, &e.cond);
                    self.stmt(scope, &e.body);
                }
                if let Some(e) = els {
                    self.stmt(scope, e);
                }
            }
            StmtKind::While { cond, body } | StmtKind::DoWhile { body, cond } => {
                self.expr(scope, cond);
                self.stmt(scope, body);
            }
            StmtKind::For {
                init,
                cond,
                update,
                body,
            } => {
                for v in init.iter().chain(cond).chain(update) {
                    self.expr(scope, v);
                }
                self.stmt(scope, body);
            }
            StmtKind::Foreach {
                subject,
                key,
                value,
                body,
                ..
            } => {
                self.expr(scope, subject);
                if let Some(k) = key {
                    self.expr(scope, k);
                }
                self.expr(scope, value);
                self.stmt(scope, body);
            }
            StmtKind::Switch { subject, cases } => {
                self.expr(scope, subject);
                for case in cases {
                    if let Some(t) = &case.test {
                        self.expr(scope, t);
                    }
                    self.stmts(scope, &case.body);
                }
            }
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                self.stmts(scope, body);
                for c in catches {
                    // `catch (A | B $e)` — the caught types are class references.
                    c.types.iter().for_each(|n| self.class_ref(scope, n));
                    self.stmts(scope, &c.body);
                }
                if let Some(f) = finally {
                    self.stmts(scope, f);
                }
            }
            StmtKind::Global(es) | StmtKind::Unset(es) => {
                es.iter().for_each(|e| self.expr(scope, e))
            }
            StmtKind::StaticVars(vs) => {
                for v in vs {
                    if let Some(d) = &v.default {
                        self.expr(scope, d);
                    }
                }
            }
            StmtKind::Declare { directives, body } => {
                directives.iter().for_each(|(_, e)| self.expr(scope, e));
                if let Some(b) = body {
                    self.stmt(scope, b);
                }
            }
            StmtKind::Function(f) => {
                self.attrs(scope, &f.attrs);
                self.params(scope, &f.params);
                self.opt_ty(scope, &f.return_type);
                self.stmts(scope, &f.body);
            }
            StmtKind::Class(c) => self.class_decl(scope, c),
            StmtKind::ConstDecl { consts, attrs } => {
                self.attrs(scope, attrs);
                consts.iter().for_each(|el| self.expr(scope, &el.value));
            }
            // Namespace blocks are handled by region splitting; imports, labels,
            // goto, halt, inline HTML and nops carry no resolvable references.
            _ => {}
        }
    }
}

/// `true`/`false`/`null` and the magic `__LINE__`-style constants are language
/// constants, never namespaced.
fn is_reserved_const(text: &str) -> bool {
    matches!(
        text.to_ascii_lowercase().as_str(),
        "true" | "false" | "null"
    ) || (text.starts_with("__") && text.ends_with("__"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn refs(src: &str) -> Vec<(RefKind, String)> {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors in test source");
        resolve_references(&r.program, &r.interner)
            .into_iter()
            .map(|rf| {
                (
                    rf.kind,
                    rf.resolution.fqn().unwrap_or("<late/builtin>").to_string(),
                )
            })
            .collect()
    }

    #[test]
    fn new_extends_and_type_hints_are_class_refs() {
        let got = refs(
            r#"<?php
            namespace App;
            use App\Support\Base;
            class User extends Base {
                public function make(Helper $h): Result { return new Widget(); }
            }
            "#,
        );
        assert!(got.contains(&(RefKind::Class, "App\\Support\\Base".into())));
        assert!(got.contains(&(RefKind::Class, "App\\Helper".into())));
        assert!(got.contains(&(RefKind::Class, "App\\Result".into())));
        assert!(got.contains(&(RefKind::Class, "App\\Widget".into())));
    }

    #[test]
    fn function_calls_get_global_fallback() {
        let got = refs(r#"<?php namespace App; strlen("x");"#);
        assert_eq!(got, [(RefKind::Function, "App\\strlen".into())]);
    }

    #[test]
    fn fully_qualified_call_is_definite() {
        let got = refs(r#"<?php namespace App; \strlen("x"); \Other\go();"#);
        assert_eq!(
            got,
            [
                (RefKind::Function, "strlen".into()),
                (RefKind::Function, "Other\\go".into())
            ]
        );
    }

    #[test]
    fn static_and_instanceof_are_class_refs() {
        let got = refs(
            r#"<?php
            namespace App;
            use Other\Service;
            Service::make();
            $x instanceof Service;
            Service::CONST;
            "#,
        );
        let classes: Vec<_> = got.iter().filter(|(k, _)| *k == RefKind::Class).collect();
        assert_eq!(classes.len(), 3);
        assert!(classes.iter().all(|(_, f)| f == "Other\\Service"));
    }

    #[test]
    fn catch_types_are_class_refs() {
        let got = refs(r#"<?php namespace App; try {} catch (\RuntimeException | Bad $e) {}"#);
        assert!(got.contains(&(RefKind::Class, "RuntimeException".into())));
        assert!(got.contains(&(RefKind::Class, "App\\Bad".into())));
    }

    #[test]
    fn bare_name_is_a_const_ref_but_reserved_are_skipped() {
        let got =
            refs(r#"<?php namespace App; echo MY_CONST; echo true; echo null; echo __LINE__;"#);
        assert_eq!(got, [(RefKind::Const, "App\\MY_CONST".into())]);
    }

    #[test]
    fn builtin_type_hints_are_not_references() {
        let got = refs(r#"<?php namespace App; function f(int $a, string $b): bool {}"#);
        assert!(got.is_empty());
    }

    #[test]
    fn attribute_names_are_class_refs() {
        let got = refs(
            r#"<?php
            namespace App;
            use App\Attr\Route;
            #[Route("/x")] class C {}
            "#,
        );
        assert_eq!(got, [(RefKind::Class, "App\\Attr\\Route".into())]);
    }

    #[test]
    fn references_inside_nested_bodies_and_closures() {
        let got = refs(
            r#"<?php
            namespace App;
            function outer() {
                $f = function (): Widget { return new Gadget(); };
                if (true) { new Deep(); }
            }
            "#,
        );
        assert!(got.contains(&(RefKind::Class, "App\\Widget".into())));
        assert!(got.contains(&(RefKind::Class, "App\\Gadget".into())));
        assert!(got.contains(&(RefKind::Class, "App\\Deep".into())));
    }

    #[test]
    fn self_parent_static_resolve_as_late_static() {
        let got: Vec<_> = {
            let r = php_parser::parse(
                r#"<?php namespace App; class C extends B { function m() { return new static(); } }"#,
            );
            resolve_references(&r.program, &r.interner)
                .into_iter()
                .map(|rf| (rf.kind, rf.resolution))
                .collect()
        };
        assert!(got.iter().any(|(k, r)| *k == RefKind::Class
            && matches!(r, Resolution::LateStatic(s) if s == "static")));
    }
}
