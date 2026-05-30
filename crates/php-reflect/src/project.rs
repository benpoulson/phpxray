//! M-T3: the **project reflection index** + inherited-member lookup.
//!
//! [`ReflectionIndex`] aggregates the [`ClassReflection`]s / [`FunctionReflection`]s
//! of many files into one queryable map (the reflection counterpart of
//! `php_index::ProjectIndex`, which only holds names). On top of it sit the
//! member-resolution queries the type system needs: looking up a method,
//! property, or constant *through* a class's hierarchy
//! (extends → implemented interfaces → used traits → `@mixin`), substituting
//! generic type arguments from each parent's `@extends`/`@implements`/`@use`
//! type args as the walk ascends.

use crate::{
    reflect_class, reflect_function, ClassReflection, ConstReflection, FunctionReflection,
    MethodReflection, PropertyReflection,
};
use php_ast::{ClassDecl, ClassKind, Member, Program, Stmt, StmtKind};
use php_intern::Interner;
use php_resolve::{for_each_region, Scope, SymbolKey, SymbolOrigin};
use php_types::{PhpVersion, Type};
use std::collections::HashMap;

/// A map from `@template` names to the types bound for them along a hierarchy walk.
type Subst = HashMap<String, Type>;

/// How a parsed file participates in reflection.
pub type SourceKind = SymbolOrigin;

/// A member found via hierarchy lookup, plus the class that declared it. Member
/// types have generic template variables substituted for the query's bindings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Found<T> {
    pub member: T,
    /// FQN of the class/interface/trait the member was declared on.
    pub declaring_class: String,
}

/// Stored AST body metadata for a reflected function or method.
#[derive(Debug, Clone)]
struct BodyRecord {
    body: Vec<Stmt>,
    scope: Scope,
    path: Option<String>,
    source_kind: SourceKind,
}

/// A borrowed function/method body plus the source metadata needed by callers
/// that emit diagnostics against that body.
#[derive(Debug, Clone, Copy)]
pub struct BodyMetadata<'a> {
    pub body: &'a [Stmt],
    pub scope: &'a Scope,
    pub path: Option<&'a str>,
    pub source_kind: SourceKind,
}

impl BodyRecord {
    fn metadata(&self) -> BodyMetadata<'_> {
        BodyMetadata {
            body: self.body.as_slice(),
            scope: &self.scope,
            path: self.path.as_deref(),
            source_kind: self.source_kind,
        }
    }
}

/// A reflected function plus the AST declaration it came from.
#[derive(Debug)]
pub struct ReflectedFunction<'a> {
    pub decl: &'a php_ast::FunctionDecl,
    pub reflection: FunctionReflection,
}

/// A reflected class-like declaration plus the AST declaration it came from.
#[derive(Debug)]
pub struct ReflectedClass<'a> {
    pub decl: &'a ClassDecl,
    pub reflection: ClassReflection,
}

/// The reflected declarations discovered in one parsed source unit.
#[derive(Debug, Default)]
pub struct ReflectedFile<'a> {
    pub classes: Vec<ReflectedClass<'a>>,
    pub functions: Vec<ReflectedFunction<'a>>,
}

/// Reflect every named class-like and function declaration in a parsed file.
pub fn reflect_file<'a>(program: &'a Program, interner: &Interner) -> ReflectedFile<'a> {
    let mut out = ReflectedFile::default();
    for_each_region(&program.stmts, interner, |scope, region| {
        for st in region {
            visit_reflectable_decls(scope, st, &mut |scope, decl| match decl {
                ReflectableDecl::Function(f) => {
                    out.functions.push(ReflectedFunction {
                        decl: f,
                        reflection: reflect_function(scope, interner, f),
                    });
                }
                ReflectableDecl::Class(c) => {
                    let Some(name) = c.name else { return };
                    let fqn = scope.qualify(interner.resolve(name));
                    out.classes.push(ReflectedClass {
                        decl: c,
                        reflection: reflect_class(scope, interner, &fqn, c),
                    });
                }
            });
        }
    });
    out
}

enum ReflectableDecl<'a> {
    Function(&'a php_ast::FunctionDecl),
    Class(&'a ClassDecl),
}

fn visit_reflectable_decls<'a>(
    scope: &Scope,
    st: &'a php_ast::Stmt,
    f: &mut impl FnMut(&Scope, ReflectableDecl<'a>),
) {
    match &st.kind {
        StmtKind::Function(func) => {
            f(scope, ReflectableDecl::Function(func));
            for st in &func.body {
                visit_reflectable_decls(scope, st, f);
            }
        }
        StmtKind::Class(class) => {
            f(scope, ReflectableDecl::Class(class));
            for member in &class.members {
                if let Member::Method(method) = member {
                    if let Some(body) = &method.body {
                        for st in body {
                            visit_reflectable_decls(scope, st, f);
                        }
                    }
                }
            }
        }
        StmtKind::Block(body) => {
            for st in body {
                visit_reflectable_decls(scope, st, f);
            }
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            visit_reflectable_decls(scope, then, f);
            for elseif in elseifs {
                visit_reflectable_decls(scope, &elseif.body, f);
            }
            if let Some(els) = els {
                visit_reflectable_decls(scope, els, f);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => visit_reflectable_decls(scope, body, f),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for st in body {
                visit_reflectable_decls(scope, st, f);
            }
            for catch in catches {
                for st in &catch.body {
                    visit_reflectable_decls(scope, st, f);
                }
            }
            if let Some(finally) = finally {
                for st in finally {
                    visit_reflectable_decls(scope, st, f);
                }
            }
        }
        StmtKind::Switch { cases, .. } => {
            for case in cases {
                for st in &case.body {
                    visit_reflectable_decls(scope, st, f);
                }
            }
        }
        StmtKind::Declare {
            body: Some(body), ..
        } => {
            visit_reflectable_decls(scope, body, f);
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

/// All reflected classes/functions across a set of files, keyed for lookup.
#[derive(Debug, Default)]
pub struct ReflectionIndex {
    /// Lowercased FQN → class reflection (class names are case-insensitive).
    classes: HashMap<String, ClassReflection>,
    /// Lowercased FQN → function reflection.
    functions: HashMap<String, FunctionReflection>,
    /// Callable bodies + their declaring [`Scope`] for interprocedural per-call
    /// return inference and context diagnostics. Keyed by `key(fqn)` for free
    /// functions and `key(declaring_class)::name_lower` for methods. The scope is
    /// kept so the body's name references resolve in *their* namespace, not the
    /// caller's; this is sound only because all files share one interner (symbols
    /// are global).
    bodies: HashMap<String, BodyRecord>,
}

impl ReflectionIndex {
    pub fn new() -> Self {
        Self::default()
    }

    /// A fresh index pre-loaded with the typed built-in **function** signatures
    /// (Cap #4). Project files added afterward (`add_file`) override a builtin of
    /// the same FQN. This is what makes `argument.type` / return inference work
    /// on `strlen`, `array_map`, … without any per-rule special-casing.
    pub fn with_builtins() -> Self {
        Self::with_builtins_for(PhpVersion::default())
    }

    /// A fresh index pre-loaded with typed built-in signatures for `version`.
    pub fn with_builtins_for(version: PhpVersion) -> Self {
        let mut idx = Self::new();
        for fr in crate::builtins::builtin_functions_for(version) {
            idx.functions.insert(function_key(&fr.fqn), fr);
        }
        for cr in crate::builtins::builtin_classes_for(version) {
            idx.classes.insert(class_key(&cr.fqn), cr);
        }
        idx
    }

    /// Reflect every class and function in a parsed file and add them to the
    /// index. Later definitions of the same FQN overwrite earlier ones.
    pub fn add_file(&mut self, program: &Program, interner: &Interner) {
        self.add_file_as(program, interner, SourceKind::Analyzed);
    }

    /// Reflect every class and function in a parsed file, with scan-only files
    /// prevented from replacing curated built-in reflections.
    pub fn add_file_as(&mut self, program: &Program, interner: &Interner, kind: SourceKind) {
        self.add_file_labeled_as(None, program, interner, kind);
    }

    /// Reflect every class and function in a parsed file and retain `path` for
    /// body metadata. The legacy [`add_file_as`](Self::add_file_as) remains for
    /// callers that only need signatures.
    pub fn add_file_labeled_as(
        &mut self,
        path: Option<&str>,
        program: &Program,
        interner: &Interner,
        kind: SourceKind,
    ) {
        for_each_region(&program.stmts, interner, |scope, region| {
            for st in region {
                self.collect_stmt(scope, interner, st, kind, path);
            }
        });
    }

    /// Look up a class by FQN (case-insensitive, leading `\` ignored).
    pub fn class(&self, fqn: &str) -> Option<&ClassReflection> {
        self.classes.get(&class_key(fqn))
    }

    /// Look up a function by FQN (case-insensitive, leading `\` ignored).
    pub fn function(&self, fqn: &str) -> Option<&FunctionReflection> {
        self.functions.get(&function_key(fqn))
    }

    /// Number of indexed classes.
    pub fn class_count(&self) -> usize {
        self.classes.len()
    }

    /// Whether `sub` is `sup` or transitively extends/implements/uses it
    /// (reflexive, case-insensitive). Walks parents, interfaces, and traits;
    /// tolerant of unknown links and cycles. Returns `false` if the relationship
    /// can't be established from the indexed classes — callers that must avoid
    /// false positives should treat an *unknown* class leniently themselves.
    pub fn is_subclass_of(&self, sub: &str, sup: &str) -> bool {
        let mut visited = Vec::new();
        self.is_sub(&class_key(sub), &class_key(sup), &mut visited)
    }

    fn is_sub(&self, sub_key: &str, sup_key: &str, visited: &mut Vec<String>) -> bool {
        if sub_key == sup_key {
            return true; // reflexive
        }
        if visited.iter().any(|v| v == sub_key) {
            return false;
        }
        visited.push(sub_key.to_string());
        let Some(c) = self.classes.get(sub_key) else {
            return false;
        };
        c.parents
            .iter()
            .chain(&c.interfaces)
            .chain(&c.traits)
            .filter_map(|p| match p {
                Type::Named { fqn, .. } => Some(class_key(fqn)),
                _ => None,
            })
            .any(|pk| self.is_sub(&pk, sup_key, visited))
    }

    /// Resolve a method by name through `class_fqn`'s hierarchy (own members
    /// first, then traits, parent class, interfaces, mixins). Method names match
    /// case-insensitively. Returns the method with generic args substituted.
    pub fn find_method(&self, class_fqn: &str, name: &str) -> Option<Found<MethodReflection>> {
        let mut visited = Vec::new();
        self.ascend(
            class_fqn,
            Subst::new(),
            &mut visited,
            &mut |class, subst| {
                class
                    .methods
                    .iter()
                    .find(|m| m.name.eq_ignore_ascii_case(name))
                    .map(|m| Found {
                        member: subst_method(m, subst),
                        declaring_class: class.fqn.clone(),
                    })
            },
        )
    }

    /// Resolve a method through the hierarchy of a concrete receiver type,
    /// substituting the receiver's own generic arguments before walking parents.
    pub fn find_method_on_type(
        &self,
        receiver: &Type,
        name: &str,
    ) -> Option<Found<MethodReflection>> {
        let (fqn, subst) = self.receiver_named_subst(receiver)?;
        let mut visited = Vec::new();
        self.ascend(fqn, subst, &mut visited, &mut |class, subst| {
            class
                .methods
                .iter()
                .find(|m| m.name.eq_ignore_ascii_case(name))
                .map(|m| Found {
                    member: subst_method(m, subst),
                    declaring_class: class.fqn.clone(),
                })
        })
    }

    /// Whether every known concrete descendant of an abstract class/interface is
    /// final and exposes `method`. This is an intentionally narrow escape hatch
    /// for member-existence checks on abstract receiver types: if a library's
    /// hierarchy is closed by final leaf classes, a call may be valid even when
    /// the abstract parent does not declare the method.
    pub fn final_concrete_descendants_have_method(&self, class_fqn: &str, method: &str) -> bool {
        let Some(base) = self.class(class_fqn) else {
            return false;
        };
        if !base.is_abstract && !matches!(base.kind, ClassKind::Interface) {
            return false;
        }

        let base_key = class_key(class_fqn);
        let mut saw_concrete = false;
        for class in self.classes.values() {
            if class_key(&class.fqn) == base_key || !self.is_subclass_of(&class.fqn, class_fqn) {
                continue;
            }
            if !matches!(class.kind, ClassKind::Class | ClassKind::Enum) || class.is_abstract {
                continue;
            }
            saw_concrete = true;
            if !class.is_final || self.find_method(&class.fqn, method).is_none() {
                return false;
            }
        }
        saw_concrete
    }

    /// Resolve a property by name (without `$`) through the hierarchy. Property
    /// names are case-sensitive.
    pub fn find_property(&self, class_fqn: &str, name: &str) -> Option<Found<PropertyReflection>> {
        let mut visited = Vec::new();
        self.ascend(
            class_fqn,
            Subst::new(),
            &mut visited,
            &mut |class, subst| {
                class
                    .properties
                    .iter()
                    .find(|p| p.name == name)
                    .map(|p| Found {
                        member: PropertyReflection {
                            ty: subst_type(&p.ty, subst),
                            ..p.clone()
                        },
                        declaring_class: class.fqn.clone(),
                    })
            },
        )
    }

    /// Resolve a property through the hierarchy of a concrete receiver type,
    /// substituting the receiver's own generic arguments before walking parents.
    pub fn find_property_on_type(
        &self,
        receiver: &Type,
        name: &str,
    ) -> Option<Found<PropertyReflection>> {
        let (fqn, subst) = self.receiver_named_subst(receiver)?;
        let mut visited = Vec::new();
        self.ascend(fqn, subst, &mut visited, &mut |class, subst| {
            class
                .properties
                .iter()
                .find(|p| p.name == name)
                .map(|p| Found {
                    member: PropertyReflection {
                        ty: subst_type(&p.ty, subst),
                        ..p.clone()
                    },
                    declaring_class: class.fqn.clone(),
                })
        })
    }

    /// Resolve a class constant by name through the hierarchy. Constant names are
    /// case-sensitive.
    pub fn find_constant(&self, class_fqn: &str, name: &str) -> Option<Found<ConstReflection>> {
        let mut visited = Vec::new();
        self.ascend(
            class_fqn,
            Subst::new(),
            &mut visited,
            &mut |class, subst| {
                class
                    .constants
                    .iter()
                    .find(|c| c.name == name)
                    .map(|c| Found {
                        member: ConstReflection {
                            ty: subst_type(&c.ty, subst),
                            ..c.clone()
                        },
                        declaring_class: class.fqn.clone(),
                    })
            },
        )
    }

    /// Walk `fqn` and its ancestors in PHP member-resolution order, calling `f`
    /// with each class and the active template substitution; returns the first
    /// `Some(f(...))`. `visited` (lowercased FQNs) breaks diamonds/cycles.
    fn ascend<T>(
        &self,
        fqn: &str,
        subst: Subst,
        visited: &mut Vec<String>,
        f: &mut impl FnMut(&ClassReflection, &Subst) -> Option<T>,
    ) -> Option<T> {
        let k = class_key(fqn);
        if visited.contains(&k) {
            return None;
        }
        visited.push(k);
        let class = self.classes.get(&class_key(fqn))?;
        if let Some(found) = f(class, &subst) {
            return Some(found);
        }
        // Traits, then the parent class, then interfaces, then mixins.
        let parents = class
            .traits
            .iter()
            .chain(&class.parents)
            .chain(&class.interfaces)
            .chain(&class.mixins);
        for parent in parents {
            if let Type::Named { fqn: pf, args } = parent {
                let psubst = self.compose(pf, args, &subst);
                if let Some(found) = self.ascend(pf, psubst, visited, f) {
                    return Some(found);
                }
            }
        }
        None
    }

    /// Build the substitution for entering parent `pf` applied with `args`: map
    /// the parent's declared `@template` names to `args` (each first rewritten
    /// through the outer substitution so bindings compose down the chain).
    fn compose(&self, pf: &str, args: &[Type], outer: &Subst) -> Subst {
        let mut map = Subst::new();
        if let Some(parent) = self.classes.get(&class_key(pf)) {
            for (name, arg) in parent.templates.iter().zip(args) {
                map.insert(name.clone(), subst_type(arg, outer));
            }
        }
        map
    }

    fn receiver_named_subst<'a>(&self, receiver: &'a Type) -> Option<(&'a str, Subst)> {
        match receiver {
            Type::Named { fqn, args } => Some((fqn.as_str(), self.receiver_subst(fqn, args))),
            Type::Nullable(inner) => self.receiver_named_subst(inner),
            _ => None,
        }
    }

    fn receiver_subst(&self, fqn: &str, args: &[Type]) -> Subst {
        let mut map = Subst::new();
        if let Some(class) = self.classes.get(&class_key(fqn)) {
            for (name, arg) in class.templates.iter().zip(args) {
                map.insert(name.clone(), arg.clone());
            }
        }
        map
    }

    fn collect_stmt(
        &mut self,
        scope: &Scope,
        interner: &Interner,
        st: &php_ast::Stmt,
        kind: SourceKind,
        path: Option<&str>,
    ) {
        visit_reflectable_decls(scope, st, &mut |scope, decl| match decl {
            ReflectableDecl::Class(c) => self.add_class(scope, interner, c, kind, path),
            ReflectableDecl::Function(f) => {
                let r = reflect_function(scope, interner, f);
                if kind == SourceKind::Scan
                    && self
                        .functions
                        .get(&function_key(&r.fqn))
                        .is_some_and(|f| f.builtin)
                {
                    return;
                }
                self.bodies.insert(
                    function_key(&r.fqn),
                    BodyRecord {
                        body: f.body.clone(),
                        scope: scope.clone(),
                        path: path.map(str::to_string),
                        source_kind: kind,
                    },
                );
                self.functions.insert(function_key(&r.fqn), r);
            }
        });
    }

    fn add_class(
        &mut self,
        scope: &Scope,
        interner: &Interner,
        c: &ClassDecl,
        kind: SourceKind,
        path: Option<&str>,
    ) {
        // Anonymous classes have no FQN.
        let Some(name) = c.name else { return };
        let fqn = scope.qualify(interner.resolve(name));
        if kind == SourceKind::Scan
            && self
                .classes
                .get(&class_key(&fqn))
                .is_some_and(|c| c.builtin)
        {
            return;
        }
        let r = reflect_class(scope, interner, &fqn, c);
        // Store method bodies (+ the class's scope) for interprocedural inference.
        for m in &c.members {
            if let Member::Method(md) = m {
                if let Some(body) = &md.body {
                    let mname = interner.resolve(md.name).to_ascii_lowercase();
                    self.bodies.insert(
                        format!("{}::{}", class_key(&fqn), mname),
                        BodyRecord {
                            body: body.clone(),
                            scope: scope.clone(),
                            path: path.map(str::to_string),
                            source_kind: kind,
                        },
                    );
                }
            }
        }
        self.classes.insert(class_key(&fqn), r);
    }

    /// The body + declaring scope of a free function, by FQN (for interprocedural
    /// return inference).
    pub fn function_body(&self, fqn: &str) -> Option<(&[Stmt], &Scope)> {
        self.bodies
            .get(&function_key(fqn))
            .map(|r| (r.body.as_slice(), &r.scope))
    }

    /// Full body metadata for a free function, including source path/kind when
    /// it was added through [`add_file_labeled_as`](Self::add_file_labeled_as).
    pub fn function_body_meta(&self, fqn: &str) -> Option<BodyMetadata<'_>> {
        self.bodies
            .get(&function_key(fqn))
            .map(BodyRecord::metadata)
    }

    /// The body + declaring scope of a method on `declaring_class` (use the
    /// `declaring_class` from [`find_method`](Self::find_method), not the receiver).
    pub fn method_body(&self, declaring_class: &str, name: &str) -> Option<(&[Stmt], &Scope)> {
        self.bodies
            .get(&format!(
                "{}::{}",
                class_key(declaring_class),
                name.to_ascii_lowercase()
            ))
            .map(|r| (r.body.as_slice(), &r.scope))
    }

    /// Full body metadata for a method on `declaring_class`.
    pub fn method_body_meta(&self, declaring_class: &str, name: &str) -> Option<BodyMetadata<'_>> {
        self.bodies
            .get(&format!(
                "{}::{}",
                class_key(declaring_class),
                name.to_ascii_lowercase()
            ))
            .map(BodyRecord::metadata)
    }
}

fn class_key(fqn: &str) -> String {
    SymbolKey::class_like(fqn).into_string()
}

fn function_key(fqn: &str) -> String {
    SymbolKey::function(fqn).into_string()
}

/// Apply a template substitution to a method's parameter and return types.
fn subst_method(m: &MethodReflection, subst: &Subst) -> MethodReflection {
    if subst.is_empty() {
        return m.clone();
    }
    let mut out = m.clone();
    for p in &mut out.params {
        p.ty = subst_type(&p.ty, subst);
        p.native_ty = subst_type(&p.native_ty, subst);
    }
    out.return_type = subst_type(&out.return_type, subst);
    out.native_return = subst_type(&out.native_return, subst);
    out
}

/// Recursively replace [`Type::TemplateVar`] occurrences using `subst`.
fn subst_type(ty: &Type, subst: &Subst) -> Type {
    if subst.is_empty() {
        return ty.clone();
    }
    ty.clone().map(&mut |part| match part {
        Type::TemplateVar(name) => subst.get(&name).cloned().unwrap_or(Type::TemplateVar(name)),
        Type::Union(parts) => Type::union(parts),
        Type::Intersection(parts) => Type::intersection(parts),
        other => other,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_resolve::SymbolKey;
    use std::collections::BTreeSet;

    fn index(src: &str) -> ReflectionIndex {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::new();
        idx.add_file(&r.program, &r.interner);
        idx
    }

    fn named(fqn: &str) -> Type {
        Type::Named {
            fqn: fqn.into(),
            args: vec![],
        }
    }

    fn generic(fqn: &str, args: Vec<Type>) -> Type {
        Type::Named {
            fqn: fqn.into(),
            args,
        }
    }

    #[test]
    fn indexes_classes_and_functions_case_insensitively() {
        let idx = index(
            r#"<?php
            namespace App;
            class User {}
            function helper(): void {}"#,
        );
        assert!(idx.class("App\\User").is_some());
        assert!(idx.class("app\\user").is_some()); // case-insensitive
        assert!(idx.class("\\App\\User").is_some()); // leading backslash ignored
        assert!(idx.function("App\\helper").is_some());
        assert_eq!(idx.class_count(), 1);
    }

    #[test]
    fn body_metadata_preserves_source_path_kind_and_scope() {
        let r = php_parser::parse(
            r#"<?php
            namespace App;
            function cb($x): void { helper($x); }
            class Handler { public function map($x): void { helper($x); } }
            "#,
        );
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::new();
        idx.add_file_labeled_as(
            Some("src/Callbacks.php"),
            &r.program,
            &r.interner,
            SourceKind::Analyzed,
        );

        let old_fn = idx.function_body("App\\cb").unwrap();
        assert_eq!(old_fn.1.namespace(), Some("App"));
        let fn_meta = idx.function_body_meta("App\\cb").unwrap();
        assert_eq!(fn_meta.path, Some("src/Callbacks.php"));
        assert_eq!(fn_meta.source_kind, SourceKind::Analyzed);
        assert_eq!(fn_meta.scope.namespace(), Some("App"));
        assert!(!fn_meta.body.is_empty());

        let old_method = idx.method_body("App\\Handler", "map").unwrap();
        assert_eq!(old_method.1.namespace(), Some("App"));
        let method_meta = idx.method_body_meta("App\\Handler", "map").unwrap();
        assert_eq!(method_meta.path, Some("src/Callbacks.php"));
        assert_eq!(method_meta.source_kind, SourceKind::Analyzed);
        assert_eq!(method_meta.scope.namespace(), Some("App"));
        assert!(!method_meta.body.is_empty());
    }

    #[test]
    fn unlabeled_body_metadata_keeps_old_body_api_but_has_no_path() {
        let r = php_parser::parse("<?php function cb(): void {}");
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::new();
        idx.add_file(&r.program, &r.interner);

        assert!(idx.function_body("cb").is_some());
        let meta = idx.function_body_meta("cb").unwrap();
        assert_eq!(meta.path, None);
        assert_eq!(meta.source_kind, SourceKind::Analyzed);
    }

    #[test]
    fn finds_inherited_method_from_parent() {
        let idx = index(
            r#"<?php
            class Base { public function id(): int { return 1; } }
            class User extends Base {}"#,
        );
        let f = idx.find_method("User", "id").unwrap();
        assert_eq!(f.declaring_class, "Base");
        assert_eq!(f.member.return_type, Type::Int);
        // Own method shadows the inherited one.
        let idx2 = index(
            r#"<?php
            class Base { public function id(): int {} }
            class User extends Base { public function id(): string {} }"#,
        );
        let f2 = idx2.find_method("User", "id").unwrap();
        assert_eq!(f2.declaring_class, "User");
        assert_eq!(f2.member.return_type, Type::String);
    }

    #[test]
    fn method_lookup_is_case_insensitive() {
        let idx = index(r#"<?php class C { public function doThing(): void {} }"#);
        assert!(idx.find_method("C", "DOTHING").is_some());
        assert!(idx.find_method("C", "dothing").is_some());
    }

    #[test]
    fn finds_method_through_trait_and_interface_const() {
        let idx = index(
            r#"<?php
            trait T { public function shared(): bool {} }
            interface I { const MAX = 10; }
            class C extends \stdClass implements I { use T; }"#,
        );
        assert_eq!(idx.find_method("C", "shared").unwrap().declaring_class, "T");
        assert_eq!(idx.find_constant("C", "MAX").unwrap().declaring_class, "I");
    }

    #[test]
    fn inherited_property_is_found() {
        let idx = index(
            r#"<?php
            class Base { protected string $name; }
            class User extends Base {}"#,
        );
        let p = idx.find_property("User", "name").unwrap();
        assert_eq!(p.declaring_class, "Base");
        assert_eq!(p.member.ty, Type::String);
        assert!(idx.find_property("User", "missing").is_none());
    }

    #[test]
    fn generic_args_substitute_into_inherited_members() {
        // Collection<T> with `add(T): void` and `first(): T`; a concrete
        // subclass binds T = User and inherited members specialise.
        let idx = index(
            r#"<?php
            /** @template T */
            class Collection {
                /** @param T $item */
                public function add($item): void {}
                /** @return T */
                public function first() {}
            }
            /** @extends Collection<User> */
            class Users extends Collection {}
            class User {}"#,
        );
        let add = idx.find_method("Users", "add").unwrap();
        assert_eq!(add.declaring_class, "Collection");
        assert_eq!(
            add.member.params[0].ty,
            Type::Named {
                fqn: "User".into(),
                args: vec![]
            }
        );
        let first = idx.find_method("Users", "first").unwrap();
        assert_eq!(
            first.member.return_type,
            Type::Named {
                fqn: "User".into(),
                args: vec![]
            }
        );
    }

    #[test]
    fn receiver_generic_args_substitute_own_method() {
        let idx = index(
            r#"<?php
            /** @template T */
            class Collection {
                /** @return T */
                public function first() {}
            }
            class User {}"#,
        );
        let receiver = generic("Collection", vec![named("User")]);
        let found = idx.find_method_on_type(&receiver, "first").unwrap();
        assert_eq!(found.declaring_class, "Collection");
        assert_eq!(found.member.return_type, named("User"));
    }

    #[test]
    fn receiver_generic_args_substitute_own_property() {
        let idx = index(
            r#"<?php
            /** @template T */
            class Box {
                /** @var T */
                public $value;
            }
            class User {}"#,
        );
        let receiver = generic("Box", vec![named("User")]);
        let found = idx.find_property_on_type(&receiver, "value").unwrap();
        assert_eq!(found.declaring_class, "Box");
        assert_eq!(found.member.ty, named("User"));
    }

    #[test]
    fn receiver_generic_builtin_arrayobject_offset_get() {
        let idx = ReflectionIndex::with_builtins();
        let receiver = generic("ArrayObject", vec![Type::Int, named("User")]);
        let found = idx.find_method_on_type(&receiver, "offsetGet").unwrap();
        assert_eq!(found.member.return_type.to_string(), "User|null");
    }

    #[test]
    fn receiver_substitution_composes_through_inherited_parent() {
        let idx = index(
            r#"<?php
            /** @template T */
            class ParentBox {
                /** @return T */
                public function get() {}
            }
            /**
             * @template U
             * @extends ParentBox<U>
             */
            class ChildBox extends ParentBox {}
            class User {}"#,
        );
        let receiver = generic("ChildBox", vec![named("User")]);
        let found = idx.find_method_on_type(&receiver, "get").unwrap();
        assert_eq!(found.declaring_class, "ParentBox");
        assert_eq!(found.member.return_type, named("User"));
    }

    #[test]
    fn substitution_composes_through_two_levels() {
        // Map<K,V> -> StringMap<V> binds K=string -> IntStringMap binds V=int.
        let idx = index(
            r#"<?php
            /**
             * @template K
             * @template V
             */
            class Map {
                /** @return array<K, V> */
                public function all(): array {}
            }
            /**
             * @template V
             * @extends Map<string, V>
             */
            class StringMap extends Map {}
            /** @extends StringMap<int> */
            class IntStringMap extends StringMap {}"#,
        );
        let all = idx.find_method("IntStringMap", "all").unwrap();
        assert_eq!(all.member.return_type.to_string(), "array<string, int>");
    }

    #[test]
    fn cycle_in_hierarchy_does_not_loop() {
        // A pathological mutual-extends pair must terminate.
        let idx = index(
            r#"<?php
            class A extends B {}
            class B extends A {}"#,
        );
        assert!(idx.find_method("A", "whatever").is_none());
    }

    #[test]
    fn enum_magic_members_are_reflected() {
        let idx = index(
            r#"<?php
            enum Suit: string { case Hearts = 'H'; }"#,
        );
        assert_eq!(
            idx.find_property("Suit", "name").unwrap().member.ty,
            Type::String
        );
        assert_eq!(
            idx.find_property("Suit", "value").unwrap().member.ty,
            Type::String
        );
        assert_eq!(
            idx.find_method("Suit", "cases")
                .unwrap()
                .member
                .return_type
                .to_string(),
            "list<static>"
        );
        assert_eq!(
            idx.find_method("Suit", "tryFrom")
                .unwrap()
                .member
                .return_type
                .to_string(),
            "?static"
        );
    }

    #[test]
    fn builtin_class_members_are_loaded() {
        let idx = ReflectionIndex::with_builtins();
        assert_eq!(
            idx.find_method("DateTimeImmutable", "format")
                .unwrap()
                .member
                .return_type,
            Type::String
        );
        assert_eq!(
            idx.find_method("DateTimeZone", "getName")
                .unwrap()
                .member
                .return_type,
            Type::String
        );
    }

    #[test]
    fn builtin_generic_class_templates_substitute_through_extends() {
        let r = php_parser::parse(
            r#"<?php
            class User {}
            /** @extends \ArrayObject<int, User> */
            class Users extends \ArrayObject {}
            "#,
        );
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::with_builtins();
        idx.add_file(&r.program, &r.interner);

        assert_eq!(
            idx.class("ArrayObject").unwrap().templates,
            ["TKey", "TValue"]
        );
        assert_eq!(
            idx.class("Users").unwrap().parents[0].to_string(),
            "ArrayObject<int, User>"
        );
        let offset_get = idx.find_method("Users", "offsetGet").unwrap();
        assert_eq!(offset_get.member.return_type.to_string(), "User|null");
    }

    #[test]
    fn builtin_signatures_follow_selected_php_version() {
        let idx84 = ReflectionIndex::with_builtins_for(PhpVersion::from_id(80400).unwrap());
        assert_eq!(
            idx84.function("array_multisort").unwrap().return_type,
            Type::Bool
        );

        let idx85 = ReflectionIndex::with_builtins_for(PhpVersion::from_id(80500).unwrap());
        assert_eq!(
            idx85.function("array_multisort").unwrap().return_type,
            Type::True
        );

        let idx86 = ReflectionIndex::with_builtins_for(PhpVersion::from_id(80600).unwrap());
        assert_eq!(
            idx86.function("array_multisort").unwrap().return_type,
            Type::True
        );

        let below = ReflectionIndex::with_builtins_for(PhpVersion::from_id(70400).unwrap());
        assert_eq!(
            below.function("array_multisort").unwrap().return_type,
            Type::Bool
        );

        let above = ReflectionIndex::with_builtins_for(PhpVersion::from_id(90000).unwrap());
        assert_eq!(
            above.function("array_multisort").unwrap().return_type,
            Type::True
        );
    }

    #[test]
    fn builtin_names_match_typed_manifests_for_supported_versions() {
        for id in [80400, 80500, 80600] {
            let version = PhpVersion::from_id(id).unwrap();
            let project = php_index::ProjectIndex::with_builtins_for(version);
            let reflection = ReflectionIndex::with_builtins_for(version);

            let project_functions: BTreeSet<_> = project
                .functions()
                .map(|f| SymbolKey::function(&f.fqn).into_string())
                .collect();
            let reflection_functions: BTreeSet<_> = reflection.functions.keys().cloned().collect();
            assert_eq!(
                project_functions, reflection_functions,
                "builtin function manifest drift for PHP {id}"
            );

            let project_classes: BTreeSet<_> = project
                .classes()
                .map(|c| SymbolKey::class_like(&c.fqn).into_string())
                .collect();
            let reflection_classes: BTreeSet<_> = reflection.classes.keys().cloned().collect();
            assert_eq!(
                project_classes, reflection_classes,
                "builtin class manifest drift for PHP {id}"
            );

            let project_constants: BTreeSet<_> = project
                .constants()
                .map(|c| SymbolKey::constant(&c.fqn).into_string())
                .collect();
            let manifest_constants: BTreeSet<_> = php_types::builtins::constants_for(version)
                .into_iter()
                .map(|c| SymbolKey::constant(c.fqn).into_string())
                .collect();
            assert_eq!(
                project_constants, manifest_constants,
                "builtin constant manifest drift for PHP {id}"
            );
        }
    }

    #[test]
    fn reflected_file_discovers_same_nested_declarations_as_project_index() {
        let r = php_parser::parse(
            r#"<?php
            if (true) {
                function conditional_fn(): int {}
                class ConditionalClass {}
            }
            class Host {
                public function boot(): void {
                    function method_fn(): string {}
                    class MethodClass {}
                }
            }"#,
        );
        assert!(!r.has_errors(), "parse errors");

        let file_index = php_resolve::index_file(&r.program, &r.interner);
        let mut project = php_index::ProjectIndex::new();
        project.add_file("fixture.php", &file_index);

        let mut reflection = ReflectionIndex::new();
        reflection.add_file(&r.program, &r.interner);

        for name in ["conditional_fn", "method_fn"] {
            assert_eq!(
                project.has_function(name),
                reflection.function(name).is_some(),
                "function discovery diverged for {name}"
            );
        }
        for name in ["ConditionalClass", "Host", "MethodClass"] {
            assert_eq!(
                project.has_class(name),
                reflection.class(name).is_some(),
                "class discovery diverged for {name}"
            );
        }

        let reflected = reflect_file(&r.program, &r.interner);
        assert!(reflected
            .functions
            .iter()
            .any(|f| f.reflection.fqn == "method_fn"));
        assert!(reflected
            .classes
            .iter()
            .any(|c| c.reflection.fqn == "MethodClass"));
    }

    #[test]
    fn scan_file_does_not_override_builtin_function() {
        let r = php_parser::parse("<?php function strlen(): bool {}");
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::with_builtins();
        idx.add_file_as(&r.program, &r.interner, SourceKind::Scan);
        assert_eq!(idx.function("strlen").unwrap().return_type, Type::Int);
    }
}
