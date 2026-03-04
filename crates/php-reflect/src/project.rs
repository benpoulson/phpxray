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
    reflect_class, reflect_function, ClassReflection, ConstReflection, FunctionReflection, MethodReflection,
    PropertyReflection,
};
use php_ast::{ClassDecl, Program, StmtKind};
use php_intern::Interner;
use php_resolve::{for_each_region, Scope};
use php_types::{CallableSig, ShapeField, Type};
use std::collections::HashMap;

/// A map from `@template` names to the types bound for them along a hierarchy walk.
type Subst = HashMap<String, Type>;

/// A member found via hierarchy lookup, plus the class that declared it. Member
/// types have generic template variables substituted for the query's bindings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Found<T> {
    pub member: T,
    /// FQN of the class/interface/trait the member was declared on.
    pub declaring_class: String,
}

/// All reflected classes/functions across a set of files, keyed for lookup.
#[derive(Debug, Default)]
pub struct ReflectionIndex {
    /// Lowercased FQN → class reflection (class names are case-insensitive).
    classes: HashMap<String, ClassReflection>,
    /// Lowercased FQN → function reflection.
    functions: HashMap<String, FunctionReflection>,
}

impl ReflectionIndex {
    pub fn new() -> Self {
        Self::default()
    }

    /// Reflect every class and function in a parsed file and add them to the
    /// index. Later definitions of the same FQN overwrite earlier ones.
    pub fn add_file(&mut self, program: &Program, interner: &Interner) {
        for_each_region(&program.stmts, interner, |scope, region| {
            for st in region {
                self.collect_stmt(scope, interner, st);
            }
        });
    }

    /// Look up a class by FQN (case-insensitive, leading `\` ignored).
    pub fn class(&self, fqn: &str) -> Option<&ClassReflection> {
        self.classes.get(&key(fqn))
    }

    /// Look up a function by FQN (case-insensitive, leading `\` ignored).
    pub fn function(&self, fqn: &str) -> Option<&FunctionReflection> {
        self.functions.get(&key(fqn))
    }

    /// Number of indexed classes.
    pub fn class_count(&self) -> usize {
        self.classes.len()
    }

    /// Resolve a method by name through `class_fqn`'s hierarchy (own members
    /// first, then traits, parent class, interfaces, mixins). Method names match
    /// case-insensitively. Returns the method with generic args substituted.
    pub fn find_method(&self, class_fqn: &str, name: &str) -> Option<Found<MethodReflection>> {
        let mut visited = Vec::new();
        self.ascend(class_fqn, Subst::new(), &mut visited, &mut |class, subst| {
            class.methods.iter().find(|m| m.name.eq_ignore_ascii_case(name)).map(|m| Found {
                member: subst_method(m, subst),
                declaring_class: class.fqn.clone(),
            })
        })
    }

    /// Resolve a property by name (without `$`) through the hierarchy. Property
    /// names are case-sensitive.
    pub fn find_property(&self, class_fqn: &str, name: &str) -> Option<Found<PropertyReflection>> {
        let mut visited = Vec::new();
        self.ascend(class_fqn, Subst::new(), &mut visited, &mut |class, subst| {
            class.properties.iter().find(|p| p.name == name).map(|p| Found {
                member: PropertyReflection { ty: subst_type(&p.ty, subst), ..p.clone() },
                declaring_class: class.fqn.clone(),
            })
        })
    }

    /// Resolve a class constant by name through the hierarchy. Constant names are
    /// case-sensitive.
    pub fn find_constant(&self, class_fqn: &str, name: &str) -> Option<Found<ConstReflection>> {
        let mut visited = Vec::new();
        self.ascend(class_fqn, Subst::new(), &mut visited, &mut |class, subst| {
            class.constants.iter().find(|c| c.name == name).map(|c| Found {
                member: ConstReflection { ty: subst_type(&c.ty, subst), ..c.clone() },
                declaring_class: class.fqn.clone(),
            })
        })
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
        let k = key(fqn);
        if visited.contains(&k) {
            return None;
        }
        visited.push(k);
        let class = self.classes.get(&key(fqn))?;
        if let Some(found) = f(class, &subst) {
            return Some(found);
        }
        // Traits, then the parent class, then interfaces, then mixins.
        let parents = class.traits.iter().chain(&class.parents).chain(&class.interfaces).chain(&class.mixins);
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
        if let Some(parent) = self.classes.get(&key(pf)) {
            for (name, arg) in parent.templates.iter().zip(args) {
                map.insert(name.clone(), subst_type(arg, outer));
            }
        }
        map
    }

    fn collect_stmt(&mut self, scope: &Scope, interner: &Interner, st: &php_ast::Stmt) {
        match &st.kind {
            StmtKind::Class(c) => self.add_class(scope, interner, c),
            StmtKind::Function(f) => {
                let r = reflect_function(scope, interner, f);
                self.functions.insert(key(&r.fqn), r);
            }
            // Descend into nested/conditional declarations, mirroring the symbol
            // indexer so conditionally-declared classes are reflected too.
            StmtKind::Block(b) => self.collect_all(scope, interner, b),
            StmtKind::If { then, elseifs, els, .. } => {
                self.collect_stmt(scope, interner, then);
                for e in elseifs {
                    self.collect_stmt(scope, interner, &e.body);
                }
                if let Some(e) = els {
                    self.collect_stmt(scope, interner, e);
                }
            }
            StmtKind::While { body, .. }
            | StmtKind::DoWhile { body, .. }
            | StmtKind::For { body, .. }
            | StmtKind::Foreach { body, .. } => self.collect_stmt(scope, interner, body),
            StmtKind::Try { body, catches, finally } => {
                self.collect_all(scope, interner, body);
                for c in catches {
                    self.collect_all(scope, interner, &c.body);
                }
                if let Some(fin) = finally {
                    self.collect_all(scope, interner, fin);
                }
            }
            StmtKind::Switch { cases, .. } => {
                for case in cases {
                    self.collect_all(scope, interner, &case.body);
                }
            }
            StmtKind::Declare { body: Some(b), .. } => self.collect_stmt(scope, interner, b),
            _ => {}
        }
    }

    fn collect_all(&mut self, scope: &Scope, interner: &Interner, stmts: &[php_ast::Stmt]) {
        for st in stmts {
            self.collect_stmt(scope, interner, st);
        }
    }

    fn add_class(&mut self, scope: &Scope, interner: &Interner, c: &ClassDecl) {
        // Anonymous classes have no FQN.
        let Some(name) = c.name else { return };
        let fqn = scope.qualify(interner.resolve(name));
        let r = reflect_class(scope, interner, &fqn, c);
        self.classes.insert(key(&fqn), r);
    }
}

/// Normalise an FQN to a lookup key: drop a leading `\`, lowercase.
fn key(fqn: &str) -> String {
    fqn.trim_start_matches('\\').to_ascii_lowercase()
}

/// Apply a template substitution to a method's parameter and return types.
fn subst_method(m: &MethodReflection, subst: &Subst) -> MethodReflection {
    if subst.is_empty() {
        return m.clone();
    }
    let mut out = m.clone();
    for p in &mut out.params {
        p.ty = subst_type(&p.ty, subst);
    }
    out.return_type = subst_type(&out.return_type, subst);
    out
}

/// Recursively replace [`Type::TemplateVar`] occurrences using `subst`.
fn subst_type(ty: &Type, subst: &Subst) -> Type {
    if subst.is_empty() {
        return ty.clone();
    }
    match ty {
        Type::TemplateVar(name) => subst.get(name).cloned().unwrap_or_else(|| ty.clone()),
        Type::Nullable(inner) => Type::Nullable(Box::new(subst_type(inner, subst))),
        Type::Union(parts) => Type::union(parts.iter().map(|p| subst_type(p, subst)).collect()),
        Type::Intersection(parts) => Type::intersection(parts.iter().map(|p| subst_type(p, subst)).collect()),
        Type::List(inner) => Type::List(Box::new(subst_type(inner, subst))),
        Type::Array(Some(kv)) => Type::Array(Some(Box::new((subst_type(&kv.0, subst), subst_type(&kv.1, subst))))),
        Type::Iterable(Some(kv)) => {
            Type::Iterable(Some(Box::new((subst_type(&kv.0, subst), subst_type(&kv.1, subst)))))
        }
        Type::ClassString(Some(inner)) => Type::ClassString(Some(Box::new(subst_type(inner, subst)))),
        Type::Named { fqn, args } => {
            Type::Named { fqn: fqn.clone(), args: args.iter().map(|a| subst_type(a, subst)).collect() }
        }
        Type::Callable(Some(sig)) => Type::Callable(Some(Box::new(CallableSig {
            params: sig.params.iter().map(|p| subst_type(p, subst)).collect(),
            ret: subst_type(&sig.ret, subst),
        }))),
        Type::Shape { fields, sealed } => Type::Shape {
            fields: fields
                .iter()
                .map(|f| ShapeField { key: f.key.clone(), optional: f.optional, ty: subst_type(&f.ty, subst) })
                .collect(),
            sealed: *sealed,
        },
        Type::Conditional { subject, negated, target, then, els } => Type::Conditional {
            subject: subject.clone(),
            negated: *negated,
            target: Box::new(subst_type(target, subst)),
            then: Box::new(subst_type(then, subst)),
            els: Box::new(subst_type(els, subst)),
        },
        // Leaves and unparameterised forms are unchanged.
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn index(src: &str) -> ReflectionIndex {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::new();
        idx.add_file(&r.program, &r.interner);
        idx
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
        assert_eq!(add.member.params[0].ty, Type::Named { fqn: "User".into(), args: vec![] });
        let first = idx.find_method("Users", "first").unwrap();
        assert_eq!(first.member.return_type, Type::Named { fqn: "User".into(), args: vec![] });
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
}
