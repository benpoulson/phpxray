//! M-T2: the **reflection model** — per-declaration descriptors whose member
//! types are fully resolved.
//!
//! A [`ClassReflection`] / [`FunctionReflection`] is the semantic view of a
//! class or function the type system queries: every member's type is a
//! [`Type`], with native declarations and PHPDoc annotations merged and class
//! names resolved to FQNs. PHPDoc refines native: when both a native type hint
//! and a `@param`/`@return`/`@var` are present, the doc type wins (it carries
//! generics, shapes, and literal types the native syntax can't express).
//!
//! Magic members declared only in the class docblock — `@method` and
//! `@property*` (heavily used by Laravel facades and barryvdh/ide-helper) — are
//! reflected alongside the real members, flagged [`MethodReflection::magic`] /
//! [`PropertyReflection::magic`]. Generic parent type arguments from
//! `@extends`/`@implements`/`@use` are attached to the corresponding resolved
//! parent/interface/trait.

use crate::{resolve_ast_type, resolve_doc_type};
use php_ast::{
    ClassDecl, ClassKind, FunctionDecl, Member, MethodDecl, Name, Param as AstParam, PropertyDecl,
    Type as AstType, Visibility,
};
use php_intern::Interner;
use php_phpdoc::{Doc, DocType, MethodParam, PropertyAccess};
use php_resolve::Scope;
use php_types::Type;

/// A reflected function or method parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamReflection {
    /// Variable name without the leading `$`.
    pub name: String,
    /// The resolved type (`mixed` when neither a hint nor a `@param` is given).
    pub ty: Type,
    pub by_ref: bool,
    pub variadic: bool,
    /// Has a default value or is variadic (so may be omitted at the call site).
    pub optional: bool,
    /// Declared via constructor property promotion (`public int $x`).
    pub promoted: bool,
}

/// A reflected free function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionReflection {
    pub fqn: String,
    pub params: Vec<ParamReflection>,
    pub return_type: Type,
    pub by_ref: bool,
    /// `@template` names in scope for this function.
    pub templates: Vec<String>,
    pub deprecated: bool,
}

/// A reflected method (real or magic `@method`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MethodReflection {
    pub name: String,
    pub visibility: Visibility,
    pub is_static: bool,
    pub is_abstract: bool,
    pub is_final: bool,
    pub params: Vec<ParamReflection>,
    pub return_type: Type,
    /// `@template` names in scope (class templates plus the method's own).
    pub templates: Vec<String>,
    pub deprecated: bool,
    /// Declared only via a class-level `@method` tag (no real implementation).
    pub magic: bool,
}

/// A reflected property (real or magic `@property*`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropertyReflection {
    /// Property name without the leading `$`.
    pub name: String,
    pub visibility: Visibility,
    pub is_static: bool,
    pub is_readonly: bool,
    pub ty: Type,
    pub has_default: bool,
    /// Read/write access — always [`PropertyAccess::ReadWrite`] for real
    /// properties; reflects the `@property-read`/`-write` tag for magic ones.
    pub access: PropertyAccess,
    /// Declared only via a class-level `@property*` tag.
    pub magic: bool,
}

/// A reflected class constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstReflection {
    pub name: String,
    pub visibility: Visibility,
    /// Declared const type (`const int X = 1`) or `mixed`. Value inference is a
    /// later milestone.
    pub ty: Type,
    pub is_final: bool,
}

/// The semantic view of a class/interface/trait/enum declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassReflection {
    pub fqn: String,
    pub kind: ClassKind,
    pub is_abstract: bool,
    pub is_final: bool,
    pub is_readonly: bool,
    /// Parent class(es), resolved, with `@extends` generic args attached.
    pub parents: Vec<Type>,
    /// Implemented interfaces, with `@implements` generic args attached.
    pub interfaces: Vec<Type>,
    /// Used traits, with `@use` generic args attached.
    pub traits: Vec<Type>,
    /// `@template` names declared on the class.
    pub templates: Vec<String>,
    pub methods: Vec<MethodReflection>,
    pub properties: Vec<PropertyReflection>,
    pub constants: Vec<ConstReflection>,
    /// `@mixin` targets, resolved.
    pub mixins: Vec<Type>,
    pub deprecated: bool,
}

/// Reflect a free function declaration.
pub fn reflect_function(scope: &Scope, interner: &Interner, f: &FunctionDecl) -> FunctionReflection {
    let doc = parse_doc(f.doc.as_deref());
    let templates: Vec<String> = doc.templates.iter().map(|t| t.name.clone()).collect();
    FunctionReflection {
        fqn: scope.qualify(interner.resolve(f.name)),
        params: reflect_params(scope, interner, &templates, &f.params, &doc),
        return_type: merge_type(scope, &templates, f.return_type.as_ref(), doc.returns.as_ref()),
        by_ref: f.by_ref,
        templates,
        deprecated: doc.deprecated,
    }
}

/// Reflect a class/interface/trait/enum declaration. `fqn` is its already-resolved
/// fully-qualified name (the caller knows the declaring scope).
pub fn reflect_class(scope: &Scope, interner: &Interner, fqn: &str, c: &ClassDecl) -> ClassReflection {
    let doc = parse_doc(c.doc.as_deref());
    let class_templates: Vec<String> = doc.templates.iter().map(|t| t.name.clone()).collect();

    let mut methods = Vec::new();
    let mut properties = Vec::new();
    let mut constants = Vec::new();
    for m in &c.members {
        match m {
            Member::Method(md) => methods.push(reflect_method(scope, interner, &class_templates, md)),
            Member::Property(pd) => {
                reflect_properties(scope, interner, &class_templates, pd, &mut properties)
            }
            Member::ClassConst(cd) => reflect_consts(scope, cd, interner, &mut constants),
            // Enum cases and trait-use adaptations aren't members the type query
            // layer needs yet; traits are surfaced via `traits` below.
            Member::EnumCase(_) | Member::TraitUse(_) => {}
        }
    }

    // Magic members from the class docblock.
    methods.extend(doc.methods.iter().map(|m| magic_method(scope, &class_templates, m)));
    properties.extend(doc.properties.iter().filter_map(|p| magic_property(scope, &class_templates, p)));

    let traits: Vec<Name> = c
        .members
        .iter()
        .filter_map(|m| match m {
            Member::TraitUse(tu) => Some(tu.traits.iter().cloned()),
            _ => None,
        })
        .flatten()
        .collect();

    ClassReflection {
        fqn: fqn.to_string(),
        kind: c.kind,
        is_abstract: c.modifiers.is_abstract,
        is_final: c.modifiers.is_final,
        is_readonly: c.modifiers.is_readonly,
        parents: parents_with_generics(scope, &class_templates, &c.extends, &doc.extends),
        interfaces: parents_with_generics(scope, &class_templates, &c.implements, &doc.implements),
        traits: parents_with_generics(scope, &class_templates, &traits, &doc.uses),
        mixins: doc.mixins.iter().map(|m| resolve_doc_type(scope, &class_templates, m)).collect(),
        templates: class_templates,
        methods,
        properties,
        constants,
        deprecated: doc.deprecated,
    }
}

fn reflect_method(scope: &Scope, interner: &Interner, class_templates: &[String], m: &MethodDecl) -> MethodReflection {
    let doc = parse_doc(m.doc.as_deref());
    let templates = combine_templates(class_templates, &doc);
    MethodReflection {
        name: interner.resolve(m.name).to_string(),
        visibility: m.modifiers.visibility.unwrap_or(Visibility::Public),
        is_static: m.modifiers.is_static,
        is_abstract: m.modifiers.is_abstract || m.body.is_none(),
        is_final: m.modifiers.is_final,
        params: reflect_params(scope, interner, &templates, &m.params, &doc),
        return_type: merge_type(scope, &templates, m.return_type.as_ref(), doc.returns.as_ref()),
        templates,
        deprecated: doc.deprecated,
        magic: false,
    }
}

fn reflect_properties(
    scope: &Scope,
    interner: &Interner,
    templates: &[String],
    pd: &PropertyDecl,
    out: &mut Vec<PropertyReflection>,
) {
    let doc = parse_doc(pd.doc.as_deref());
    // A property docblock's type is the single `@var` (the var name is usually
    // omitted on a property).
    let doc_ty = doc.vars.first().and_then(|v| v.ty.as_ref());
    let ty = merge_type(scope, templates, pd.ty.as_ref(), doc_ty);
    for elem in &pd.props {
        out.push(PropertyReflection {
            name: interner.resolve(elem.name).to_string(),
            visibility: pd.modifiers.visibility.unwrap_or(Visibility::Public),
            is_static: pd.modifiers.is_static,
            is_readonly: pd.modifiers.is_readonly,
            ty: ty.clone(),
            has_default: elem.default.is_some(),
            access: PropertyAccess::ReadWrite,
            magic: false,
        });
    }
}

fn reflect_consts(scope: &Scope, cd: &php_ast::ClassConstDecl, interner: &Interner, out: &mut Vec<ConstReflection>) {
    let ty = cd.ty.as_ref().map(|t| resolve_ast_type(scope, t)).unwrap_or(Type::Mixed);
    for c in &cd.consts {
        out.push(ConstReflection {
            name: interner.resolve(c.name).to_string(),
            visibility: cd.modifiers.visibility.unwrap_or(Visibility::Public),
            ty: ty.clone(),
            is_final: cd.modifiers.is_final,
        });
    }
}

/// Reflect a `@method` magic-method declaration.
fn magic_method(scope: &Scope, class_templates: &[String], m: &php_phpdoc::MethodTag) -> MethodReflection {
    let templates = class_templates.to_vec();
    MethodReflection {
        name: m.name.clone(),
        visibility: Visibility::Public,
        is_static: m.is_static,
        is_abstract: false,
        is_final: false,
        params: m.params.iter().map(|p| magic_param(scope, &templates, p)).collect(),
        return_type: m
            .return_type
            .as_ref()
            .map(|t| resolve_doc_type(scope, &templates, t))
            .unwrap_or(Type::Mixed),
        templates,
        deprecated: false,
        magic: true,
    }
}

fn magic_param(scope: &Scope, templates: &[String], p: &MethodParam) -> ParamReflection {
    ParamReflection {
        name: p.name.clone().unwrap_or_default(),
        ty: p.ty.as_ref().map(|t| resolve_doc_type(scope, templates, t)).unwrap_or(Type::Mixed),
        by_ref: p.by_ref,
        variadic: p.variadic,
        optional: p.default.is_some() || p.variadic,
        promoted: false,
    }
}

/// Reflect a `@property*` magic property. Skips tags without a name.
fn magic_property(scope: &Scope, templates: &[String], p: &php_phpdoc::PropertyTag) -> Option<PropertyReflection> {
    let name = p.name.clone()?;
    Some(PropertyReflection {
        name,
        visibility: Visibility::Public,
        is_static: false,
        is_readonly: p.access == PropertyAccess::ReadOnly,
        ty: p.ty.as_ref().map(|t| resolve_doc_type(scope, templates, t)).unwrap_or(Type::Mixed),
        has_default: false,
        access: p.access,
        magic: true,
    })
}

/// Reflect a parameter list, merging native hints with `@param` types by name.
fn reflect_params(
    scope: &Scope,
    interner: &Interner,
    templates: &[String],
    params: &[AstParam],
    doc: &Doc,
) -> Vec<ParamReflection> {
    params
        .iter()
        .map(|p| {
            let name = interner.resolve(p.name).to_string();
            let doc_ty = doc
                .params
                .iter()
                .find(|dp| dp.name.as_deref() == Some(name.as_str()))
                .and_then(|dp| dp.ty.as_ref());
            ParamReflection {
                ty: merge_type(scope, templates, p.ty.as_ref(), doc_ty),
                name,
                by_ref: p.by_ref,
                variadic: p.variadic,
                optional: p.default.is_some() || p.variadic,
                promoted: !p.modifiers.is_empty(),
            }
        })
        .collect()
}

/// Resolve native parents to types, attaching generic args from matching
/// `@extends`/`@implements`/`@use` doc generics (matched by resolved FQN).
fn parents_with_generics(scope: &Scope, templates: &[String], native: &[Name], doc_generics: &[DocType]) -> Vec<Type> {
    let doc_args: Vec<(String, Vec<Type>)> = doc_generics
        .iter()
        .filter_map(|d| match resolve_doc_type(scope, templates, d) {
            Type::Named { fqn, args } => Some((fqn, args)),
            _ => None,
        })
        .collect();
    native
        .iter()
        .filter_map(|n| {
            let fqn = scope.resolve_class(n).fqn()?.to_string();
            let args = doc_args.iter().find(|(f, _)| *f == fqn).map(|(_, a)| a.clone()).unwrap_or_default();
            Some(Type::Named { fqn, args })
        })
        .collect()
}

/// Merge a native type hint and a PHPDoc type: the doc type wins when present,
/// then the native hint, else `mixed`.
fn merge_type(scope: &Scope, templates: &[String], native: Option<&AstType>, doc: Option<&DocType>) -> Type {
    if let Some(d) = doc {
        return resolve_doc_type(scope, templates, d);
    }
    if let Some(n) = native {
        return resolve_ast_type(scope, n);
    }
    Type::Mixed
}

/// Class templates plus a method's own `@template` names.
fn combine_templates(class_templates: &[String], doc: &Doc) -> Vec<String> {
    let mut t = class_templates.to_vec();
    t.extend(doc.templates.iter().map(|d| d.name.clone()));
    t
}

/// Parse a declaration's docblock text, or an empty [`Doc`] when absent.
fn parse_doc(raw: Option<&str>) -> Doc {
    raw.map(php_phpdoc::parse).unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_resolve::index_file;

    /// Parse `src`, build the global scope, and reflect the first class.
    fn reflect_first_class(src: &str) -> (ClassReflection, Interner) {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors");
        let idx = index_file(&r.program, &r.interner);
        let fqn = idx.classes[0].fqn.clone();
        // Rebuild the declaring scope (global namespace here).
        let scope = Scope::global();
        let class = first_class(&r.program).expect("a class decl");
        (reflect_class(&scope, &r.interner, &fqn, class), r.interner)
    }

    fn first_class(p: &php_ast::Program) -> Option<&ClassDecl> {
        p.stmts.iter().find_map(|s| match &s.kind {
            php_ast::StmtKind::Class(c) => Some(c),
            _ => None,
        })
    }

    fn first_function(src: &str) -> (FunctionReflection, Interner) {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors");
        let scope = Scope::global();
        let f = r.program.stmts.iter().find_map(|s| match &s.kind {
            php_ast::StmtKind::Function(f) => Some(f),
            _ => None,
        });
        let refl = reflect_function(&scope, &r.interner, f.expect("a function"));
        (refl, r.interner)
    }

    #[test]
    fn function_params_and_return_native() {
        let (f, _) = first_function(r#"<?php function add(int $a, int $b = 0): int { return $a + $b; }"#);
        assert_eq!(f.fqn, "add");
        assert_eq!(f.params.len(), 2);
        assert_eq!(f.params[0].name, "a");
        assert_eq!(f.params[0].ty, Type::Int);
        assert!(!f.params[0].optional);
        assert!(f.params[1].optional);
        assert_eq!(f.return_type, Type::Int);
    }

    #[test]
    fn phpdoc_refines_native_param_and_return() {
        let (f, _) = first_function(
            r#"<?php
            /**
             * @param string[] $names
             * @return list<int>
             */
            function f(array $names): array { return []; }"#,
        );
        assert_eq!(f.params[0].ty.to_string(), "array<int|string, string>");
        assert_eq!(f.return_type.to_string(), "list<int>");
    }

    #[test]
    fn method_visibility_static_and_abstract() {
        let (c, _) = reflect_first_class(
            r#"<?php
            abstract class Repo {
                public function find(int $id): ?string { return null; }
                protected static function make(): static { }
                abstract public function all(): array;
            }"#,
        );
        assert!(c.is_abstract);
        let find = c.methods.iter().find(|m| m.name == "find").unwrap();
        assert_eq!(find.visibility, Visibility::Public);
        assert_eq!(find.return_type, Type::Nullable(Box::new(Type::String)));
        let make = c.methods.iter().find(|m| m.name == "make").unwrap();
        assert!(make.is_static && make.visibility == Visibility::Protected);
        assert_eq!(make.return_type, Type::StaticType);
        let all = c.methods.iter().find(|m| m.name == "all").unwrap();
        assert!(all.is_abstract);
    }

    #[test]
    fn properties_merge_var_and_promotion() {
        let (c, _) = reflect_first_class(
            r#"<?php
            class Box {
                /** @var array<string, int> */
                private array $items = [];
                public readonly string $name;
                public function __construct(public int $size) {}
            }"#,
        );
        let items = c.properties.iter().find(|p| p.name == "items").unwrap();
        assert_eq!(items.ty.to_string(), "array<string, int>");
        assert_eq!(items.visibility, Visibility::Private);
        assert!(items.has_default);
        let name = c.properties.iter().find(|p| p.name == "name").unwrap();
        assert!(name.is_readonly);
        // Constructor-promoted param shows up as a param on __construct.
        let ctor = c.methods.iter().find(|m| m.name == "__construct").unwrap();
        assert!(ctor.params[0].promoted && ctor.params[0].ty == Type::Int);
    }

    #[test]
    fn class_constants() {
        let (c, _) = reflect_first_class(
            r#"<?php
            class C {
                const A = 1;
                final protected const int B = 2;
            }"#,
        );
        let a = c.constants.iter().find(|k| k.name == "A").unwrap();
        assert_eq!(a.visibility, Visibility::Public);
        assert_eq!(a.ty, Type::Mixed);
        let b = c.constants.iter().find(|k| k.name == "B").unwrap();
        assert!(b.is_final && b.visibility == Visibility::Protected);
        assert_eq!(b.ty, Type::Int);
    }

    #[test]
    fn magic_methods_and_properties() {
        let (c, _) = reflect_first_class(
            r#"<?php
            /**
             * @method static \Builder where(string $column, mixed $value = null)
             * @property-read int $id
             * @property string $name
             */
            class Model {}"#,
        );
        let m = c.methods.iter().find(|m| m.name == "where").unwrap();
        assert!(m.magic && m.is_static);
        assert_eq!(m.return_type.to_string(), "Builder");
        assert_eq!(m.params.len(), 2);
        assert_eq!(m.params[0].ty, Type::String);
        assert!(m.params[1].optional);
        let id = c.properties.iter().find(|p| p.name == "id").unwrap();
        assert!(id.magic && id.is_readonly && id.ty == Type::Int);
        let name = c.properties.iter().find(|p| p.name == "name").unwrap();
        assert!(name.magic && name.access == PropertyAccess::ReadWrite);
    }

    #[test]
    fn generic_extends_and_implements_attach_args() {
        let (c, _) = reflect_first_class(
            r#"<?php
            /**
             * @extends \ArrayObject<int, string>
             * @implements \IteratorAggregate<int, string>
             */
            class Bag extends \ArrayObject implements \IteratorAggregate {}"#,
        );
        assert_eq!(c.parents[0].to_string(), "ArrayObject<int, string>");
        assert_eq!(c.interfaces[0].to_string(), "IteratorAggregate<int, string>");
    }

    #[test]
    fn class_templates_resolve_in_members() {
        let (c, _) = reflect_first_class(
            r#"<?php
            /**
             * @template T
             */
            class Collection {
                /** @param T $item */
                public function add($item): void {}
                /** @return T */
                public function first() {}
            }"#,
        );
        assert_eq!(c.templates, ["T"]);
        let add = c.methods.iter().find(|m| m.name == "add").unwrap();
        assert_eq!(add.params[0].ty, Type::TemplateVar("T".into()));
        let first = c.methods.iter().find(|m| m.name == "first").unwrap();
        assert_eq!(first.return_type, Type::TemplateVar("T".into()));
    }
}
