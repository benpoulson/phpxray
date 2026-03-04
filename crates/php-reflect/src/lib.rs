//! Reflection: turn the syntactic types and declarations of a parsed file into
//! the resolved semantic types ([`php_types::Type`]) and reflection descriptors
//! the type system queries.
//!
//! M-T0 (here): resolve a native `php_ast::Type` to a [`Type`], with class names
//! resolved to FQNs via name resolution. Later milestones resolve PHPDoc types
//! and build full class/function reflections (merging native + PHPDoc).

use php_ast::{Name, NameFq, Type as AstType, TypeKind};
use php_phpdoc::DocType;
use php_resolve::{Resolution, Scope};
use php_span::Span;
use php_types::{CallableSig, ShapeField, Type};

mod model;
mod project;
pub use model::{
    reflect_class, reflect_function, ClassReflection, ConstReflection, FunctionReflection,
    MethodReflection, ParamReflection, PropertyReflection,
};
pub use project::{Found, ReflectionIndex};

/// Resolve a native PHP type declaration to a semantic [`Type`] in `scope`.
pub fn resolve_ast_type(scope: &Scope, ty: &AstType) -> Type {
    match &ty.kind {
        TypeKind::Simple(name) => match scope.resolve_class(name) {
            Resolution::BuiltinType(kw) => builtin(&kw),
            Resolution::LateStatic(s) => match s.as_str() {
                "self" => Type::SelfType,
                "parent" => Type::Parent,
                _ => Type::StaticType,
            },
            Resolution::Fqn(fqn) => Type::Named { fqn, args: Vec::new() },
            // Native type position never yields a fallback, but be total.
            Resolution::Fallback { namespaced, .. } => Type::Named { fqn: namespaced, args: Vec::new() },
        },
        TypeKind::Nullable(inner) => resolve_ast_type(scope, inner).nullable(),
        TypeKind::Union(parts) => Type::union(parts.iter().map(|p| resolve_ast_type(scope, p)).collect()),
        TypeKind::Intersection(parts) => {
            Type::intersection(parts.iter().map(|p| resolve_ast_type(scope, p)).collect())
        }
    }
}

/// Resolve a PHPDoc type expression ([`DocType`]) to a semantic [`Type`] in
/// `scope`. `templates` are the generic template names in effect (from
/// `@template T` on the enclosing class/function); a [`DocType::Named`] matching
/// one of them becomes a [`Type::TemplateVar`] rather than a class reference.
pub fn resolve_doc_type(scope: &Scope, templates: &[String], t: &DocType) -> Type {
    match t {
        DocType::Named(name) => doc_named(scope, templates, name),
        DocType::Nullable(inner) => resolve_doc_type(scope, templates, inner).nullable(),
        DocType::Union(parts) => {
            Type::union(parts.iter().map(|p| resolve_doc_type(scope, templates, p)).collect())
        }
        DocType::Intersection(parts) => {
            Type::intersection(parts.iter().map(|p| resolve_doc_type(scope, templates, p)).collect())
        }
        // `T[]` — array of `T`, keyed by `array-key`.
        DocType::Array(inner) => {
            let v = resolve_doc_type(scope, templates, inner);
            Type::Array(Some(Box::new((array_key(), v))))
        }
        DocType::Generic { base, args } => doc_generic(scope, templates, base, args),
        DocType::Shape { fields, sealed, .. } => Type::Shape {
            fields: fields
                .iter()
                .map(|fld| ShapeField {
                    key: fld.key.clone(),
                    optional: fld.optional,
                    ty: resolve_doc_type(scope, templates, &fld.ty),
                })
                .collect(),
            sealed: *sealed,
        },
        DocType::Callable { params, ret, .. } => Type::Callable(Some(Box::new(CallableSig {
            params: params.iter().map(|p| resolve_doc_type(scope, templates, p)).collect(),
            ret: ret.as_ref().map(|r| resolve_doc_type(scope, templates, r)).unwrap_or(Type::Mixed),
        }))),
        DocType::ConstString(s) => Type::LiteralString(s.clone()),
        DocType::ConstInt(s) => match s.parse::<i64>() {
            Ok(n) => Type::LiteralInt(n),
            Err(_) => Type::Int,
        },
        DocType::Conditional { subject, negated, target, then, els } => Type::Conditional {
            subject: subject.clone(),
            negated: *negated,
            target: Box::new(resolve_doc_type(scope, templates, target)),
            then: Box::new(resolve_doc_type(scope, templates, then)),
            els: Box::new(resolve_doc_type(scope, templates, els)),
        },
    }
}

/// Resolve a bare PHPDoc name: a template variable, a doc-only pseudo-type
/// keyword, a native keyword, or a class reference.
fn doc_named(scope: &Scope, templates: &[String], name: &str) -> Type {
    if templates.iter().any(|t| t == name) {
        return Type::TemplateVar(name.to_string());
    }
    match doc_keyword(name) {
        Some(t) => t,
        None => match scope.resolve_class(&name_from(name)) {
            Resolution::BuiltinType(kw) => builtin(&kw),
            Resolution::LateStatic(s) => match s.as_str() {
                "self" => Type::SelfType,
                "parent" => Type::Parent,
                _ => Type::StaticType,
            },
            Resolution::Fqn(fqn) => Type::Named { fqn, args: Vec::new() },
            Resolution::Fallback { namespaced, .. } => Type::Named { fqn: namespaced, args: Vec::new() },
        },
    }
}

/// Doc-only pseudo-type keywords that aren't native PHP types (and the native
/// aliases PHPDoc allows, like `integer`/`boolean`). Returns `None` for anything
/// that should be treated as a class name or native keyword.
fn doc_keyword(name: &str) -> Option<Type> {
    // Case-insensitive on the bare word (no namespace separators).
    let lower = name.to_ascii_lowercase();
    Some(match lower.as_str() {
        "$this" => Type::StaticType,
        "self" => Type::SelfType,
        "parent" => Type::Parent,
        "static" => Type::StaticType,
        "resource" | "closed-resource" => Type::Resource,
        "list" | "non-empty-list" => Type::List(Box::new(Type::Mixed)),
        "class-string" | "interface-string" | "trait-string" | "enum-string" => {
            Type::ClassString(None)
        }
        "array-key" => array_key(),
        "scalar" => Type::union(vec![Type::Int, Type::Float, Type::String, Type::Bool]),
        "number" | "numeric" => Type::union(vec![Type::Int, Type::Float]),
        // Refinements we don't model precisely collapse to their base type.
        "positive-int" | "negative-int" | "non-positive-int" | "non-negative-int"
        | "non-zero-int" | "int-mask" | "integer" => Type::Int,
        "double" => Type::Float,
        "boolean" => Type::Bool,
        "non-empty-string" | "non-falsy-string" | "truthy-string" | "numeric-string"
        | "lowercase-string" | "literal-string" | "html-escaped-string" => Type::String,
        "key-of" | "value-of" => Type::Mixed,
        "noreturn" | "no-return" => Type::Never,
        "empty" => Type::Unknown("empty".into()),
        _ => return None,
    })
}

/// Resolve a generic application `base<args>`.
fn doc_generic(scope: &Scope, templates: &[String], base: &str, args: &[DocType]) -> Type {
    let resolved: Vec<Type> = args.iter().map(|a| resolve_doc_type(scope, templates, a)).collect();
    let lower = base.to_ascii_lowercase();
    match lower.as_str() {
        "array" => match resolved.as_slice() {
            [v] => Type::Array(Some(Box::new((array_key(), v.clone())))),
            [k, v] => Type::Array(Some(Box::new((k.clone(), v.clone())))),
            _ => Type::Array(None),
        },
        "non-empty-array" => match resolved.as_slice() {
            [v] => Type::Array(Some(Box::new((array_key(), v.clone())))),
            [k, v] => Type::Array(Some(Box::new((k.clone(), v.clone())))),
            _ => Type::Array(None),
        },
        "iterable" => match resolved.as_slice() {
            [v] => Type::Iterable(Some(Box::new((array_key(), v.clone())))),
            [k, v] => Type::Iterable(Some(Box::new((k.clone(), v.clone())))),
            _ => Type::Iterable(None),
        },
        "list" | "non-empty-list" => {
            Type::List(Box::new(resolved.into_iter().last().unwrap_or(Type::Mixed)))
        }
        "class-string" | "interface-string" => {
            Type::ClassString(resolved.into_iter().next().map(Box::new))
        }
        // `int<0, 100>` — a bounded int range we don't model; collapse to `int`.
        "int" => Type::Int,
        // `key-of<T>` / `value-of<T>` / `int-mask-of<T>` — unmodelled refinements.
        "key-of" | "value-of" | "int-mask-of" | "int-mask" => Type::Mixed,
        // A user/class generic, e.g. `Collection<int, User>`.
        _ => match doc_named(scope, templates, base) {
            Type::Named { fqn, .. } => Type::Named { fqn, args: resolved },
            // Template or keyword base with args (unusual): keep the base, drop args.
            other => other,
        },
    }
}

/// The implicit key type of an unparameterised array: `int|string`.
fn array_key() -> Type {
    Type::union(vec![Type::Int, Type::String])
}

/// Build a `php_ast::Name` from PHPDoc text, classifying its `NameFq` so name
/// resolution applies imports/namespacing correctly.
fn name_from(text: &str) -> Name {
    let fq = if text.starts_with("namespace\\") {
        NameFq::Relative
    } else if text.starts_with('\\') {
        NameFq::Fq
    } else {
        NameFq::NotFq
    };
    Name { span: Span::at(0), fq, text: text.to_string() }
}

/// Map a reserved built-in type keyword (lowercased) to its semantic [`Type`].
fn builtin(kw: &str) -> Type {
    match kw {
        "int" => Type::Int,
        "float" => Type::Float,
        "string" => Type::String,
        "bool" => Type::Bool,
        "true" => Type::True,
        "false" => Type::False,
        "void" => Type::Void,
        "null" => Type::Null,
        "never" => Type::Never,
        "mixed" => Type::Mixed,
        "object" => Type::Object,
        "array" => Type::Array(None),
        "iterable" => Type::Iterable(None),
        "callable" => Type::Callable(None),
        other => Type::Unknown(other.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_ast::{Name, NameFq};
    use php_span::Span;

    fn simple(fq: NameFq, text: &str) -> AstType {
        AstType {
            span: Span::at(0),
            kind: TypeKind::Simple(Name { span: Span::at(0), fq, text: text.into() }),
        }
    }
    fn nullable(t: AstType) -> AstType {
        AstType { span: Span::at(0), kind: TypeKind::Nullable(Box::new(t)) }
    }
    fn union(parts: Vec<AstType>) -> AstType {
        AstType { span: Span::at(0), kind: TypeKind::Union(parts) }
    }
    fn intersection(parts: Vec<AstType>) -> AstType {
        AstType { span: Span::at(0), kind: TypeKind::Intersection(parts) }
    }

    fn app_scope() -> Scope {
        let mut s = Scope::in_namespace("App");
        s.add_class_use("Collection", "Illuminate\\Support\\Collection");
        s
    }

    #[test]
    fn scalar_keywords() {
        let s = Scope::global();
        for (kw, ty) in [
            ("int", Type::Int),
            ("string", Type::String),
            ("bool", Type::Bool),
            ("float", Type::Float),
            ("void", Type::Void),
            ("mixed", Type::Mixed),
            ("never", Type::Never),
            ("object", Type::Object),
            ("array", Type::Array(None)),
            ("iterable", Type::Iterable(None)),
            ("callable", Type::Callable(None)),
            ("false", Type::False),
        ] {
            assert_eq!(resolve_ast_type(&s, &simple(NameFq::NotFq, kw)), ty, "{kw}");
        }
    }

    #[test]
    fn class_names_resolve_to_fqns() {
        let s = app_scope();
        // Unqualified -> current namespace.
        assert_eq!(
            resolve_ast_type(&s, &simple(NameFq::NotFq, "User")),
            Type::Named { fqn: "App\\User".into(), args: vec![] }
        );
        // Imported alias.
        assert_eq!(
            resolve_ast_type(&s, &simple(NameFq::NotFq, "Collection")),
            Type::Named { fqn: "Illuminate\\Support\\Collection".into(), args: vec![] }
        );
        // Fully qualified -> leading backslash stripped.
        assert_eq!(
            resolve_ast_type(&s, &simple(NameFq::Fq, "\\DateTimeImmutable")),
            Type::Named { fqn: "DateTimeImmutable".into(), args: vec![] }
        );
    }

    #[test]
    fn self_parent_static() {
        let s = app_scope();
        assert_eq!(resolve_ast_type(&s, &simple(NameFq::NotFq, "self")), Type::SelfType);
        assert_eq!(resolve_ast_type(&s, &simple(NameFq::NotFq, "parent")), Type::Parent);
        assert_eq!(resolve_ast_type(&s, &simple(NameFq::NotFq, "static")), Type::StaticType);
    }

    #[test]
    fn nullable_union_intersection() {
        let s = app_scope();
        assert_eq!(resolve_ast_type(&s, &nullable(simple(NameFq::NotFq, "int"))), Type::Nullable(Box::new(Type::Int)));
        assert_eq!(
            resolve_ast_type(&s, &union(vec![simple(NameFq::NotFq, "User"), simple(NameFq::NotFq, "null")])).to_string(),
            "App\\User|null"
        );
        assert_eq!(
            resolve_ast_type(&s, &intersection(vec![simple(NameFq::NotFq, "Countable"), simple(NameFq::NotFq, "Traversable")])).to_string(),
            "App\\Countable&App\\Traversable"
        );
    }

    // --- PHPDoc type resolution (M-T1) -----------------------------------

    /// Resolve a PHPDoc type *string* end-to-end via the real PHPDoc parser.
    fn doc(scope: &Scope, templates: &[&str], s: &str) -> Type {
        let dt = php_phpdoc::parse_type(s).unwrap_or_else(|| panic!("parse_type failed: {s:?}"));
        let tpl: Vec<String> = templates.iter().map(|t| t.to_string()).collect();
        resolve_doc_type(scope, &tpl, &dt)
    }

    #[test]
    fn doc_scalars_and_aliases() {
        let s = Scope::global();
        assert_eq!(doc(&s, &[], "int"), Type::Int);
        assert_eq!(doc(&s, &[], "integer"), Type::Int);
        assert_eq!(doc(&s, &[], "boolean"), Type::Bool);
        assert_eq!(doc(&s, &[], "double"), Type::Float);
        assert_eq!(doc(&s, &[], "mixed"), Type::Mixed);
        assert_eq!(doc(&s, &[], "void"), Type::Void);
    }

    #[test]
    fn doc_pseudo_types() {
        let s = Scope::global();
        assert_eq!(doc(&s, &[], "array-key").to_string(), "int|string");
        assert_eq!(doc(&s, &[], "class-string"), Type::ClassString(None));
        assert_eq!(doc(&s, &[], "list"), Type::List(Box::new(Type::Mixed)));
        assert_eq!(doc(&s, &[], "positive-int"), Type::Int);
        assert_eq!(doc(&s, &[], "non-empty-string"), Type::String);
        assert_eq!(doc(&s, &[], "scalar").to_string(), "int|float|string|bool");
        assert_eq!(doc(&s, &[], "numeric").to_string(), "int|float");
        assert_eq!(doc(&s, &[], "$this"), Type::StaticType);
        assert_eq!(doc(&s, &[], "resource"), Type::Resource);
    }

    #[test]
    fn doc_templates_win_over_classes() {
        let s = app_scope();
        assert_eq!(doc(&s, &["T"], "T"), Type::TemplateVar("T".into()));
        // A non-template name in the same scope resolves as a class.
        assert_eq!(doc(&s, &["T"], "User"), Type::Named { fqn: "App\\User".into(), args: vec![] });
    }

    #[test]
    fn doc_class_names_resolve_to_fqns() {
        let s = app_scope();
        assert_eq!(doc(&s, &[], "User"), Type::Named { fqn: "App\\User".into(), args: vec![] });
        assert_eq!(
            doc(&s, &[], "Collection"),
            Type::Named { fqn: "Illuminate\\Support\\Collection".into(), args: vec![] }
        );
        assert_eq!(doc(&s, &[], "\\DateTimeImmutable"), Type::Named { fqn: "DateTimeImmutable".into(), args: vec![] });
    }

    #[test]
    fn doc_arrays_and_generics() {
        let s = app_scope();
        assert_eq!(doc(&s, &[], "int[]").to_string(), "array<int|string, int>");
        assert_eq!(doc(&s, &[], "array<int>").to_string(), "array<int|string, int>");
        assert_eq!(doc(&s, &[], "array<string, User>").to_string(), "array<string, App\\User>");
        assert_eq!(doc(&s, &[], "list<int>"), Type::List(Box::new(Type::Int)));
        assert_eq!(doc(&s, &[], "iterable<User>").to_string(), "iterable<int|string, App\\User>");
        assert_eq!(doc(&s, &[], "class-string<User>").to_string(), "class-string<App\\User>");
        assert_eq!(doc(&s, &[], "int<0, 100>"), Type::Int);
    }

    #[test]
    fn doc_user_generic_resolves_base_and_args() {
        let s = app_scope();
        assert_eq!(
            doc(&s, &["TKey", "TValue"], "Collection<TKey, User>"),
            Type::Named {
                fqn: "Illuminate\\Support\\Collection".into(),
                args: vec![Type::TemplateVar("TKey".into()), Type::Named { fqn: "App\\User".into(), args: vec![] }],
            }
        );
    }

    #[test]
    fn doc_shapes_callables_literals_conditionals() {
        let s = Scope::global();
        assert_eq!(doc(&s, &[], "array{id: int, name?: string}").to_string(), "array{id: int, name?: string}");
        assert_eq!(doc(&s, &[], "callable(int, string): bool").to_string(), "callable(int, string): bool");
        assert_eq!(doc(&s, &[], "'draft'|'published'").to_string(), "'draft'|'published'");
        assert_eq!(doc(&s, &[], "1|2|3").to_string(), "1|2|3");
        assert_eq!(
            doc(&s, &["T"], "(T is int ? string : bool)").to_string(),
            "(T is int ? string : bool)"
        );
    }
}
