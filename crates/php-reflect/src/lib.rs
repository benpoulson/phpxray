//! Reflection: turn the syntactic types and declarations of a parsed file into
//! the resolved semantic types ([`php_types::Type`]) and reflection descriptors
//! the type system queries.
//!
//! M-T0 (here): resolve a native `php_ast::Type` to a [`Type`], with class names
//! resolved to FQNs via name resolution. Later milestones resolve PHPDoc types
//! and build full class/function reflections (merging native + PHPDoc).

use php_ast::{Type as AstType, TypeKind};
use php_resolve::{Resolution, Scope};
use php_types::Type;

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
}
