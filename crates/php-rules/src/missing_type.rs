//! Shared missing-type semantics for rules.

use php_ast::{Name, NameFq};
use php_phpdoc::DocType;
use php_reflect::ReflectionIndex;
use php_resolve::{display_fqn, Resolution, Scope, SymbolKey};
use php_span::Span;
use php_types::Type;
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MissingTypeIssue {
    IterableValue { word: &'static str },
    GenericArgs { name: String, templates: String },
    CallableSignature,
}

/// Analyze a resolved semantic type.
pub(crate) fn check_type(reflection: &ReflectionIndex, ty: &Type) -> Vec<MissingTypeIssue> {
    let mut out = Vec::new();
    if let Some(word) = type_iterable_word(ty) {
        out.push(MissingTypeIssue::IterableValue { word });
    }
    for (name, templates) in type_generic_args(reflection, ty) {
        out.push(MissingTypeIssue::GenericArgs { name, templates });
    }
    if type_callable_signature_missing(ty) {
        out.push(MissingTypeIssue::CallableSignature);
    }
    out
}

pub(crate) fn type_iterable_word(ty: &Type) -> Option<&'static str> {
    match ty {
        Type::Array(None) => Some("array"),
        Type::Iterable(None) => Some("iterable"),
        Type::Nullable(inner) | Type::List(inner) | Type::ClassString(Some(inner)) => {
            type_iterable_word(inner)
        }
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            type_iterable_word(&kv.0).or_else(|| type_iterable_word(&kv.1))
        }
        Type::Named { args, .. } => args.iter().find_map(type_iterable_word),
        Type::Callable(Some(sig)) => sig
            .params
            .iter()
            .find_map(type_iterable_word)
            .or_else(|| type_iterable_word(&sig.ret)),
        Type::Shape { fields, .. } => fields.iter().find_map(|f| type_iterable_word(&f.ty)),
        Type::Union(parts) | Type::Intersection(parts) => parts.iter().find_map(type_iterable_word),
        Type::Conditional {
            target, then, els, ..
        } => type_iterable_word(target)
            .or_else(|| type_iterable_word(then))
            .or_else(|| type_iterable_word(els)),
        _ => None,
    }
}

/// Collect every bare `array` / `iterable` word in a union-like native type.
/// Some rules intentionally emit one diagnostic per union arm.
pub(crate) fn type_iterable_words(ty: &Type) -> Vec<&'static str> {
    let mut out = Vec::new();
    collect_type_iterable_words(ty, &mut out);
    out
}

fn collect_type_iterable_words(ty: &Type, out: &mut Vec<&'static str>) {
    match ty {
        Type::Array(None) => out.push("array"),
        Type::Iterable(None) => out.push("iterable"),
        Type::Nullable(inner) => collect_type_iterable_words(inner, out),
        Type::Union(parts) | Type::Intersection(parts) => {
            for part in parts.iter() {
                collect_type_iterable_words(part, out);
            }
        }
        _ => {}
    }
}

pub(crate) fn type_generic_args(reflection: &ReflectionIndex, ty: &Type) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    collect_type_generic_args(reflection, ty, &mut seen, &mut out);
    out
}

/// Collect missing generic args for the native type shapes that currently emit
/// one property-hook diagnostic per union arm.
pub(crate) fn type_generic_args_in_union(
    reflection: &ReflectionIndex,
    ty: &Type,
) -> Vec<(String, String)> {
    let mut out = Vec::new();
    collect_type_generic_args_in_union(reflection, ty, &mut out);
    out
}

fn collect_type_generic_args_in_union(
    reflection: &ReflectionIndex,
    ty: &Type,
    out: &mut Vec<(String, String)>,
) {
    match ty {
        Type::Named { fqn, args } if args.is_empty() => {
            if let Some(class) = reflection.class(fqn) {
                if !class.templates.is_empty() {
                    out.push((display_fqn(&class.fqn), class.templates.join(", ")));
                }
            }
        }
        Type::Nullable(inner) => collect_type_generic_args_in_union(reflection, inner, out),
        Type::Union(parts) | Type::Intersection(parts) => {
            for part in parts.iter() {
                collect_type_generic_args_in_union(reflection, part, out);
            }
        }
        _ => {}
    }
}

fn collect_type_generic_args(
    reflection: &ReflectionIndex,
    ty: &Type,
    seen: &mut HashSet<String>,
    out: &mut Vec<(String, String)>,
) {
    match ty {
        Type::Named { fqn, args } => {
            if args.is_empty() {
                if let Some(class) = reflection.class(fqn) {
                    if !class.templates.is_empty()
                        && seen.insert(SymbolKey::class_like(fqn).into_string())
                    {
                        out.push((display_fqn(&class.fqn), class.templates.join(", ")));
                    }
                }
            }
            for arg in args {
                collect_type_generic_args(reflection, arg, seen, out);
            }
        }
        Type::Nullable(inner) | Type::List(inner) | Type::ClassString(Some(inner)) => {
            collect_type_generic_args(reflection, inner, seen, out)
        }
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            collect_type_generic_args(reflection, &kv.0, seen, out);
            collect_type_generic_args(reflection, &kv.1, seen, out);
        }
        Type::Callable(Some(sig)) => {
            for param in &sig.params {
                collect_type_generic_args(reflection, param, seen, out);
            }
            collect_type_generic_args(reflection, &sig.ret, seen, out);
        }
        Type::Shape { fields, .. } => {
            for field in fields {
                collect_type_generic_args(reflection, &field.ty, seen, out);
            }
        }
        Type::Union(parts) | Type::Intersection(parts) => {
            for part in parts.iter() {
                collect_type_generic_args(reflection, part, seen, out);
            }
        }
        Type::Conditional {
            target, then, els, ..
        } => {
            collect_type_generic_args(reflection, target, seen, out);
            collect_type_generic_args(reflection, then, seen, out);
            collect_type_generic_args(reflection, els, seen, out);
        }
        _ => {}
    }
}

pub(crate) fn type_callable_signature_missing(ty: &Type) -> bool {
    match ty {
        Type::Callable(None) => true,
        Type::Nullable(inner) | Type::List(inner) | Type::ClassString(Some(inner)) => {
            type_callable_signature_missing(inner)
        }
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            type_callable_signature_missing(&kv.0) || type_callable_signature_missing(&kv.1)
        }
        Type::Named { args, .. } => args.iter().any(type_callable_signature_missing),
        Type::Callable(Some(sig)) => {
            sig.params.iter().any(type_callable_signature_missing)
                || type_callable_signature_missing(&sig.ret)
        }
        Type::Shape { fields, .. } => fields
            .iter()
            .any(|f| type_callable_signature_missing(&f.ty)),
        Type::Union(parts) | Type::Intersection(parts) => {
            parts.iter().any(type_callable_signature_missing)
        }
        Type::Conditional {
            target, then, els, ..
        } => {
            type_callable_signature_missing(target)
                || type_callable_signature_missing(then)
                || type_callable_signature_missing(els)
        }
        _ => false,
    }
}

pub(crate) fn type_callable_signature_words(ty: &Type) -> Vec<&'static str> {
    let mut out = Vec::new();
    collect_type_callable_signature_words(ty, &mut out);
    out
}

fn collect_type_callable_signature_words(ty: &Type, out: &mut Vec<&'static str>) {
    match ty {
        Type::Callable(None) => out.push("callable"),
        Type::Nullable(inner) => collect_type_callable_signature_words(inner, out),
        Type::Union(parts) | Type::Intersection(parts) => {
            for part in parts.iter() {
                collect_type_callable_signature_words(part, out);
            }
        }
        _ => {}
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct DocGenericContext<'a> {
    pub reflection: &'a ReflectionIndex,
    pub scope: &'a Scope,
    pub class_fqn: Option<&'a str>,
    pub current_class_templates: &'a [String],
    pub excluded_templates: &'a [String],
    pub skip_traits: bool,
}

/// Analyze a PHPDoc syntactic type.
pub(crate) fn check_doc_type(ctx: DocGenericContext<'_>, ty: &DocType) -> Vec<MissingTypeIssue> {
    let mut out = Vec::new();
    if let Some(word) = doc_iterable_word(ty) {
        out.push(MissingTypeIssue::IterableValue { word });
    }
    for (name, templates) in doc_generic_args(ctx, ty) {
        out.push(MissingTypeIssue::GenericArgs { name, templates });
    }
    if doc_callable_signature_missing(ty) {
        out.push(MissingTypeIssue::CallableSignature);
    }
    out
}

pub(crate) fn doc_iterable_word(t: &DocType) -> Option<&'static str> {
    match t {
        DocType::Named(n) => match n.to_ascii_lowercase().as_str() {
            "array" | "non-empty-array" => Some("array"),
            "iterable" => Some("iterable"),
            _ => None,
        },
        DocType::Nullable(inner) | DocType::Array(inner) => doc_iterable_word(inner),
        DocType::Union(parts) | DocType::Intersection(parts) => {
            parts.iter().find_map(doc_iterable_word)
        }
        DocType::Generic { args, .. } => args.iter().find_map(doc_iterable_word),
        DocType::Shape { fields, .. } => fields.iter().find_map(|f| doc_iterable_word(&f.ty)),
        DocType::Callable { params, ret, .. } => params
            .iter()
            .find_map(doc_iterable_word)
            .or_else(|| ret.as_deref().and_then(doc_iterable_word)),
        DocType::Conditional {
            target, then, els, ..
        } => doc_iterable_word(target)
            .or_else(|| doc_iterable_word(then))
            .or_else(|| doc_iterable_word(els)),
        _ => None,
    }
}

pub(crate) fn doc_generic_args(ctx: DocGenericContext<'_>, t: &DocType) -> Vec<(String, String)> {
    let mut out = Vec::new();
    collect_doc_generic_args(ctx, t, &mut out);
    out
}

fn collect_doc_generic_args(
    ctx: DocGenericContext<'_>,
    t: &DocType,
    out: &mut Vec<(String, String)>,
) {
    match t {
        DocType::Named(n) => {
            if let Some(issue) = doc_generic_without_args(ctx, n) {
                out.push(issue);
            }
        }
        DocType::Generic { args, .. } => {
            for arg in args {
                collect_doc_generic_args(ctx, arg, out);
            }
        }
        DocType::Nullable(inner) | DocType::Array(inner) => {
            collect_doc_generic_args(ctx, inner, out)
        }
        DocType::Union(parts) | DocType::Intersection(parts) => {
            for p in parts.iter() {
                collect_doc_generic_args(ctx, p, out);
            }
        }
        DocType::Shape { fields, .. } => {
            for f in fields {
                collect_doc_generic_args(ctx, &f.ty, out);
            }
        }
        DocType::Callable { params, ret, .. } => {
            for p in params {
                collect_doc_generic_args(ctx, p, out);
            }
            if let Some(ret) = ret {
                collect_doc_generic_args(ctx, ret, out);
            }
        }
        DocType::Conditional {
            target, then, els, ..
        } => {
            for p in [target.as_ref(), then.as_ref(), els.as_ref()] {
                collect_doc_generic_args(ctx, p, out);
            }
        }
        _ => {}
    }
}

fn doc_generic_without_args(ctx: DocGenericContext<'_>, name: &str) -> Option<(String, String)> {
    if is_doc_keyword(name) || ctx.excluded_templates.iter().any(|t| t == name) {
        return None;
    }
    let fqn = match name.to_ascii_lowercase().as_str() {
        "self" | "static" | "$this" => ctx.class_fqn?.to_string(),
        _ => match ctx.scope.resolve_class(&name_from_doc(name)) {
            Resolution::Fqn(fqn) => fqn,
            Resolution::Fallback { namespaced, .. } => namespaced,
            _ => return None,
        },
    };
    let class_ref = ctx.reflection.class(&fqn)?;
    if ctx.skip_traits && class_ref.kind == php_ast::ClassKind::Trait {
        return None;
    }
    let templates = if ctx
        .class_fqn
        .is_some_and(|current| SymbolKey::same(php_resolve::SymbolKind::ClassLike, &fqn, current))
    {
        ctx.current_class_templates.to_vec()
    } else {
        class_ref.templates.clone()
    };
    if templates.is_empty() {
        return None;
    }
    Some((display_fqn(&class_ref.fqn), templates.join(", ")))
}

pub(crate) fn name_from_doc(text: &str) -> Name {
    let fq = if text.starts_with("namespace\\") {
        NameFq::Relative
    } else if text.starts_with('\\') {
        NameFq::Fq
    } else {
        NameFq::NotFq
    };
    Name {
        span: Span::new(0, 0),
        fq,
        text: text.to_string(),
    }
}

fn is_doc_keyword(name: &str) -> bool {
    matches!(
        name.to_ascii_lowercase().as_str(),
        "array"
            | "iterable"
            | "callable"
            | "int"
            | "integer"
            | "float"
            | "double"
            | "string"
            | "bool"
            | "boolean"
            | "void"
            | "never"
            | "mixed"
            | "object"
            | "resource"
            | "null"
            | "true"
            | "false"
            | "scalar"
            | "list"
            | "non-empty-array"
            | "non-empty-list"
            | "class-string"
    )
}

pub(crate) fn doc_callable_signature_missing(t: &DocType) -> bool {
    match t {
        DocType::Named(n) => matches!(n.to_ascii_lowercase().as_str(), "callable" | "closure"),
        DocType::Nullable(inner) | DocType::Array(inner) => doc_callable_signature_missing(inner),
        DocType::Union(parts) | DocType::Intersection(parts) => {
            parts.iter().any(doc_callable_signature_missing)
        }
        DocType::Generic { args, .. } => args.iter().any(doc_callable_signature_missing),
        DocType::Shape { fields, .. } => {
            fields.iter().any(|f| doc_callable_signature_missing(&f.ty))
        }
        DocType::Callable { params, ret, .. } => {
            params.iter().any(doc_callable_signature_missing)
                || ret.as_deref().is_some_and(doc_callable_signature_missing)
        }
        DocType::Conditional {
            target, then, els, ..
        } => {
            doc_callable_signature_missing(target)
                || doc_callable_signature_missing(then)
                || doc_callable_signature_missing(els)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_types::{CallableSig, Type};

    #[test]
    fn resolved_type_recurses_through_containers() {
        let ty = Type::List(Box::new(Type::Array(None)));
        assert_eq!(type_iterable_word(&ty), Some("array"));
        let ty = Type::Callable(Some(Box::new(CallableSig {
            params: vec![Type::String],
            ret: Type::Callable(None),
        })));
        assert!(type_callable_signature_missing(&ty));
    }

    #[test]
    fn doc_type_recurses_through_containers() {
        let ty = DocType::Generic {
            base: "list".into(),
            args: vec![DocType::Named("array".into())],
        };
        assert_eq!(doc_iterable_word(&ty), Some("array"));
        let ty = DocType::Nullable(Box::new(DocType::Named("callable".into())));
        assert!(doc_callable_signature_missing(&ty));
    }
}
