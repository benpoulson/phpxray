//! Typed built-in signatures loaded from the shared generated manifests in
//! `php-types`.
//!
//! Each line is `fqn<TAB>return<TAB>p1;p2;…` where a param is `name#type#flags`
//! (flags ⊆ `r`=by-ref `v`=variadic `o`=optional; empty type ⇒ `mixed`). Types
//! are `php_types::Type` Display, re-parsed here via the PHPDoc type grammar so
//! the manifest stays human-readable and we reuse one type parser. Parsing is
//! lenient — an unrecognised type string falls back to `mixed`.

use crate::{
    resolve_doc_type, AttributeSpec, ClassReflection, ConstReflection, FunctionReflection,
    MethodReflection, ParamReflection, PropertyReflection,
};
use php_ast::{ClassKind, Visibility};
use php_resolve::Scope;
use php_types::{
    builtins::{self, BuiltinClassRecord, BuiltinParam},
    PhpVersion, Type,
};

/// Parse the committed manifest into function reflections for `version`.
pub(crate) fn builtin_functions_for(version: PhpVersion) -> Vec<FunctionReflection> {
    let scope = Scope::global();
    builtins::functions_for(version)
        .into_iter()
        .map(|f| FunctionReflection {
            fqn: f.fqn.to_string(),
            params: f
                .params
                .into_iter()
                .map(|p| reflected_param(p, &scope))
                .collect(),
            return_type: deser_type(f.return_type, &scope),
            native_return: deser_type(f.return_type, &scope),
            by_ref: false,
            templates: Vec::new(),
            deprecated: false,
            // Built-in purity is curated separately (rules' PURE_BUILTINS); the
            // stub manifest carries no purity info.
            pure: false,
            must_use_return_value: false,
            builtin: true,
        })
        .collect()
}

/// Parse the committed built-in class-member manifest for `version`.
pub(crate) fn builtin_classes_for(version: PhpVersion) -> Vec<ClassReflection> {
    let scope = Scope::global();
    let mut classes = Vec::<ClassReflection>::new();
    for record in builtins::class_records_for(version) {
        match record {
            BuiltinClassRecord::Class {
                kind,
                fqn,
                parents,
                interfaces,
                traits,
                flags,
            } => {
                if fqn.is_empty() {
                    continue;
                }
                classes.push(ClassReflection {
                    fqn: fqn.to_string(),
                    kind: parse_kind(kind),
                    is_abstract: flags.contains('a'),
                    is_final: flags.contains('f'),
                    is_readonly: flags.contains('r'),
                    parents: named_types(parents),
                    interfaces: named_types(interfaces),
                    traits: named_types(traits),
                    templates: Vec::new(),
                    methods: Vec::new(),
                    properties: Vec::new(),
                    constants: Vec::new(),
                    mixins: Vec::new(),
                    deprecated: false,
                    attribute: builtin_attribute(flags),
                    consistent_constructor: false,
                    builtin: true,
                });
            }
            BuiltinClassRecord::Method {
                class,
                name,
                visibility,
                flags,
                return_type,
                native_return,
                params,
            } => {
                let Some(cr) = ensure_class(&mut classes, class) else {
                    continue;
                };
                cr.methods.push(MethodReflection {
                    name: name.to_string(),
                    visibility: parse_visibility(visibility),
                    is_static: flags.contains('s'),
                    is_abstract: flags.contains('a'),
                    is_final: flags.contains('f'),
                    params: params
                        .into_iter()
                        .map(|p| reflected_param(p, &scope))
                        .collect(),
                    return_type: deser_type(return_type, &scope),
                    explicit_return: true,
                    native_return: deser_type(native_return, &scope),
                    templates: Vec::new(),
                    deprecated: false,
                    pure: flags.contains('p'),
                    must_use_return_value: flags.contains('u'),
                    magic: false,
                });
            }
            BuiltinClassRecord::Property {
                class,
                name,
                visibility,
                flags,
                ty,
                native_ty,
            } => {
                let Some(cr) = ensure_class(&mut classes, class) else {
                    continue;
                };
                cr.properties.push(PropertyReflection {
                    name: name.to_string(),
                    visibility: parse_visibility(visibility),
                    is_static: flags.contains('s'),
                    is_readonly: flags.contains('r'),
                    ty: deser_type(ty, &scope),
                    native_ty: deser_type(native_ty, &scope),
                    has_default: false,
                    access: php_phpdoc::PropertyAccess::ReadWrite,
                    magic: false,
                });
            }
            BuiltinClassRecord::Constant {
                class,
                name,
                visibility,
                flags,
                ty,
                int_value,
            } => {
                let Some(cr) = ensure_class(&mut classes, class) else {
                    continue;
                };
                cr.constants.push(ConstReflection {
                    name: name.to_string(),
                    visibility: parse_visibility(visibility),
                    ty: deser_type(ty, &scope),
                    is_final: flags.contains('f'),
                    int_value,
                });
            }
        }
    }
    classes
}

fn reflected_param(p: BuiltinParam<'_>, scope: &Scope) -> ParamReflection {
    let ty = deser_type(p.ty, scope);
    ParamReflection {
        name: p.name.to_string(),
        native_ty: ty.clone(),
        ty,
        by_ref: p.flags.contains('r'),
        variadic: p.flags.contains('v'),
        optional: p.flags.contains('o'),
        promoted: false,
        explicit: true,
    }
}

fn deser_type(s: &str, scope: &Scope) -> Type {
    if s.is_empty() {
        return Type::Mixed;
    }
    match php_phpdoc::parse_type(s) {
        Some(dt) => resolve_doc_type(scope, &[], &dt),
        None => Type::Mixed,
    }
}

fn parse_kind(kind: builtins::BuiltinClassKind) -> ClassKind {
    match kind {
        builtins::BuiltinClassKind::Class => ClassKind::Class,
        builtins::BuiltinClassKind::Interface => ClassKind::Interface,
        builtins::BuiltinClassKind::Trait => ClassKind::Trait,
        builtins::BuiltinClassKind::Enum => ClassKind::Enum,
    }
}

fn parse_visibility(s: &str) -> Visibility {
    match s {
        "private" => Visibility::Private,
        "protected" => Visibility::Protected,
        _ => Visibility::Public,
    }
}

fn named_types(names: Vec<&str>) -> Vec<Type> {
    names
        .into_iter()
        .map(|fqn| Type::Named {
            fqn: fqn.to_string(),
            args: Vec::new(),
        })
        .collect()
}

fn ensure_class<'a>(
    classes: &'a mut Vec<ClassReflection>,
    fqn: &str,
) -> Option<&'a mut ClassReflection> {
    if fqn.is_empty() {
        return None;
    }
    if let Some(idx) = classes.iter().position(|c| c.fqn.eq_ignore_ascii_case(fqn)) {
        return classes.get_mut(idx);
    }
    classes.push(ClassReflection {
        fqn: fqn.to_string(),
        kind: ClassKind::Class,
        is_abstract: false,
        is_final: false,
        is_readonly: false,
        parents: Vec::new(),
        interfaces: Vec::new(),
        traits: Vec::new(),
        templates: Vec::new(),
        methods: Vec::new(),
        properties: Vec::new(),
        constants: Vec::<ConstReflection>::new(),
        mixins: Vec::new(),
        deprecated: false,
        attribute: None,
        consistent_constructor: false,
        builtin: true,
    });
    classes.last_mut()
}

fn builtin_attribute(flags: &str) -> Option<AttributeSpec> {
    if flags.contains('A') {
        Some(AttributeSpec {
            targets: crate::attr_target::ALL,
            repeatable: false,
        })
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn loads_and_resolves_common_signatures() {
        let fns = builtin_functions_for(PhpVersion::default());
        assert!(
            fns.len() > 4000,
            "expected thousands of builtins, got {}",
            fns.len()
        );

        let strlen = fns
            .iter()
            .find(|f| f.fqn.eq_ignore_ascii_case("strlen"))
            .unwrap();
        assert_eq!(strlen.return_type, Type::Int);
        assert_eq!(strlen.params.len(), 1);
        assert_eq!(strlen.params[0].ty, Type::String);

        let count = fns
            .iter()
            .find(|f| f.fqn.eq_ignore_ascii_case("count"))
            .unwrap();
        assert_eq!(count.return_type, Type::Int);
        // mode param is optional.
        assert!(count.params.last().unwrap().optional);
    }

    #[test]
    fn loads_common_builtin_class_members() {
        let classes = builtin_classes_for(PhpVersion::default());
        let date = classes
            .iter()
            .find(|c| c.fqn.eq_ignore_ascii_case("DateTimeImmutable"))
            .unwrap();
        assert!(date.interfaces.iter().any(|t| {
            matches!(t, Type::Named { fqn, .. } if fqn.eq_ignore_ascii_case("DateTimeInterface"))
        }));
        assert!(date
            .methods
            .iter()
            .any(|m| m.name.eq_ignore_ascii_case("format") && m.return_type == Type::String));

        let zone = classes
            .iter()
            .find(|c| c.fqn.eq_ignore_ascii_case("DateTimeZone"))
            .unwrap();
        assert!(zone
            .methods
            .iter()
            .any(|m| m.name.eq_ignore_ascii_case("getName") && m.return_type == Type::String));
    }
}
