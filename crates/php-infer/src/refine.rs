//! Shared type refinements used by expression inference, flow, and assignability.

use php_types::Type;

/// Remove `null` from a type. A type that is purely `null` becomes `never`.
pub fn strip_null_strict(t: &Type) -> Type {
    match t {
        Type::Null => Type::Never,
        Type::Nullable(inner) => (**inner).clone(),
        Type::Union(parts) => Type::union(
            parts
                .iter()
                .filter(|p| **p != Type::Null)
                .cloned()
                .collect(),
        ),
        other => other.clone(),
    }
}

/// Remove `null` from a type for lenient compatibility checks. A type that is
/// purely `null` stays `null`.
pub fn strip_null_lenient(t: &Type) -> Type {
    match t {
        Type::Null => Type::Null,
        Type::Nullable(inner) => (**inner).clone(),
        Type::Union(parts) => {
            let kept: Vec<Type> = parts
                .iter()
                .filter(|p| !matches!(p, Type::Null))
                .cloned()
                .collect();
            if kept.is_empty() {
                Type::Null
            } else {
                Type::union(kept)
            }
        }
        other => other.clone(),
    }
}

/// Remove `false` from a type. `bool` narrows to `true`, and bare `false`
/// becomes `never`.
pub fn strip_false(t: &Type) -> Type {
    match t {
        Type::False => Type::Never,
        Type::Bool => Type::True,
        Type::Union(parts) => Type::union(
            parts
                .iter()
                .filter(|p| !matches!(p, Type::False))
                .map(strip_false)
                .collect(),
        ),
        Type::Nullable(inner) => Type::Nullable(Box::new(strip_false(inner))),
        other => other.clone(),
    }
}

/// Remove always-falsy members (`null`, `false`) from a type. `bool` narrows to
/// `true`.
pub fn strip_falsy(t: &Type) -> Type {
    match t {
        Type::Null | Type::False => Type::Never,
        Type::Bool => Type::True,
        Type::Nullable(inner) => strip_falsy(inner),
        Type::Union(parts) => Type::union(
            parts
                .iter()
                .filter(|p| !matches!(p, Type::Null | Type::False))
                .map(strip_falsy)
                .collect(),
        ),
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn truthy_refinement_recursively_narrows_bool_null() {
        let ty = Type::union(vec![Type::Bool, Type::Null]);
        assert_eq!(strip_falsy(&ty), Type::True);
    }

    #[test]
    fn strict_and_lenient_null_differ_for_bare_null() {
        assert_eq!(strip_null_strict(&Type::Null), Type::Never);
        assert_eq!(strip_null_lenient(&Type::Null), Type::Null);
    }
}
