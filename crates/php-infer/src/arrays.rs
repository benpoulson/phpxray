//! Shared array/list/shape semantics.

use php_ast::{Expr, ExprKind};
use php_types::{ShapeField, Type};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ShapeOffsetStatus {
    Missing,
    Present(Type),
    Maybe,
}

impl ShapeOffsetStatus {
    pub fn without_type(self) -> ShapeOffsetPresence {
        match self {
            ShapeOffsetStatus::Missing => ShapeOffsetPresence::Missing,
            ShapeOffsetStatus::Present(_) => ShapeOffsetPresence::Present,
            ShapeOffsetStatus::Maybe => ShapeOffsetPresence::Maybe,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShapeOffsetPresence {
    Missing,
    Present,
    Maybe,
}

/// `Some(n)` iff `bytes` is the canonical base-10 representation of an integer
/// key. PHP coerces only canonical integer strings to int array keys.
pub fn canonical_int_string(bytes: &[u8]) -> Option<i64> {
    if bytes.is_empty() {
        return None;
    }
    let (neg, digits): (bool, &[u8]) = match bytes.first() {
        Some(b'-') => (true, &bytes[1..]),
        _ => (false, bytes),
    };
    if digits.is_empty() || !digits.iter().all(|b| b.is_ascii_digit()) {
        return None;
    }
    if digits.len() > 1 && digits[0] == b'0' {
        return None;
    }
    let s = std::str::from_utf8(bytes).ok()?;
    let n: i64 = s.parse().ok()?;
    if neg && n == 0 {
        return None;
    }
    Some(n)
}

pub fn shape_key_is_string(key: &str) -> bool {
    canonical_int_string(key.as_bytes()).is_none()
}

/// The key type of a shape field.
pub fn shape_field_key_type(f: &ShapeField) -> Type {
    match &f.key {
        Some(k) if !shape_key_is_string(k) => Type::Int,
        Some(_) => Type::String,
        None => Type::Int,
    }
}

/// The constant array-shape key spelled by a literal string or integer
/// expression. Non-literal keys yield `None`.
pub fn const_shape_key(expr: &Expr) -> Option<String> {
    match &expr.kind {
        ExprKind::Str(bytes) => Some(String::from_utf8_lossy(bytes).into_owned()),
        ExprKind::Int(n) => Some(n.to_string()),
        ExprKind::Paren(inner) => const_shape_key(inner),
        _ => None,
    }
}

pub fn shape_offset_status(base_ty: &Type, key: &str) -> Option<ShapeOffsetStatus> {
    match base_ty {
        Type::Shape { fields, sealed } => {
            match fields.iter().find(|f| f.key.as_deref() == Some(key)) {
                Some(field) if field.optional => Some(ShapeOffsetStatus::Maybe),
                Some(field) => Some(ShapeOffsetStatus::Present(field.ty.clone())),
                None if key.parse::<usize>().is_ok() && fields.iter().any(|f| f.key.is_none()) => {
                    Some(ShapeOffsetStatus::Maybe)
                }
                None if *sealed => Some(ShapeOffsetStatus::Missing),
                None => Some(ShapeOffsetStatus::Maybe),
            }
        }
        Type::Union(parts) if !parts.is_empty() => {
            let mut saw_missing = false;
            let mut present_types = Vec::new();
            for part in parts {
                match shape_offset_status(part, key)? {
                    ShapeOffsetStatus::Missing => saw_missing = true,
                    ShapeOffsetStatus::Present(ty) => present_types.push(ty),
                    ShapeOffsetStatus::Maybe => return Some(ShapeOffsetStatus::Maybe),
                }
            }
            if saw_missing && present_types.is_empty() {
                Some(ShapeOffsetStatus::Missing)
            } else if saw_missing {
                Some(ShapeOffsetStatus::Maybe)
            } else {
                Some(ShapeOffsetStatus::Present(Type::union(present_types)))
            }
        }
        _ => None,
    }
}

pub fn shape_offset_maybe_reportable(base_ty: &Type, key: &str) -> bool {
    match base_ty {
        Type::Shape { fields, .. } => {
            if let Some(field) = fields.iter().find(|f| f.key.as_deref() == Some(key)) {
                return field.optional;
            }
            if key.parse::<usize>().is_ok() && fields.iter().any(|f| f.key.is_none()) {
                return false;
            }
            false
        }
        Type::Union(parts) if !parts.is_empty() => {
            let mut present = false;
            let mut missing = false;
            for part in parts {
                match shape_offset_status(part, key).map(ShapeOffsetStatus::without_type) {
                    Some(ShapeOffsetPresence::Present) => present = true,
                    Some(ShapeOffsetPresence::Missing) => missing = true,
                    Some(ShapeOffsetPresence::Maybe) => return true,
                    None => return false,
                }
            }
            present && missing
        }
        _ => false,
    }
}

pub fn array_value_type(ty: &Type) -> Option<Type> {
    match ty {
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => Some(kv.1.clone()),
        Type::List(v) => Some((**v).clone()),
        Type::Shape { fields, sealed } => {
            let mut vals: Vec<Type> = fields.iter().map(|f| f.ty.clone()).collect();
            if !sealed {
                vals.push(Type::Mixed);
            }
            Some(Type::union(vals))
        }
        _ => None,
    }
}

pub fn array_key_type(ty: &Type) -> Option<Type> {
    match ty {
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => Some(kv.0.clone()),
        Type::List(_) => Some(Type::Int),
        Type::Shape { fields, .. } => Some(Type::union(
            fields.iter().map(shape_field_key_type).collect(),
        )),
        _ => None,
    }
}

pub fn iter_key_value(ty: &Type) -> (Type, Type) {
    match ty {
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => (kv.0.clone(), kv.1.clone()),
        Type::List(v) => (Type::Int, (**v).clone()),
        Type::Shape { .. } => (
            array_key_type(ty).unwrap_or(Type::Mixed),
            array_value_type(ty).unwrap_or(Type::Mixed),
        ),
        _ => (Type::Mixed, Type::Mixed),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_integer_strings_follow_php_array_key_rules() {
        assert_eq!(canonical_int_string(b"0"), Some(0));
        assert_eq!(canonical_int_string(b"-1"), Some(-1));
        assert_eq!(canonical_int_string(b"01"), None);
        assert_eq!(canonical_int_string(b"-0"), None);
        assert_eq!(canonical_int_string(b"+1"), None);
    }

    #[test]
    fn shape_offset_status_reports_presence_and_missing() {
        let shape = Type::Shape {
            fields: vec![ShapeField {
                key: Some("a".into()),
                optional: false,
                ty: Type::String,
            }],
            sealed: true,
        };
        assert_eq!(
            shape_offset_status(&shape, "a"),
            Some(ShapeOffsetStatus::Present(Type::String))
        );
        assert_eq!(
            shape_offset_status(&shape, "b"),
            Some(ShapeOffsetStatus::Missing)
        );
    }
}
