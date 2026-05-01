//! The canonical *semantic* type vocabulary shared by reflection, the type
//! system, and the rules engine.
//!
//! The parser and PHPDoc layers produce *syntactic* types (`php_ast::Type`,
//! `php_phpdoc::DocType`) where class names are unresolved text. This crate is
//! the *resolved* form everything downstream reasons about: class names are
//! fully-qualified, keywords are distinct variants, and native + PHPDoc types
//! unify here. Construction (resolving names, merging native + doc) lives in
//! `php-reflect`; this crate is just the representation + rendering.

use std::fmt;

/// A resolved PHP type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// `mixed` — the top type.
    Mixed,
    /// `never` — the bottom type.
    Never,
    /// `void` (a return type).
    Void,
    Null,
    Bool,
    /// The literal `true` type.
    True,
    /// The literal `false` type.
    False,
    Int,
    Float,
    String,
    /// Bare `object`.
    Object,
    Resource,
    /// `array`; `None` = bare `array`, `Some((key, value))` = `array<K, V>`.
    Array(Option<Box<(Type, Type)>>),
    /// `iterable`; same shape as [`Type::Array`].
    Iterable(Option<Box<(Type, Type)>>),
    /// `list<T>`.
    List(Box<Type>),
    /// `callable`/`Closure`; `None` = bare, `Some` = a signature.
    Callable(Option<Box<CallableSig>>),
    /// `class-string` or `class-string<T>`.
    ClassString(Option<Box<Type>>),
    /// A class/interface/enum/trait, fully-qualified, with optional generic args.
    Named { fqn: String, args: Vec<Type> },
    /// `self` / `static` / `parent` — resolved against the class context later.
    SelfType,
    StaticType,
    Parent,
    /// A generic template variable (`T`).
    TemplateVar(String),
    /// A literal-int type (`42`).
    LiteralInt(i64),
    /// A literal-string type (`'draft'`).
    LiteralString(String),
    /// An array shape `array{id: int, name?: string}` (or unsealed `…, ...`).
    Shape { fields: Vec<ShapeField>, sealed: bool },
    /// `T|null` shorthand.
    Nullable(Box<Type>),
    Union(Vec<Type>),
    Intersection(Vec<Type>),
    /// A conditional type `($subject is [not] target ? then : else)`.
    Conditional {
        subject: String,
        negated: bool,
        target: Box<Type>,
        then: Box<Type>,
        els: Box<Type>,
    },
    /// A type we couldn't resolve or don't model; analysis treats it as `mixed`.
    Unknown(String),
}

/// A callable signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallableSig {
    pub params: Vec<Type>,
    pub ret: Type,
}

/// One field of an array/object shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShapeField {
    pub key: Option<String>,
    pub optional: bool,
    pub ty: Type,
}

impl Type {
    /// Wrap in nullability, flattening `?(?T)` and `?null`.
    pub fn nullable(self) -> Type {
        match self {
            Type::Null | Type::Nullable(_) => self,
            other => Type::Nullable(Box::new(other)),
        }
    }

    /// Build a union, flattening nested unions *and* `Nullable` members (`?T`
    /// becomes `T | null`) and dropping duplicates (order-preserving); a single
    /// member collapses to itself, an empty one to `never`. Decomposing nullable
    /// members keeps unions normalized so a contained `null` can be narrowed away
    /// (otherwise `string | ?string` hides its `null` from strip-null/falsy).
    pub fn union(parts: Vec<Type>) -> Type {
        let mut flat = Vec::new();
        for p in parts {
            collect_union_members(p, &mut flat);
        }
        dedup(&mut flat);
        absorb_literals(&mut flat);
        match flat.len() {
            0 => Type::Never,
            1 => flat.pop().unwrap(),
            _ => Type::Union(flat),
        }
    }

    /// Build an intersection, flattening + deduping; a single member collapses.
    pub fn intersection(parts: Vec<Type>) -> Type {
        let mut flat = Vec::new();
        for p in parts {
            match p {
                Type::Intersection(inner) => flat.extend(inner),
                other => flat.push(other),
            }
        }
        dedup(&mut flat);
        match flat.len() {
            1 => flat.pop().unwrap(),
            _ => Type::Intersection(flat),
        }
    }
}

/// Flatten a type into atomic union members: nested unions are spread, and a
/// `Nullable(X)` contributes `X`'s members plus `null`.
fn collect_union_members(t: Type, out: &mut Vec<Type>) {
    match t {
        Type::Union(inner) => inner.into_iter().for_each(|q| collect_union_members(q, out)),
        Type::Nullable(inner) => {
            collect_union_members(*inner, out);
            out.push(Type::Null);
        }
        other => out.push(other),
    }
}

/// Drop literal members already covered by their general type in the same union:
/// `int|5` → `int`, `string|'x'` → `string`, `bool|true` → `bool`. A union of
/// *only* literals (`1|2|3`, `'a'|'b'`) is kept — that's a precise type, not
/// redundant. Mirrors phpstan, and keeps diagnostic messages clean.
fn absorb_literals(types: &mut Vec<Type>) {
    let has_int = types.contains(&Type::Int);
    let has_string = types.contains(&Type::String);
    let has_bool = types.contains(&Type::Bool);
    types.retain(|t| match t {
        Type::LiteralInt(_) => !has_int,
        Type::LiteralString(_) => !has_string,
        Type::True | Type::False => !has_bool,
        _ => true,
    });
}

/// Remove duplicate types while preserving first-seen order (unlike
/// `Vec::dedup`, which only collapses *adjacent* duplicates).
fn dedup(types: &mut Vec<Type>) {
    let mut i = 0;
    while i < types.len() {
        if types[..i].contains(&types[i]) {
            types.remove(i);
        } else {
            i += 1;
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Mixed => f.write_str("mixed"),
            Type::Never => f.write_str("never"),
            Type::Void => f.write_str("void"),
            Type::Null => f.write_str("null"),
            Type::Bool => f.write_str("bool"),
            Type::True => f.write_str("true"),
            Type::False => f.write_str("false"),
            Type::Int => f.write_str("int"),
            Type::Float => f.write_str("float"),
            Type::String => f.write_str("string"),
            Type::Object => f.write_str("object"),
            Type::Resource => f.write_str("resource"),
            Type::Array(None) => f.write_str("array"),
            Type::Array(Some(kv)) => write!(f, "array<{}, {}>", kv.0, kv.1),
            Type::Iterable(None) => f.write_str("iterable"),
            Type::Iterable(Some(kv)) => write!(f, "iterable<{}, {}>", kv.0, kv.1),
            Type::List(t) => write!(f, "list<{t}>"),
            Type::Callable(None) => f.write_str("callable"),
            Type::Callable(Some(sig)) => {
                let params = sig.params.iter().map(|p| p.to_string()).collect::<Vec<_>>().join(", ");
                write!(f, "callable({params}): {}", sig.ret)
            }
            Type::ClassString(None) => f.write_str("class-string"),
            Type::ClassString(Some(t)) => write!(f, "class-string<{t}>"),
            Type::Named { fqn, args } if args.is_empty() => f.write_str(fqn),
            Type::Named { fqn, args } => {
                let a = args.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ");
                write!(f, "{fqn}<{a}>")
            }
            Type::SelfType => f.write_str("self"),
            Type::StaticType => f.write_str("static"),
            Type::Parent => f.write_str("parent"),
            Type::TemplateVar(n) => f.write_str(n),
            Type::LiteralInt(n) => write!(f, "{n}"),
            Type::LiteralString(s) => write!(f, "'{s}'"),
            Type::Shape { fields, sealed } => {
                f.write_str("array{")?;
                for (i, fld) in fields.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    if let Some(k) = &fld.key {
                        write!(f, "{k}{}: ", if fld.optional { "?" } else { "" })?;
                    }
                    write!(f, "{}", fld.ty)?;
                }
                if !sealed {
                    f.write_str(if fields.is_empty() { "..." } else { ", ..." })?;
                }
                f.write_str("}")
            }
            Type::Nullable(t) => write!(f, "?{t}"),
            Type::Union(parts) => {
                let s = parts.iter().map(|p| p.to_string()).collect::<Vec<_>>().join("|");
                f.write_str(&s)
            }
            Type::Intersection(parts) => {
                let s = parts.iter().map(|p| p.to_string()).collect::<Vec<_>>().join("&");
                f.write_str(&s)
            }
            Type::Conditional { subject, negated, target, then, els } => {
                let not = if *negated { "not " } else { "" };
                write!(f, "({subject} is {not}{target} ? {then} : {els})")
            }
            Type::Unknown(s) => write!(f, "mixed/*{s}*/"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_scalars_and_named() {
        assert_eq!(Type::Int.to_string(), "int");
        assert_eq!(Type::Named { fqn: "App\\User".into(), args: vec![] }.to_string(), "App\\User");
        assert_eq!(Type::Array(None).to_string(), "array");
        assert_eq!(
            Type::Array(Some(Box::new((Type::String, Type::Int)))).to_string(),
            "array<string, int>"
        );
        assert_eq!(Type::List(Box::new(Type::Int)).to_string(), "list<int>");
    }

    #[test]
    fn display_composite() {
        assert_eq!(Type::Nullable(Box::new(Type::Int)).to_string(), "?int");
        assert_eq!(Type::Union(vec![Type::Int, Type::String]).to_string(), "int|string");
        assert_eq!(
            Type::Named { fqn: "Collection".into(), args: vec![Type::Int, Type::Named { fqn: "User".into(), args: vec![] }] }.to_string(),
            "Collection<int, User>"
        );
    }

    #[test]
    fn smart_constructors_flatten_and_dedup() {
        assert_eq!(Type::union(vec![Type::Int]), Type::Int);
        assert_eq!(
            Type::union(vec![Type::Int, Type::Union(vec![Type::String, Type::Int])]),
            Type::Union(vec![Type::Int, Type::String])
        );
        assert_eq!(Type::Int.nullable().nullable(), Type::Nullable(Box::new(Type::Int)));
        assert_eq!(Type::Null.nullable(), Type::Null);
    }
}
