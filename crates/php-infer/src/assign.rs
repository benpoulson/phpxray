//! M-T6: the **type assignability (subtype) relation** — "can a value of type
//! `value` be used where `target` is expected?".
//!
//! This is the core relation the rules engine checks (argument passing, returns,
//! property writes). It deliberately errs toward **leniency**: when we can't be
//! sure (a `mixed`/`Unknown` operand, an unindexed class), it answers `true`, so
//! a first-cut linter under-reports rather than emitting false positives. It only
//! answers `false` when both types are concrete and known to be incompatible
//! (e.g. `string` where `int` is wanted, or two unrelated *known* classes).

use php_reflect::ReflectionIndex;
use php_types::Type;

/// Whether a value of type `value` is assignable to a slot of type `target`.
pub fn is_assignable(index: &ReflectionIndex, value: &Type, target: &Type) -> bool {
    use Type::*;

    // Leniency escapes: top/bottom and anything we couldn't resolve.
    match (value, target) {
        (_, Mixed) => return true,           // everything fits mixed
        (Never, _) => return true,           // never is the bottom type
        (Mixed, _) => return true,           // unknown value — don't flag
        (Unknown(_), _) | (_, Unknown(_)) => return true,
        _ => {}
    }
    if value == target {
        return true;
    }

    // A union value is assignable only if *every* member is.
    if let Union(parts) = value {
        return parts.iter().all(|p| is_assignable(index, p, target));
    }
    // `?A` (value) ⊑ target iff both `A` and `null` are.
    if let Nullable(v) = value {
        return is_assignable(index, v, target) && is_assignable(index, &Null, target);
    }

    // A union/nullable target accepts the value if *any* arm does.
    match target {
        Nullable(t) => return matches!(value, Null) || is_assignable(index, value, t),
        Union(parts) => return parts.iter().any(|t| is_assignable(index, value, t)),
        _ => {}
    }

    assignable_atom(index, value, target)
}

/// Atomic (non-union, non-nullable) assignability: scalar widening, array/iterable
/// covariance, and class subtyping.
fn assignable_atom(index: &ReflectionIndex, value: &Type, target: &Type) -> bool {
    use Type::*;
    match (value, target) {
        // self/static/parent are unbound here — be lenient either way.
        (SelfType | StaticType | Parent, _) | (_, SelfType | StaticType | Parent) => true,

        // --- scalars (with PHP's int → float widening) ---
        (Int | LiteralInt(_), Int | Float) => true,
        (Float, Float) => true,
        (Bool | True | False, Bool) => true,
        (True, True) | (False, False) => true,
        (LiteralInt(a), LiteralInt(b)) => a == b,
        (String | LiteralString(_) | ClassString(_), String) => true,
        (LiteralString(a), LiteralString(b)) => a == b,
        (ClassString(_), ClassString(_)) => true,
        (Null, Null) => true,

        // --- arrays / iterables (covariant; lenient on bare forms) ---
        (Array(_) | List(_) | Shape { .. }, Array(None)) => true,
        (Array(Some(a)), Array(Some(b))) => {
            is_assignable(index, &a.0, &b.0) && is_assignable(index, &a.1, &b.1)
        }
        (List(v), Array(Some(b))) => is_assignable(index, &Int, &b.0) && is_assignable(index, v, &b.1),
        (List(a), List(b)) => is_assignable(index, a, b),
        (Shape { .. }, Array(Some(_))) => true,
        (Array(_) | List(_) | Iterable(_) | Shape { .. }, Iterable(None)) => true,
        (Iterable(Some(a)), Iterable(Some(b))) => {
            is_assignable(index, &a.0, &b.0) && is_assignable(index, &a.1, &b.1)
        }
        // An object may be Traversable; we can't see builtins, so stay lenient.
        (Named { .. }, Iterable(_)) => true,

        // --- objects / classes ---
        (Named { fqn: a, .. }, Named { fqn: b, .. }) => {
            // Only a confident negative when *both* classes are indexed; an
            // unindexed class (e.g. a built-in) is assumed compatible.
            if index.class(a).is_none() || index.class(b).is_none() {
                true
            } else {
                index.is_subclass_of(a, b)
            }
        }
        (Named { .. } | Object, Object) => true,
        // Closures and (leniently) any object can be callable.
        (Callable(_) | Named { .. }, Callable(_)) => true,

        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn empty_index() -> ReflectionIndex {
        ReflectionIndex::new()
    }

    /// Build an index from `src` (so class hierarchies are known).
    fn index_of(src: &str) -> (ReflectionIndex, php_intern::Interner) {
        let full = format!("<?php {src}");
        let r = php_parser::parse(&full);
        assert!(!r.has_errors(), "parse errors");
        let mut idx = ReflectionIndex::new();
        idx.add_file(&r.program, &r.interner);
        (idx, r.interner)
    }

    fn ok(v: Type, t: Type) -> bool {
        is_assignable(&empty_index(), &v, &t)
    }

    fn named(s: &str) -> Type {
        Type::Named { fqn: s.into(), args: vec![] }
    }

    #[test]
    fn identity_and_top_bottom() {
        assert!(ok(Type::Int, Type::Int));
        assert!(ok(Type::Int, Type::Mixed));
        assert!(ok(Type::Never, Type::Int));
        assert!(ok(Type::Mixed, Type::Int)); // lenient
    }

    #[test]
    fn scalar_widening() {
        assert!(ok(Type::Int, Type::Float)); // int -> float
        assert!(!ok(Type::Float, Type::Int)); // float -/> int
        assert!(!ok(Type::String, Type::Int));
        assert!(!ok(Type::Bool, Type::Int));
        assert!(ok(Type::True, Type::Bool));
        assert!(!ok(Type::Int, Type::String));
    }

    #[test]
    fn nullable_and_union_targets() {
        assert!(ok(Type::Int, Type::Nullable(Box::new(Type::Int))));
        assert!(ok(Type::Null, Type::Nullable(Box::new(Type::Int))));
        assert!(!ok(Type::String, Type::Nullable(Box::new(Type::Int))));
        let int_or_str = Type::Union(vec![Type::Int, Type::String]);
        assert!(ok(Type::Int, int_or_str.clone()));
        assert!(ok(Type::String, int_or_str.clone()));
        assert!(!ok(Type::Float, int_or_str));
    }

    #[test]
    fn union_value_needs_all_members() {
        let v = Type::Union(vec![Type::Int, Type::String]);
        assert!(!ok(v.clone(), Type::Int)); // string member fails
        assert!(ok(v.clone(), Type::Union(vec![Type::Int, Type::String])));
        assert!(ok(v, Type::Mixed));
    }

    #[test]
    fn nullable_value() {
        let v = Type::Nullable(Box::new(Type::Int));
        assert!(!ok(v.clone(), Type::Int)); // null doesn't fit int
        assert!(ok(v, Type::Nullable(Box::new(Type::Int))));
    }

    #[test]
    fn arrays_are_covariant_and_lenient_on_bare() {
        let ai = Type::Array(Some(Box::new((Type::Int, Type::Int))));
        assert!(ok(ai.clone(), Type::Array(None)));
        assert!(ok(ai.clone(), Type::Array(Some(Box::new((Type::Int, Type::Float)))))); // int->float value
        assert!(!ok(ai, Type::Array(Some(Box::new((Type::Int, Type::String))))));
        assert!(ok(Type::List(Box::new(Type::Int)), Type::Array(None)));
    }

    #[test]
    fn class_subtyping_uses_the_index() {
        let (idx, _) = index_of("class Base {} class User extends Base {} interface I {} class Impl implements I {}");
        assert!(is_assignable(&idx, &named("User"), &named("Base")));
        assert!(!is_assignable(&idx, &named("Base"), &named("User"))); // downcast
        assert!(is_assignable(&idx, &named("Impl"), &named("I")));
        assert!(is_assignable(&idx, &named("User"), &named("User")));
    }

    #[test]
    fn unknown_classes_are_lenient() {
        // Neither class is indexed (e.g. built-ins) -> assume compatible.
        assert!(ok(named("Exception"), named("Throwable")));
        assert!(ok(named("App\\Foo"), named("App\\Bar")));
    }

    #[test]
    fn objects_and_callables() {
        assert!(ok(named("Anything"), Type::Object));
        assert!(ok(Type::Named { fqn: "Closure".into(), args: vec![] }, Type::Callable(None)));
        assert!(!ok(Type::Int, Type::Object));
    }
}
