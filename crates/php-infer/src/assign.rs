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
use php_types::{ShapeField, Type};

/// The key type of a shape field: an integer-valued literal key is `int`,
/// otherwise `string` (a positional field, no key, is treated as `int`).
fn shape_key_type(f: &ShapeField) -> Type {
    match &f.key {
        Some(k) if k.parse::<i64>().is_ok() => Type::Int,
        Some(_) => Type::String,
        None => Type::Int,
    }
}

/// Whether every value of `ty` can be coerced to a string — PHP's `(string)` /
/// string-interpolation / `implode` element rules. Lenient like [`is_assignable`]:
/// scalars/`null`/`mixed`/templates and any object with `__toString` (or an
/// *unknown* class) are castable; only arrays, iterables, shapes, callables, and
/// `void` are definitely not. Used by the castable-to-string argument rules.
pub fn is_castable_to_string(index: &ReflectionIndex, ty: &Type) -> bool {
    use Type::*;
    match ty {
        Array(_) | List(_) | Iterable(_) | Shape { .. } | Callable(_) | Void => false,
        Nullable(inner) => is_castable_to_string(index, inner),
        Union(parts) => parts.iter().all(|p| is_castable_to_string(index, p)),
        // An object is castable iff it declares `__toString` (Stringable); be
        // lenient when the class isn't indexed (built-in / unknown).
        Named { fqn, .. } => index.find_method(fqn, "__toString").is_some() || index.class(fqn).is_none(),
        // scalars, `null`, `mixed`, `object`, `self`/`static`, templates, literals.
        _ => true,
    }
}

/// Strip the **PHPDoc-only** refinements from a type, leaving its *native* PHP
/// shape. In PHP the only native container type is bare `array`/`object`; every
/// element type (`array<Arg>`, `Arg[]`, `list<T>`, `array{…}`), generic argument
/// (`Collection<User>`), `class-string<T>`, and literal (`'draft'`, `42`) is
/// expressible *only* in PHPDoc. So this models "what the type would be if PHPDoc
/// were ignored" — used to honour `treatPhpDocTypesAsCertain`. Native nullability
/// is preserved (it can be a real `?T` hint).
pub fn native_shape(t: &Type) -> Type {
    use Type::*;
    match t {
        Array(_) | List(_) | Shape { .. } => Array(None),
        Iterable(_) => Iterable(None),
        ClassString(_) => ClassString(None),
        LiteralInt(_) | IntRange { .. } => Int,
        LiteralString(_) => String,
        Named { fqn, .. } => Named { fqn: fqn.clone(), args: Vec::new() },
        Nullable(inner) => Type::nullable(native_shape(inner)),
        Union(parts) => Type::union(parts.iter().map(native_shape).collect()),
        Intersection(parts) => Type::intersection(parts.iter().map(native_shape).collect()),
        other => other.clone(),
    }
}

/// Assignability honouring phpstan's `treatPhpDocTypesAsCertain`. When
/// `treat_phpdoc_certain` is `false`, an incompatibility that only appears at the
/// PHPDoc-refined level — an array *element* type, a generic argument, a literal —
/// is treated as uncertain and accepted (the native shapes are compatible). A
/// genuinely native mismatch (`string` where `array` is wanted) is still rejected.
pub fn assignable_certain(
    index: &ReflectionIndex,
    value: &Type,
    target: &Type,
    treat_phpdoc_certain: bool,
) -> bool {
    is_assignable(index, value, target)
        || (!treat_phpdoc_certain
            && is_assignable(index, &native_shape(value), &native_shape(target)))
}

/// Lower-bound `≥`: is value-bound `a` at least target-bound `b`? `None` target
/// bound is -∞ (any `a` qualifies); `None` value bound is -∞ (qualifies only if
/// `b` is also -∞).
fn ge_bound(a: Option<i64>, b: Option<i64>) -> bool {
    match (a, b) {
        (_, None) => true,
        (Some(a), Some(b)) => a >= b,
        (None, Some(_)) => false,
    }
}

/// Upper-bound `≤`: is value-bound `a` at most target-bound `b`? `None` target is +∞.
fn le_bound(a: Option<i64>, b: Option<i64>) -> bool {
    match (a, b) {
        (_, None) => true,
        (Some(a), Some(b)) => a <= b,
        (None, Some(_)) => false,
    }
}

/// Whether a value of type `value` is assignable to a slot of type `target`.
pub fn is_assignable(index: &ReflectionIndex, value: &Type, target: &Type) -> bool {
    use Type::*;

    // Leniency escapes: top/bottom and anything we couldn't resolve.
    match (value, target) {
        (_, Mixed) => return true,           // everything fits mixed
        (Never, _) => return true,           // never is the bottom type
        (Mixed, _) => return true,           // unknown value — don't flag
        (Unknown(_), _) | (_, Unknown(_)) => return true,
        // A template variable's concrete type is unknown (bounded by its
        // `@template T of …`, which we don't track) — stay lenient either way.
        (TemplateVar(_), _) | (_, TemplateVar(_)) => return true,
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
        (Int | LiteralInt(_) | IntRange { .. }, Int | Float) => true,
        // An int-range fits a target range iff it's fully contained; a literal fits
        // iff in bounds. (`min`/`max` `None` are -inf/+inf.)
        (IntRange { min: a0, max: a1 }, IntRange { min: b0, max: b1 }) => {
            ge_bound(*a0, *b0) && le_bound(*a1, *b1)
        }
        (LiteralInt(n), IntRange { min, max }) => {
            min.is_none_or(|lo| *n >= lo) && max.is_none_or(|hi| *n <= hi)
        }
        (Float, Float) => true,
        (Bool | True | False, Bool) => true,
        (True, True) | (False, False) => true,
        (LiteralInt(a), LiteralInt(b)) => a == b,
        (String | LiteralString(_) | ClassString(_), String) => true,
        (LiteralString(a), LiteralString(b)) => a == b,
        // A plain string may hold a class name — lenient toward `class-string`
        // (phpstan allows `string`/literal → `class-string`, e.g. a name built by
        // concatenation returned where `class-string` is declared).
        (String | LiteralString(_) | ClassString(_), ClassString(_)) => true,
        (Null, Null) => true,

        // --- arrays / iterables (covariant; lenient on bare forms) ---
        (Array(_) | List(_) | Shape { .. }, Array(None)) => true,
        // A bare `array` value (no element info — e.g. `[]` or an untyped array)
        // carries nothing to disprove against, so accept any array-shaped target
        // leniently (phpstan treats `[]` as assignable to every array type).
        (Array(None), Array(_) | List(_) | Iterable(_) | Shape { .. }) => true,
        (Array(Some(a)), Array(Some(b))) => {
            is_assignable(index, &a.0, &b.0) && is_assignable(index, &a.1, &b.1)
        }
        (List(v), Array(Some(b))) => is_assignable(index, &Int, &b.0) && is_assignable(index, v, &b.1),
        (List(a), List(b)) => is_assignable(index, a, b),
        // An int-keyed array may be a list — lenient (only the value type matters).
        (Array(Some(a)), List(b)) => is_assignable(index, &a.1, b),

        // --- array shapes ---
        // shape ⊑ shape: every field the target *requires* must be present and
        // assignable; a target-optional field is checked only when the value
        // supplies it. Extra value fields are tolerated (lenient — avoids false
        // positives against sealed targets, where phpstan would be stricter).
        (Shape { fields: av, .. }, Shape { fields: bv, .. }) => bv.iter().all(|bf| {
            match av.iter().find(|af| af.key == bf.key) {
                Some(af) => is_assignable(index, &af.ty, &bf.ty),
                None => bf.optional,
            }
        }),
        // shape ⊑ array<K,V>: each field's key and value must fit the element types.
        (Shape { fields, .. }, Array(Some(kv))) => fields.iter().all(|f| {
            is_assignable(index, &shape_key_type(f), &kv.0) && is_assignable(index, &f.ty, &kv.1)
        }),
        // shape ⊑ list<V>: lenient on key/order, check the value types.
        (Shape { fields, .. }, List(v)) => fields.iter().all(|f| is_assignable(index, &f.ty, v)),
        // A coarse array (no per-field info) ⊑ shape: can't disprove → lenient.
        (Array(_) | List(_), Shape { .. }) => true,
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
        // A callable may be a Closure, an object (`__invoke`), a function-name
        // string, or an `[$obj, 'method']` array — all accepted leniently (PHP's
        // `callable` is structural; rejecting a `string`/`array` would false-flag
        // `array_map('trim', …)` and `[$this, 'm']`).
        (Callable(_) | Named { .. } | Object | String | LiteralString(_) | Array(_) | List(_), Callable(_)) => true,

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
    fn string_and_array_are_callable() {
        assert!(ok(Type::String, Type::Callable(None)));
        assert!(ok(Type::Array(None), Type::Callable(None)));
        assert!(ok(Type::List(Box::new(Type::Mixed)), Type::Callable(None)));
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

    fn field(key: &str, optional: bool, ty: Type) -> ShapeField {
        ShapeField { key: Some(key.into()), optional, ty }
    }
    fn shape(fields: Vec<ShapeField>) -> Type {
        Type::Shape { fields, sealed: true }
    }

    #[test]
    fn shape_assignability() {
        // shape ⊑ shape: required field present & assignable.
        let v = shape(vec![field("id", false, Type::Int), field("name", false, Type::String)]);
        let t = shape(vec![field("id", false, Type::Int)]);
        assert!(ok(v.clone(), t)); // extra value field tolerated
        // a wrong field type is rejected (capability preserved).
        let bad = shape(vec![field("id", false, Type::String)]);
        assert!(!ok(v.clone(), bad));
        // a missing *required* target field is rejected; optional is fine.
        let needs_extra = shape(vec![field("id", false, Type::Int), field("x", false, Type::Bool)]);
        assert!(!ok(v.clone(), needs_extra));
        let opt_extra = shape(vec![field("id", false, Type::Int), field("x", true, Type::Bool)]);
        assert!(ok(v.clone(), opt_extra));
        // shape ⊑ array<string, int|string>.
        assert!(ok(v.clone(), Type::Array(Some(Box::new((Type::String, Type::union(vec![Type::Int, Type::String])))))));
        // a coarse array ⊑ shape is lenient (can't disprove).
        assert!(ok(Type::Array(None), shape(vec![field("id", false, Type::Int)])));
        assert!(ok(Type::Array(Some(Box::new((Type::String, Type::Mixed)))), shape(vec![field("id", false, Type::Int)])));
    }

    #[test]
    fn phpdoc_uncertain_suppresses_element_mismatch() {
        let idx = empty_index();
        let str_arr = Type::Array(Some(Box::new((Type::Int, Type::String))));
        let int_arr = Type::Array(Some(Box::new((Type::Int, Type::Int))));
        // With phpdoc certain (default), the element mismatch is a real error.
        assert!(!is_assignable(&idx, &str_arr, &int_arr));
        assert!(!assignable_certain(&idx, &str_arr, &int_arr, true));
        // With phpdoc *uncertain*, both are native `array` → accepted.
        assert!(assignable_certain(&idx, &str_arr, &int_arr, false));
        // A genuinely native mismatch is still rejected even when uncertain.
        assert!(!assignable_certain(&idx, &Type::String, &int_arr, false));
    }

    #[test]
    fn native_shape_erases_phpdoc_refinements() {
        assert_eq!(native_shape(&Type::List(Box::new(Type::Int))), Type::Array(None));
        assert_eq!(native_shape(&Type::LiteralInt(5)), Type::Int);
        assert_eq!(
            native_shape(&Type::Named { fqn: "C".into(), args: vec![Type::Int] }),
            Type::Named { fqn: "C".into(), args: vec![] }
        );
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
