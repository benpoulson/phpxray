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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trinary {
    Yes,
    Maybe,
    No,
}

impl Trinary {
    pub fn from_bool(v: bool) -> Self {
        if v {
            Trinary::Yes
        } else {
            Trinary::No
        }
    }

    pub fn is_yes(self) -> bool {
        matches!(self, Trinary::Yes)
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
        Array(_) | List(_) | Iterable(_) | Shape { .. } | Callable(_) | Void | NonEmpty(_) => {
            false
        }
        Nullable(inner) => is_castable_to_string(index, inner),
        Union(parts) => parts.iter().all(|p| is_castable_to_string(index, p)),
        // An object is castable iff it declares `__toString` (Stringable); be
        // lenient when the class isn't indexed (built-in / unknown).
        Named { fqn, .. } => {
            index.find_method(fqn, "__toString").is_some() || index.class(fqn).is_none()
        }
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
        NonEmpty(inner) => native_shape(inner),
        Iterable(_) => Iterable(None),
        ClassString(_) => ClassString(None),
        LiteralInt(_) | IntRange { .. } => Int,
        LiteralString(_) | StringOf(_) => String,
        Named { fqn, .. } | EnumCase { fqn, .. } => Named {
            fqn: fqn.clone(),
            args: Vec::new(),
        },
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
        (_, Mixed | ExplicitMixed) => return true, // everything fits mixed
        (Never, _) => return true,                 // never is the bottom type
        (Mixed | ExplicitMixed, _) => return true, // mixed value — don't flag by default
        (Unknown(_), _) | (_, Unknown(_)) => return true,
        // A template variable's concrete type is unknown (bounded by its
        // `@template T of …`, which we don't track) — stay lenient either way.
        (TemplateVar(_), _) | (_, TemplateVar(_)) => return true,
        _ => {}
    }
    if value == target {
        return true;
    }

    // PHP's `/` and `**` yield a *benevolent* `int|float` (phpstan's
    // `BenevolentUnionType`). With `checkBenevolentUnionTypes` off — phpstan's
    // default at *every* level — a benevolent union satisfies a target if *any*
    // member does, so `$even / 2` (typed `int|float`) is accepted where `int` is
    // expected. We can't distinguish a benevolent union from a declared
    // `int|float`, so a declared one is likewise lenient toward a numeric target;
    // that's a safe under-report (phpstan would flag the declared case only at
    // level 8+), never a false positive.
    if let Union(parts) = value {
        let numeric = parts
            .iter()
            .all(|p| matches!(p, Int | Float | LiteralInt(_) | IntRange { .. }))
            && parts.iter().any(|p| matches!(p, Float));
        if numeric && matches!(target, Int | Float) {
            return true;
        }
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

pub fn assignable_trinary(index: &ReflectionIndex, value: &Type, target: &Type) -> Trinary {
    use Type::*;

    // Leniency escapes: top/bottom and anything we couldn't resolve.
    match (value, target) {
        (_, Mixed | ExplicitMixed) => return Trinary::Yes, // everything fits mixed
        (Never, _) => return Trinary::Yes,                 // never is the bottom type
        (Mixed | ExplicitMixed, _) => return Trinary::Maybe,
        (Unknown(_), _) | (_, Unknown(_)) => return Trinary::Maybe,
        // A template variable's concrete type is unknown (bounded by its
        // `@template T of …`, which we don't track) — stay lenient either way.
        (TemplateVar(_), _) | (_, TemplateVar(_)) => return Trinary::Maybe,
        _ => {}
    }
    if value == target {
        return Trinary::Yes;
    }

    // PHP's `/` and `**` yield a *benevolent* `int|float` (phpstan's
    // `BenevolentUnionType`). With `checkBenevolentUnionTypes` off — phpstan's
    // default at *every* level — a benevolent union satisfies a target if *any*
    // member does, so `$even / 2` (typed `int|float`) is accepted where `int` is
    // expected. We can't distinguish a benevolent union from a declared
    // `int|float`, so a declared one is likewise lenient toward a numeric target;
    // that's a safe under-report (phpstan would flag the declared case only at
    // level 8+), never a false positive.
    if let Union(parts) = value {
        let numeric = parts
            .iter()
            .all(|p| matches!(p, Int | Float | LiteralInt(_) | IntRange { .. }))
            && parts.iter().any(|p| matches!(p, Float));
        if numeric && matches!(target, Int | Float) {
            return Trinary::Yes;
        }
    }
    // A union value is assignable only if *every* member is.
    if let Union(parts) = value {
        if parts
            .iter()
            .all(|p| assignable_trinary(index, p, target).is_yes())
        {
            return Trinary::Yes;
        }
        if parts
            .iter()
            .all(|p| matches!(assignable_trinary(index, p, target), Trinary::No))
        {
            return Trinary::No;
        }
        return Trinary::Maybe;
    }
    // `?A` (value) ⊑ target iff both `A` and `null` are.
    if let Nullable(v) = value {
        return assignable_trinary(index, &Union(vec![(**v).clone(), Null].into()), target);
    }

    // A union/nullable target accepts the value if *any* arm does.
    match target {
        Nullable(t) => {
            return assignable_trinary(index, value, &Union(vec![(**t).clone(), Null].into()));
        }
        Union(parts) => {
            if parts
                .iter()
                .any(|t| assignable_trinary(index, value, t).is_yes())
            {
                return Trinary::Yes;
            }
            if parts
                .iter()
                .all(|t| matches!(assignable_trinary(index, value, t), Trinary::No))
            {
                return Trinary::No;
            }
            return Trinary::Maybe;
        }
        _ => {}
    }

    Trinary::from_bool(assignable_atom(index, value, target))
}

/// Atomic (non-union, non-nullable) assignability: scalar widening, array/iterable
/// covariance, and class subtyping.
/// Array/iterable *key* compatibility, checked benevolently. PHP array keys are
/// always `int|string`, and inference frequently widens a precise key to the full
/// `int|string` (`array-key`); requiring the key be a strict subtype then
/// false-flags `array<int|string, V>` where `array<int, V>` is wanted. Accept
/// when the keys are assignable in *either* direction (widening or narrowing),
/// which still rejects a genuinely disjoint key type (`string` vs `int`). Value
/// types stay checked strictly by the caller.
fn key_compatible(index: &ReflectionIndex, given: &Type, target: &Type) -> bool {
    is_assignable(index, given, target) || is_assignable(index, target, given)
}

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
        // A plain `int` of unknown value toward an int-range target stays lenient:
        // we can't prove it falls outside the range (mirrors plain `string` →
        // refined string). Report-maybe strictness, not a hard assignability error
        // — keeps e.g. `usleep($positiveIshInt)` from a false `argument.type`.
        (Int, IntRange { .. }) => true,
        (Float, Float) => true,
        (Bool | True | False, Bool) => true,
        (True, True) | (False, False) => true,
        (LiteralInt(a), LiteralInt(b)) => a == b,
        (String | LiteralString(_) | ClassString(_) | StringOf(_), String) => true,
        (LiteralString(a), LiteralString(b)) => a == b,
        // --- refined strings ---
        // Refinement → refinement follows the implication lattice; a literal
        // fits iff its value satisfies the refinement; a `class-string` is a
        // real non-empty name. A *plain* `string` toward a refined target stays
        // lenient (can't disprove non-emptiness) — the report-maybe machinery
        // is where "string might not be non-empty" belongs.
        (StringOf(a), StringOf(b)) => a.implies(*b),
        (LiteralString(v), StringOf(r)) => r.admits_literal(v),
        (ClassString(_), StringOf(_)) => true,
        (String, StringOf(_)) => true,
        // A plain string may hold a class name — lenient toward `class-string`
        // (phpstan allows `string`/literal → `class-string`, e.g. a name built by
        // concatenation returned where `class-string` is declared).
        (String | LiteralString(_) | ClassString(_) | StringOf(_), ClassString(_)) => true,
        (Null, Null) => true,

        // --- arrays / iterables (covariant; lenient on bare forms) ---
        (Array(_) | List(_) | Shape { .. }, Array(None)) => true,
        // A bare `array` value (no element info — e.g. `[]` or an untyped array)
        // carries nothing to disprove against, so accept any array-shaped target
        // leniently (phpstan treats `[]` as assignable to every array type).
        (Array(None), Array(_) | List(_) | Iterable(_) | Shape { .. }) => true,
        (Array(Some(a)), Array(Some(b))) => {
            key_compatible(index, &a.0, &b.0) && is_assignable(index, &a.1, &b.1)
        }
        (List(v), Array(Some(b))) => {
            is_assignable(index, &Int, &b.0) && is_assignable(index, v, &b.1)
        }
        (List(a), List(b)) => is_assignable(index, a, b),
        // An int-keyed array may be a list — lenient (only the value type matters).
        (Array(Some(a)), List(b)) => is_assignable(index, &a.1, b),

        // --- array shapes ---
        // shape ⊑ shape: every field the target *requires* must be present and
        // assignable; a target-optional field is checked only when the value
        // supplies it. Extra value fields are tolerated (lenient — avoids false
        // positives against sealed targets, where phpstan would be stricter).
        (Shape { fields: av, .. }, Shape { fields: bv, .. }) => {
            bv.iter()
                .all(|bf| match av.iter().find(|af| af.key == bf.key) {
                    Some(af) => is_assignable(index, &af.ty, &bf.ty),
                    None => bf.optional,
                })
        }
        // shape ⊑ array<K,V>: each field's key and value must fit the element types.
        (Shape { fields, .. }, Array(Some(kv))) => fields.iter().all(|f| {
            is_assignable(index, &crate::arrays::shape_field_key_type(f), &kv.0)
                && is_assignable(index, &f.ty, &kv.1)
        }),
        // shape ⊑ list<V>: lenient on key/order, check the value types.
        (Shape { fields, .. }, List(v)) => fields.iter().all(|f| is_assignable(index, &f.ty, v)),
        // A coarse array (no per-field info) ⊑ shape: can't disprove → lenient.
        (Array(_) | List(_), Shape { .. }) => true,
        (Array(_) | List(_) | Iterable(_) | Shape { .. }, Iterable(None)) => true,
        (Iterable(Some(a)) | Array(Some(a)), Iterable(Some(b))) => {
            key_compatible(index, &a.0, &b.0) && is_assignable(index, &a.1, &b.1)
        }
        // list<V> ⊑ iterable<K,V>: int keys, covariant values.
        (List(v), Iterable(Some(b))) => {
            is_assignable(index, &Int, &b.0) && is_assignable(index, v, &b.1)
        }
        // shape ⊑ iterable<K,V>: like shape ⊑ array<K,V>.
        (Shape { fields, .. }, Iterable(Some(kv))) => fields.iter().all(|f| {
            is_assignable(index, &crate::arrays::shape_field_key_type(f), &kv.0)
                && is_assignable(index, &f.ty, &kv.1)
        }),
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

        // --- non-empty containers ---
        // A non-empty value fits wherever its base fits; a base container
        // toward a non-empty target stays lenient (can't disprove emptiness —
        // the maybe-machinery is where "array might be empty" belongs).
        (NonEmpty(v), NonEmpty(t)) => is_assignable(index, v, t),
        (NonEmpty(v), _) => is_assignable(index, v, target),
        (_, NonEmpty(t)) => is_assignable(index, value, t),

        // --- enum cases (unit subtypes of their enum) ---
        (
            EnumCase { fqn: a, case: ca },
            EnumCase { fqn: b, case: cb },
        ) => a.eq_ignore_ascii_case(b) && ca == cb,
        // A case is an instance of its enum (and whatever the enum implements).
        (EnumCase { fqn, .. }, Named { .. } | Object) => is_assignable(
            index,
            &Named {
                fqn: fqn.clone(),
                args: Vec::new(),
            },
            target,
        ),
        // An enum-typed value *might* be the target case — lenient maybe.
        (Named { fqn: a, .. }, EnumCase { fqn: b, .. }) => a.eq_ignore_ascii_case(b),
        // A callable may be a Closure, an object (`__invoke`), a function-name
        // string, or an `[$obj, 'method']` array — all accepted leniently (PHP's
        // `callable` is structural; rejecting a `string`/`array` would false-flag
        // `array_map('trim', …)` and `[$this, 'm']`).
        (
            Callable(_) | Named { .. } | Object | String | LiteralString(_) | StringOf(_)
            | Array(_) | List(_),
            Callable(_),
        ) => true,

        // An unresolvable `Named` *target* — a class not in the index and not a
        // built-in — cannot be checked, so stay lenient (the §8f "unindexed class
        // is assumed compatible" principle, applied regardless of the value's
        // shape). This is what rescues generic built-in signatures whose template
        // parameters (`array<TKey, TValue>` on `array_flip`) load as phantom class
        // names rather than template vars: `int`/`string` elements then fit them.
        (_, Named { fqn, .. }) if index.class(fqn).is_none() => true,

        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_types::ShapeField;

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
        Type::Named {
            fqn: s.into(),
            args: vec![],
        }
    }

    #[test]
    fn array_key_widening_is_lenient_but_values_stay_strict() {
        let arr = |k: Type, v: Type| Type::Array(Some(Box::new((k, v))));
        let key = Type::union(vec![Type::Int, Type::String]); // array-key
        // Key-only widening (`array<int|string, string>` → `array<int, string>`)
        // is accepted; array keys are checked benevolently.
        assert!(ok(
            arr(key.clone(), Type::String),
            arr(Type::Int, Type::String)
        ));
        // A real *value* mismatch is still rejected regardless of key widening.
        assert!(!ok(arr(key, Type::Int), arr(Type::Int, Type::String)));
        // A disjoint key type is still rejected (`string` keys vs `int` keys).
        assert!(!ok(
            arr(Type::String, Type::Int),
            arr(Type::Int, Type::Int)
        ));
    }

    #[test]
    fn unresolvable_named_target_is_lenient() {
        // A concrete array fits `array<TKey, TValue>` when the template params
        // load as unindexed phantom classes (built-in generic signatures like
        // `array_flip`). Scalars fit unresolved class targets too.
        let arr = |k: Type, v: Type| Type::Array(Some(Box::new((k, v))));
        assert!(ok(
            arr(Type::Int, Type::String),
            arr(named("TKey"), named("TValue"))
        ));
        assert!(ok(Type::Int, named("SomeUnscannedVendorClass")));
    }

    #[test]
    fn scalar_to_known_class_still_fails() {
        // The leniency must not mask a real mismatch when the target class *is*
        // known: passing `int` where a known class is expected still fails.
        let (idx, _) = index_of("class C {}");
        assert!(!is_assignable(&idx, &Type::Int, &named("C")));
    }

    #[test]
    fn identity_and_top_bottom() {
        assert!(ok(Type::Int, Type::Int));
        assert!(ok(Type::Int, Type::Mixed));
        assert!(ok(Type::Never, Type::Int));
        assert!(ok(Type::Mixed, Type::Int)); // lenient
    }

    #[test]
    fn plain_int_is_lenient_toward_int_range() {
        let pos = Type::int_range(Some(0), None); // int<0, max>
        assert!(ok(Type::Int, pos.clone())); // unknown int — lenient
        assert!(ok(Type::LiteralInt(5), pos.clone())); // in range
        assert!(!ok(Type::LiteralInt(-1), pos)); // known out of range still fails
    }

    #[test]
    fn typed_arrays_fit_typed_iterables() {
        let it = |k: Type, v: Type| Type::Iterable(Some(Box::new((k, v))));
        // list<int> ⊑ iterable<int, int>
        assert!(ok(Type::List(Box::new(Type::Int)), it(Type::Int, Type::Int)));
        // array<string, int> ⊑ iterable<string, int>
        assert!(ok(
            Type::Array(Some(Box::new((Type::String, Type::Int)))),
            it(Type::String, Type::Int)
        ));
        // list<string> ⊄ iterable<int, int> (value type wrong)
        assert!(!ok(
            Type::List(Box::new(Type::String)),
            it(Type::Int, Type::Int)
        ));
        // list<int> ⊑ iterable<TKey, TValue> — unbound templates stay lenient
        assert!(ok(
            Type::List(Box::new(Type::Int)),
            it(
                Type::TemplateVar("TKey".into()),
                Type::TemplateVar("TValue".into())
            )
        ));
    }

    #[test]
    fn non_empty_container_lattice() {
        let arr = Type::Array(Some(Box::new((Type::Int, Type::String))));
        let ne = Type::non_empty(arr.clone());
        // Non-empty fits its base and bare array; base toward non-empty stays
        // lenient (can't disprove emptiness).
        assert!(ok(ne.clone(), arr.clone()));
        assert!(ok(ne.clone(), Type::Array(None)));
        assert!(ok(arr.clone(), ne.clone()));
        assert!(ok(ne.clone(), ne.clone()));
        // Kind mismatches still fail through the wrapper.
        assert!(!ok(ne.clone(), Type::Int));
        assert!(!ok(Type::Int, ne));
        // The wrapper only applies to containers.
        assert_eq!(Type::non_empty(Type::Int), Type::Int);
    }

    #[test]
    fn refined_string_lattice() {
        use php_types::StringRefinement::*;
        let ne = Type::StringOf(NonEmpty);
        let nf = Type::StringOf(NonFalsy);
        let num = Type::StringOf(Numeric);
        let lit = Type::StringOf(Literal);
        // Refined → string always.
        assert!(ok(ne.clone(), Type::String));
        assert!(ok(num.clone(), Type::String));
        // Implication lattice: numeric/non-falsy → non-empty; not vice versa.
        assert!(ok(num.clone(), ne.clone()));
        assert!(ok(nf.clone(), ne.clone()));
        assert!(!ok(ne.clone(), num.clone()));
        assert!(!ok(num.clone(), nf.clone())); // "0" is numeric and falsy
        assert!(!ok(lit.clone(), ne.clone())); // '' is a literal
        // Literals satisfy refinements by value.
        assert!(ok(Type::LiteralString("abc".into()), ne.clone()));
        assert!(!ok(Type::LiteralString("".into()), ne.clone()));
        assert!(ok(Type::LiteralString("42".into()), num.clone()));
        assert!(!ok(Type::LiteralString("x".into()), num));
        assert!(!ok(Type::LiteralString("0".into()), nf));
        // A class-string is a real, non-empty name.
        assert!(ok(Type::ClassString(None), ne.clone()));
        // Plain string toward a refinement stays lenient (maybe, not error).
        assert!(ok(Type::String, ne));
        // Refined strings are not ints.
        assert!(!ok(Type::StringOf(NonEmpty), Type::Int));
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
        let int_or_str = Type::Union(vec![Type::Int, Type::String].into());
        assert!(ok(Type::Int, int_or_str.clone()));
        assert!(ok(Type::String, int_or_str.clone()));
        assert!(!ok(Type::Float, int_or_str));
    }

    fn field(key: &str, optional: bool, ty: Type) -> ShapeField {
        ShapeField {
            key: Some(key.into()),
            optional,
            ty,
        }
    }
    fn shape(fields: Vec<ShapeField>) -> Type {
        Type::Shape {
            fields,
            sealed: true,
        }
    }

    #[test]
    fn shape_assignability() {
        // shape ⊑ shape: required field present & assignable.
        let v = shape(vec![
            field("id", false, Type::Int),
            field("name", false, Type::String),
        ]);
        let t = shape(vec![field("id", false, Type::Int)]);
        assert!(ok(v.clone(), t)); // extra value field tolerated
                                   // a wrong field type is rejected (capability preserved).
        let bad = shape(vec![field("id", false, Type::String)]);
        assert!(!ok(v.clone(), bad));
        // a missing *required* target field is rejected; optional is fine.
        let needs_extra = shape(vec![
            field("id", false, Type::Int),
            field("x", false, Type::Bool),
        ]);
        assert!(!ok(v.clone(), needs_extra));
        let opt_extra = shape(vec![
            field("id", false, Type::Int),
            field("x", true, Type::Bool),
        ]);
        assert!(ok(v.clone(), opt_extra));
        // shape ⊑ array<string, int|string>.
        assert!(ok(
            v.clone(),
            Type::Array(Some(Box::new((
                Type::String,
                Type::union(vec![Type::Int, Type::String])
            ))))
        ));
        // a coarse array ⊑ shape is lenient (can't disprove).
        assert!(ok(
            Type::Array(None),
            shape(vec![field("id", false, Type::Int)])
        ));
        assert!(ok(
            Type::Array(Some(Box::new((Type::String, Type::Mixed)))),
            shape(vec![field("id", false, Type::Int)])
        ));
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
        assert_eq!(
            native_shape(&Type::List(Box::new(Type::Int))),
            Type::Array(None)
        );
        assert_eq!(native_shape(&Type::LiteralInt(5)), Type::Int);
        assert_eq!(
            native_shape(&Type::Named {
                fqn: "C".into(),
                args: vec![Type::Int]
            }),
            Type::Named {
                fqn: "C".into(),
                args: vec![]
            }
        );
    }

    #[test]
    fn union_value_needs_all_members() {
        let v = Type::Union(vec![Type::Int, Type::String].into());
        assert!(!ok(v.clone(), Type::Int)); // string member fails
        assert!(ok(v.clone(), Type::Union(vec![Type::Int, Type::String].into())));
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
        assert!(ok(
            ai.clone(),
            Type::Array(Some(Box::new((Type::Int, Type::Float))))
        )); // int->float value
        assert!(!ok(
            ai,
            Type::Array(Some(Box::new((Type::Int, Type::String))))
        ));
        assert!(ok(Type::List(Box::new(Type::Int)), Type::Array(None)));
    }

    #[test]
    fn class_subtyping_uses_the_index() {
        let (idx, _) = index_of(
            "class Base {} class User extends Base {} interface I {} class Impl implements I {}",
        );
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
        assert!(ok(
            Type::Named {
                fqn: "Closure".into(),
                args: vec![]
            },
            Type::Callable(None)
        ));
        assert!(!ok(Type::Int, Type::Object));
    }
}
