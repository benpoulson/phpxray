//! Shared strict type-compatibility decisions for rules that check a value
//! against a declared target type.

use crate::FileAnalysis;
use php_infer::Trinary;
use php_types::Type;

/// Whether assigning/passing/returning `value` to `target` should be reported
/// under the current rule options. When PHPDoc certainty is disabled, a mismatch
/// visible only in the merged PHPDoc-refined types is suppressed by checking the
/// native-only pair.
pub(crate) fn value_mismatch(
    fa: &FileAnalysis,
    value: &Type,
    native_value: Option<&Type>,
    target: &Type,
    native_target: &Type,
) -> bool {
    if !raw_mismatch(fa, value, target) {
        return false;
    }
    if !fa.treat_phpdoc_types_as_certain {
        if let Some(native_value) = native_value {
            return raw_mismatch(fa, native_value, native_target);
        }
    }
    true
}

/// Strict compatibility for override checks that compare type declarations
/// directly rather than expression values. This intentionally does not apply the
/// level-8 nullable source leniency: signatures themselves must be compatible.
pub(crate) fn declaration_mismatch(
    fa: &FileAnalysis,
    value: &Type,
    native_value: &Type,
    target: &Type,
    native_target: &Type,
) -> bool {
    if !raw_declaration_mismatch(fa, value, target) {
        return false;
    }
    if !fa.treat_phpdoc_types_as_certain {
        return raw_declaration_mismatch(fa, native_value, native_target);
    }
    true
}

fn raw_mismatch(fa: &FileAnalysis, value: &Type, target: &Type) -> bool {
    let checked = fa.lenient_src(value.clone());
    raw_assignability_mismatch(fa, &checked, target)
}

fn raw_declaration_mismatch(fa: &FileAnalysis, value: &Type, target: &Type) -> bool {
    raw_assignability_mismatch(fa, value, target)
}

fn raw_assignability_mismatch(fa: &FileAnalysis, value: &Type, target: &Type) -> bool {
    if concrete_target(target)
        && mixed_violates_target(
            value,
            target,
            fa.check_explicit_mixed,
            fa.check_implicit_mixed,
        )
    {
        return true;
    }

    match php_infer::assignable_trinary(fa.reflection, value, target) {
        Trinary::Yes => false,
        Trinary::No => true,
        Trinary::Maybe => {
            fa.report_maybes && maybe_is_reportable(value) && maybe_is_reportable(target)
        }
    }
}

/// Does `value`'s `mixed` sit at a position that `target` actually **constrains**?
///
/// This replaces a plain recursive containment test, which reported any `mixed`
/// anywhere inside the value type. That is wrong for containers whose value type
/// the target leaves open: `count(array<int, mixed>)` is fine, because `count`
/// accepts a bare `array`. But it is *right* when the target does pin the
/// position: `str_replace($search)` wants `array<int|string, string>`, so a
/// `mixed` value type genuinely violates it.
///
/// Walking value and target in parallel is what tells those apart. Making the
/// test merely top-level instead would have silenced ~74 corpus findings, most of
/// them real (measured).
///
/// Unconstrained positions answer `false`, keeping the low-false-positive posture:
/// where the target says nothing, we say nothing.
pub(crate) fn mixed_violates_target(
    value: &Type,
    target: &Type,
    include_explicit: bool,
    include_implicit: bool,
) -> bool {
    // The value itself is `mixed`: the caller has already established that the
    // target is concrete, so this is the plain "mixed given" case.
    match value {
        Type::ExplicitMixed => return include_explicit,
        Type::Mixed => return include_implicit,
        Type::Nullable(inner) => {
            return mixed_violates_target(inner, target, include_explicit, include_implicit)
        }
        Type::Union(parts) => {
            return parts
                .iter()
                .any(|p| mixed_violates_target(p, target, include_explicit, include_implicit))
        }
        _ => {}
    }

    // A union target accepts the value if *any* arm does, so only arms the value
    // could actually match are relevant — otherwise the shape mismatch is the
    // ordinary `argument.type` rule's business, not ours.
    if let Type::Union(arms) = target {
        let candidates: Vec<&Type> = arms.iter().filter(|t| same_shape(value, t)).collect();
        if candidates.is_empty() {
            return false;
        }
        return candidates
            .iter()
            .all(|t| mixed_violates_target(value, t, include_explicit, include_implicit));
    }

    let pair = |v: &Type, t: &Type| mixed_violates_target(v, t, include_explicit, include_implicit);
    match (value, target) {
        // Keyed containers: compare key against key, value against value.
        (
            Type::Array(Some(v)) | Type::Iterable(Some(v)),
            Type::Array(Some(t)) | Type::Iterable(Some(t)),
        ) => pair(&v.0, &t.0) || pair(&v.1, &t.1),
        // A list has integer keys; only its element type can carry mixed.
        (Type::List(v), Type::List(t)) => pair(v, t),
        (Type::List(v), Type::Array(Some(t)) | Type::Iterable(Some(t))) => pair(v, &t.1),
        (Type::ClassString(Some(v)), Type::ClassString(Some(t))) => pair(v, t),
        (Type::Callable(Some(v)), Type::Callable(Some(t))) => {
            pair(&v.ret, &t.ret)
                || v.params
                    .iter()
                    .zip(t.params.iter())
                    .any(|(vp, tp)| pair(vp, tp))
        }
        (Type::Named { args: va, .. }, Type::Named { args: ta, .. }) => {
            va.iter().zip(ta.iter()).any(|(v, t)| pair(v, t))
        }
        // Anything else: the target does not constrain this position.
        _ => false,
    }
}

/// Loose shape agreement, for picking the union arms a value could match.
fn same_shape(value: &Type, target: &Type) -> bool {
    fn array_like(t: &Type) -> bool {
        matches!(
            t,
            Type::Array(_) | Type::List(_) | Type::Iterable(_) | Type::Shape { .. }
        )
    }
    if array_like(value) && array_like(target) {
        return true;
    }
    match (value, target) {
        (Type::Callable(_), Type::Callable(_)) => true,
        (Type::ClassString(_), Type::ClassString(_)) => true,
        (Type::Named { fqn: a, .. }, Type::Named { fqn: b, .. }) => a == b,
        _ => false,
    }
}

pub(crate) fn concrete_target(ty: &Type) -> bool {
    // A union with a `mixed` arm accepts *anything*, so reporting "mixed given"
    // against it is indefensible — `is_callable(callable|mixed)` was doing exactly
    // that. `is_mixed()` only looks at the top level, hence the explicit arm scan.
    if let Type::Union(parts) = ty {
        if parts
            .iter()
            .any(|p| matches!(p, Type::Mixed | Type::ExplicitMixed))
        {
            return false;
        }
    }
    !ty.is_mixed()
        && !matches!(
            ty,
            Type::Unknown(_)
                | Type::TemplateVar(_)
                | Type::Conditional { .. }
                | Type::Void
                | Type::Never
        )
}

pub(crate) fn maybe_is_reportable(t: &Type) -> bool {
    match t {
        Type::Mixed
        | Type::ExplicitMixed
        | Type::Unknown(_)
        | Type::TemplateVar(_)
        | Type::Conditional { .. } => false,
        Type::Nullable(inner) => maybe_is_reportable(inner),
        Type::Union(parts) | Type::Intersection(parts) => parts.iter().all(maybe_is_reportable),
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            maybe_is_reportable(&kv.0) && maybe_is_reportable(&kv.1)
        }
        Type::List(inner) | Type::ClassString(Some(inner)) => maybe_is_reportable(inner),
        Type::Callable(Some(sig)) => {
            sig.params.iter().all(maybe_is_reportable) && maybe_is_reportable(&sig.ret)
        }
        Type::Named { args, .. } => args.iter().all(maybe_is_reportable),
        Type::Shape { fields, .. } => fields.iter().all(|f| maybe_is_reportable(&f.ty)),
        _ => true,
    }
}

#[cfg(test)]
mod mixed_target_tests {
    use super::{concrete_target, mixed_violates_target};
    use php_types::Type as T;

    fn arr(k: T, v: T) -> T {
        T::Array(Some(Box::new((k, v))))
    }
    fn named(n: &str) -> T {
        T::Named {
            fqn: n.into(),
            args: vec![],
        }
    }

    /// The discriminating pair, measured on the Zend corpus: testing *containment*
    /// reports 54 findings where the target constrains nothing; testing only the
    /// *top level* loses 65 real ones where it does. Walking value and target
    /// together is what answers both correctly.
    #[test]
    fn nested_mixed_counts_only_where_the_target_constrains_it() {
        let value = arr(T::Int, T::Mixed);

        // `count(array|Countable)`: the `array` arm pins no value type, so an
        // `array<int, mixed>` argument is fine.
        let unconstrained = T::union(vec![T::Array(None), named("Countable")]);
        assert!(concrete_target(&unconstrained));
        assert!(
            !mixed_violates_target(&value, &unconstrained, false, true),
            "an unconstrained value position must not be reported"
        );

        // `str_replace($search)` wants `array<int|string, string>` — the mixed
        // value type genuinely violates that.
        let constrained = T::union(vec![
            T::String,
            arr(T::union(vec![T::Int, T::String]), T::String),
        ]);
        assert!(
            mixed_violates_target(&value, &constrained, false, true),
            "a constrained value position must still be reported"
        );
    }

    #[test]
    fn top_level_mixed_is_always_reported_against_a_concrete_target() {
        assert!(mixed_violates_target(&T::Mixed, &T::Int, false, true));
        assert!(mixed_violates_target(
            &T::ExplicitMixed,
            &T::Int,
            true,
            false
        ));
        // ...and honours the strictness flags.
        assert!(!mixed_violates_target(&T::Mixed, &T::Int, true, false));
        assert!(!mixed_violates_target(
            &T::ExplicitMixed,
            &T::Int,
            false,
            true
        ));
    }

    #[test]
    fn a_target_that_accepts_mixed_is_not_concrete() {
        // `is_callable(callable|mixed)` accepts anything.
        let accepts = T::union(vec![T::Callable(None), T::Mixed]);
        assert!(!concrete_target(&accepts));
        assert!(!concrete_target(&T::Mixed));
        assert!(concrete_target(&T::union(vec![T::Int, T::String])));
    }

    #[test]
    fn lists_pair_against_the_value_position() {
        let list_of_mixed = T::List(Box::new(T::Mixed));
        // Bare `array` target: unconstrained.
        assert!(!mixed_violates_target(
            &list_of_mixed,
            &T::Array(None),
            false,
            true
        ));
        // `array<int|string, string>` target: constrained.
        let constrained = arr(T::union(vec![T::Int, T::String]), T::String);
        assert!(mixed_violates_target(
            &list_of_mixed,
            &constrained,
            false,
            true
        ));
        // `list<string>` target: constrained.
        assert!(mixed_violates_target(
            &list_of_mixed,
            &T::List(Box::new(T::String)),
            false,
            true
        ));
    }
}
