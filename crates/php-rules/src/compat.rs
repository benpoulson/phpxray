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
    if strict_mixed_source(value, fa.check_explicit_mixed, fa.check_implicit_mixed)
        && concrete_target(target)
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

pub(crate) fn strict_mixed_source(
    ty: &Type,
    include_explicit: bool,
    include_implicit: bool,
) -> bool {
    (include_explicit && ty.contains_explicit_mixed())
        || (include_implicit && ty.contains_implicit_mixed())
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
