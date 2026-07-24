//! Rule implementations, **one module per phpstan category** (the subdirectories
//! of `phpstan-src/src/Rules/`). Each category module exposes a `RULES` slice of
//! [`RuleEntry`]; [`CATEGORY_RULES`] aggregates them for the registry's
//! level-based selection. The full per-rule checklist is `docs/phpstan-rules.md`.
//!
//! Predefined categories (phpstan dir → module, with rule count @ levels):
//! Functions→functions (41 @0–6), Classes→classes (37 @0,1,2,4),
//! Properties→properties (31), Methods→methods (29), PhpDoc→phpdoc (22),
//! Comparison→comparison (19), Generics→generics (15), Arrays→arrays (13),
//! Variables→variables (12), Constants→constants (11), Exceptions→exceptions (9),
//! DeadCode→dead_code (9), Operators→operators (7), Cast→cast (7),
//! TooWideTypehints→too_wide_typehints (7), Traits→traits (4), Keywords→keywords (4),
//! Generators→generators (3), Regexp→regexp (2), Namespaces→namespaces (2),
//! EnumCases→enum_cases (2), Pure→pure (2), Types→types (1), Names→names (1),
//! Missing→missing (1), Whitespace→whitespace (1), DateTimeInstantiation→datetime (1),
//! (root)→misc (1).
//!
//! Skipped (phpstan-internal, not user-code analysis): **Api** (phpstan
//! extension-development API) and **Ignore** (phpstan's own ignore-comment
//! handling — we do suppression in `phpxray`).

use crate::{FactRuleEntry, FileAnalysis, LocatedRuleEntry, RuleEntry};
use php_types::Type;

mod arrays;
mod callback_context;
mod cast;
mod classes;
mod comparison;
mod constants;
mod datetime;
mod dead_code;
mod enum_cases;
mod exceptions;
mod functions;
mod generators;
mod generics;
mod keywords;
mod methods;
mod misc;
mod missing;
mod names;
mod namespaces;
mod operators;
mod phpdoc;
mod properties;
mod pure;
mod regexp;
mod too_wide_typehints;
mod traits;
mod types;
mod variables;
mod whitespace;

/// Every category's rule slice. The registry flattens this and filters by level.
pub(crate) static CATEGORY_RULES: &[&[RuleEntry]] = &[
    arrays::RULES,
    cast::RULES,
    classes::RULES,
    comparison::RULES,
    constants::RULES,
    datetime::RULES,
    dead_code::RULES,
    enum_cases::RULES,
    exceptions::RULES,
    functions::RULES,
    generators::RULES,
    generics::RULES,
    keywords::RULES,
    methods::RULES,
    misc::RULES,
    missing::RULES,
    names::RULES,
    namespaces::RULES,
    operators::RULES,
    phpdoc::RULES,
    properties::RULES,
    pure::RULES,
    regexp::RULES,
    too_wide_typehints::RULES,
    traits::RULES,
    types::RULES,
    variables::RULES,
    whitespace::RULES,
];

pub(crate) static FACT_CATEGORY_RULES: &[&[FactRuleEntry]] = &[
    arrays::FACT_RULES,
    cast::FACT_RULES,
    comparison::FACT_RULES,
    operators::FACT_RULES,
    regexp::FACT_RULES,
];

/// Rules whose diagnostics may target a different analyzed file than the current
/// file being walked.
pub(crate) static LOCATED_CATEGORY_RULES: &[&[LocatedRuleEntry]] = &[callback_context::RULES];

pub(crate) fn type_contains_null(t: &Type) -> bool {
    match t {
        Type::Null | Type::Nullable(_) => true,
        Type::Union(parts) => parts.iter().any(type_contains_null),
        _ => false,
    }
}

pub(crate) fn non_null_part(t: &Type) -> Option<Type> {
    if !type_contains_null(t) || matches!(t, Type::Null) {
        return None;
    }
    let stripped = php_infer::strip_null_lenient(t);
    if matches!(stripped, Type::Null | Type::Never) {
        None
    } else {
        Some(stripped)
    }
}

pub(crate) fn nullable_type_display(t: &Type) -> String {
    fn collect(t: &Type, shown: &mut Vec<String>) -> bool {
        match t {
            Type::Null => true,
            Type::Nullable(inner) => {
                collect(inner, shown);
                true
            }
            Type::Union(parts) => {
                let mut saw_null = false;
                for part in parts.iter() {
                    saw_null |= collect(part, shown);
                }
                saw_null
            }
            other => {
                let s = other.to_string();
                if !shown.contains(&s) {
                    shown.push(s);
                }
                false
            }
        }
    }

    let mut shown = Vec::new();
    let saw_null = collect(t, &mut shown);
    if saw_null {
        shown.push("null".to_string());
    }
    shown.join("|")
}

pub(crate) fn known_objectish_type(fa: &FileAnalysis, t: &Type) -> bool {
    match t {
        Type::Named { fqn, .. } | Type::EnumCase { fqn, .. } => {
            fa.project.has_class(fqn) || fa.reflection.class(fqn).is_some()
        }
        Type::Union(parts) => {
            !parts.is_empty() && parts.iter().all(|p| known_objectish_type(fa, p))
        }
        Type::Intersection(parts) => parts.iter().any(|p| known_objectish_type(fa, p)),
        _ => false,
    }
}
