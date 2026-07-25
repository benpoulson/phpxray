//! phpstan category **Traits** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Traits/`.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented here:
//! - **TraitAttributesRule** (`trait.allowDynamicProperties`, level 0) — the
//!   `#[AllowDynamicProperties]` attribute cannot be used on a trait (always
//!   invalid, independent of PHP version).
//! - **ConflictingTraitConstantsRule** (`classConstant.visibility`/
//!   `classConstant.nonFinal`/`classConstant.final`, level 0) — a class constant
//!   overriding a same-named constant inherited from one of the class's traits
//!   must keep a compatible visibility / finality.
//! - **NotAnalysedTraitRule** (`trait.unused`, level 4) — a trait declared in
//!   the analysed project but not used by any indexed class-like symbol.
//!
//! Deferred (need analysis / inputs we don't model):
//! - `ConstantsInTraitsRule` (`classConstant.inTrait`) — a pure PHP-version gate
//!   (constants in traits need 8.2); we target 8.6, so it is always clean.
//! - `TraitAttributesRule`'s `Deprecated`-attribute check (`trait.deprecatedAttribute`)
//!   — a PHP-version gate (8.5); always clean at our 8.6 target.
//! - `ConflictingTraitConstantsRule`'s value / native-type comparisons
//!   (`classConstant.value`/`classConstant.nativeType`/`classConstant.missingNativeType`)
//!   — need constant-value evaluation + native-type-equality of trait constants,
//!   not modelled here.

use crate::{FileAnalysis, RuleEntry};
use php_ast::{ClassKind, Member, Visibility};
use php_diagnostics::Diagnostic;
use php_reflect::{ConstReflection, ReflectionIndex};

use std::collections::{HashMap, HashSet};


// ---------------------------------------------------------------------------
// TraitAttributesRule — `#[AllowDynamicProperties]` on a trait
// ---------------------------------------------------------------------------

/// `ConstantsInTraitsRule` — a constant declared in a trait on a target PHP
/// version that doesn't support them (< 8.2). Version-gated on `fa.php_version`.
fn run_constants_in_traits(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if fa.php_version.at_least(80200) {
        return Vec::new();
    }
    let mut out = Vec::new();
    crate::decls::for_each_class_like(fa, |_scope, _fqn, c| {
        if c.kind != ClassKind::Trait {
            return;
        }
        for m in &c.members {
            let Member::ClassConst(cd) = m else { continue };
            if let Some(ce) = cd.consts.first() {
                out.push(
                    Diagnostic::error(
                        ce.value.span,
                        "Constant is declared inside a trait but is only supported on PHP 8.2 and later.",
                    )
                    .with_code("classConstant.inTrait"),
                );
            }
        }
    });
    out
}

fn run_trait_attributes(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::decls::for_each_class_like(fa, |_scope, _fqn, c| {
        if c.kind != ClassKind::Trait {
            return;
        }
        for g in &c.attrs {
            for a in &g.attrs {
                let text = a.name.text.trim_start_matches('\\');
                let last = text.rsplit('\\').next().unwrap_or(text);
                if last.eq_ignore_ascii_case("AllowDynamicProperties") {
                    out.push(
                        Diagnostic::error(
                            a.name.span,
                            "Attribute class AllowDynamicProperties cannot be used with trait.",
                        )
                        .with_code("trait.allowDynamicProperties"),
                    );
                }
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// ConflictingTraitConstantsRule — visibility / finality of overriding constants
// ---------------------------------------------------------------------------

/// Gather every constant (by name) reachable through a class's traits,
/// transitively (a trait may itself `use` further traits). Mirrors phpstan's
/// `getTraits(true)`. Keyed by constant name; first-seen wins (we only need the
/// modifiers, which are identical for the same declared constant).
fn recursive_trait_constants<'a>(
    refl: &'a ReflectionIndex,
    class_fqn: &str,
) -> HashMap<String, (&'a ConstReflection, String)> {
    let mut acc: HashMap<String, (&ConstReflection, String)> = HashMap::new();
    let mut seen: Vec<String> = Vec::new();

    fn collect<'a>(
        refl: &'a ReflectionIndex,
        fqn: &str,
        seen: &mut Vec<String>,
        acc: &mut HashMap<String, (&'a ConstReflection, String)>,
    ) {
        let key = fqn.trim_start_matches('\\').to_ascii_lowercase();
        if seen.contains(&key) {
            return;
        }
        seen.push(key);
        let Some(c) = refl.class(fqn) else { return };
        for tr in &c.traits {
            if let php_types::Type::Named { fqn: trait_fqn, .. } = tr {
                if let Some(tc) = refl.class(trait_fqn) {
                    for k in &tc.constants {
                        acc.entry(k.name.clone()).or_insert((k, tc.fqn.clone()));
                    }
                }
                collect(refl, trait_fqn, seen, acc);
            }
        }
    }

    collect(refl, class_fqn, &mut seen, &mut acc);
    acc
}

fn run_conflicting_trait_constants(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::decls::for_each_class_like(fa, |scope, _fqn, c| {
        // Only a class/enum can `use` traits and declare overriding constants; we
        // need the declaring class's own FQN to address it.
        let Some(name_sym) = c.name else { return };
        let class_display = scope.qualify(fa.interner.resolve(name_sym));
        let class_fqn = format!("\\{}", class_display.trim_start_matches('\\'));

        let trait_consts = recursive_trait_constants(fa.reflection, &class_fqn);
        if trait_consts.is_empty() {
            return;
        }
        let class_bare = class_display.trim_start_matches('\\').to_string();

        for m in &c.members {
            let Member::ClassConst(cd) = m else { continue };
            let class_vis = cd.modifiers.visibility.unwrap_or(Visibility::Public);
            let class_final = cd.modifiers.is_final;
            for ce in &cd.consts {
                let cname = fa.interner.resolve(ce.name);
                let Some((tc, trait_fqn)) = trait_consts.get(cname) else {
                    continue;
                };
                let trait_bare = trait_fqn.trim_start_matches('\\').to_string();

                // Visibility mismatch (the overriding constant must keep the
                // trait constant's visibility).
                if let Some(msg) =
                    visibility_message(class_vis, tc.visibility, &class_bare, cname, &trait_bare)
                {
                    out.push(
                        Diagnostic::error(ce.value.span, msg).with_code("classConstant.visibility"),
                    );
                }

                // Finality mismatch.
                if tc.is_final && !class_final {
                    out.push(
                        Diagnostic::error(
                            ce.value.span,
                            format!(
                                "Non-final constant {class_bare}::{cname} overriding final constant {trait_bare}::{cname} should also be final.",
                            ),
                        )
                        .with_code("classConstant.nonFinal"),
                    );
                } else if !tc.is_final && class_final {
                    out.push(
                        Diagnostic::error(
                            ce.value.span,
                            format!(
                                "Final constant {class_bare}::{cname} overriding non-final constant {trait_bare}::{cname} should also be non-final.",
                            ),
                        )
                        .with_code("classConstant.final"),
                    );
                }
            }
        }
    });
    out
}

/// The phpstan visibility-mismatch message for an overriding class constant, or
/// `None` if the visibilities are compatible (equal).
fn visibility_message(
    class_vis: Visibility,
    trait_vis: Visibility,
    class: &str,
    cname: &str,
    trait_name: &str,
) -> Option<String> {
    if class_vis == trait_vis {
        return None;
    }
    let word = |v: Visibility| match v {
        Visibility::Public => "public",
        Visibility::Protected => "protected",
        Visibility::Private => "private",
    };
    Some(format!(
        "{cw} constant {class}::{cname} overriding {tw} constant {trait_name}::{cname} should also be {tw}.",
        cw = cap(word(class_vis)),
        tw = word(trait_vis),
    ))
}

/// Capitalise the first letter (`private` → `Private`) for the message head.
fn cap(s: &str) -> String {
    let mut ch = s.chars();
    match ch.next() {
        Some(c) => c.to_uppercase().collect::<String>() + ch.as_str(),
        None => String::new(),
    }
}

// ---------------------------------------------------------------------------
// NotAnalysedTraitRule — unused traits
// ---------------------------------------------------------------------------

fn run_not_analysed_trait(fa: &FileAnalysis) -> Vec<Diagnostic> {
    // Collect this file's trait declarations first: most files declare none,
    // and the project-wide usage scan below is a whole-index dependency that
    // incremental analysis re-runs on any surface change — only pay it (and
    // record it) for files that actually declare traits.
    let mut own_traits: Vec<(String, php_span::Span)> = Vec::new();
    crate::decls::for_each_class_like(fa, |scope, _fqn, c| {
        if c.kind != ClassKind::Trait {
            return;
        }
        if let Some(name) = c.name {
            own_traits.push((scope.qualify(fa.interner.resolve(name)), c.name_span));
        }
    });
    if own_traits.is_empty() {
        return Vec::new();
    }

    let used_traits: HashSet<String> = fa
        .project
        .classes()
        .flat_map(|c| c.uses_traits.iter())
        .map(|t| t.trim_start_matches('\\').to_ascii_lowercase())
        .collect();

    let mut out = Vec::new();
    for (fqn, name_span) in own_traits {
        let Some(entry) = fa.project.class(&fqn) else {
            continue;
        };
        if !entry.sources.iter().any(|source| source == fa.path) {
            continue;
        }
        if used_traits.contains(&fqn.trim_start_matches('\\').to_ascii_lowercase()) {
            continue;
        }
        out.push(
            Diagnostic::error(
                name_span,
                format!(
                    "Trait {} is used zero times and is not analysed.",
                    fqn.trim_start_matches('\\')
                ),
            )
            .with_code("trait.unused"),
        );
    }
    out
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "trait.allowDynamicProperties",
        level: 0,
        run: run_trait_attributes,
    },
    RuleEntry {
        name: "trait.conflictingConstants",
        level: 0,
        run: run_conflicting_trait_constants,
    },
    RuleEntry {
        name: "classConstant.inTrait",
        level: 0,
        run: run_constants_in_traits,
    },
    RuleEntry {
        name: "trait.unused",
        level: 4,
        run: run_not_analysed_trait,
    },
];

#[cfg(test)]
mod tests {
    use crate::testutil::{codes, codes_version};
    use crate::PhpVersion;

    use super::*;

    #[test]
    fn const_in_trait_flagged_below_82() {
        let src = "<?php trait T { const X = 1; }";
        let v81 = PhpVersion::parse("8.1").unwrap();
        assert_eq!(
            codes_version(src, run_constants_in_traits, v81),
            ["classConstant.inTrait"]
        );
    }

    #[test]
    fn const_in_trait_clean_at_default() {
        let src = "<?php trait T { const X = 1; }";
        assert!(codes(src, run_constants_in_traits).is_empty());
    }

    #[test]
    fn const_in_class_below_82_clean() {
        let src = "<?php class C { const X = 1; }";
        let v81 = PhpVersion::parse("8.1").unwrap();
        assert!(codes_version(src, run_constants_in_traits, v81).is_empty());
    }

    // --- TraitAttributesRule ---

    #[test]
    fn allow_dynamic_properties_on_trait_is_flagged() {
        let src = r#"<?php #[AllowDynamicProperties] trait T {}"#;
        assert_eq!(
            codes(src, run_trait_attributes),
            ["trait.allowDynamicProperties"]
        );
    }

    #[test]
    fn allow_dynamic_properties_on_class_is_ok() {
        let src = r#"<?php #[AllowDynamicProperties] class C {}"#;
        assert!(codes(src, run_trait_attributes).is_empty());
    }

    #[test]
    fn plain_trait_is_ok() {
        let src = r#"<?php trait T { public int $x; }"#;
        assert!(codes(src, run_trait_attributes).is_empty());
    }

    // --- NotAnalysedTraitRule ---

    #[test]
    fn unused_trait_is_flagged() {
        let src = "<?php namespace App; trait T {}";
        assert_eq!(codes(src, run_not_analysed_trait), ["trait.unused"]);
    }

    #[test]
    fn used_trait_is_clean() {
        let src = "<?php namespace App; trait T {} class C { use T; }";
        assert!(codes(src, run_not_analysed_trait).is_empty());
    }

    #[test]
    fn used_trait_in_global_namespace_is_clean() {
        let src = "<?php trait A { public function a() {} } class C { use A; }";
        assert!(codes(src, run_not_analysed_trait).is_empty());
    }

    // --- ConflictingTraitConstantsRule ---

    #[test]
    fn private_overriding_public_trait_const_is_flagged() {
        let src = r#"<?php
            trait T { public const FOO = 1; }
            class C { use T; private const FOO = 1; }
        "#;
        assert_eq!(
            codes(src, run_conflicting_trait_constants),
            ["classConstant.visibility"]
        );
    }

    #[test]
    fn non_final_overriding_final_trait_const_is_flagged() {
        let src = r#"<?php
            trait T { final public const FOO = 1; }
            class C { use T; public const FOO = 1; }
        "#;
        assert_eq!(
            codes(src, run_conflicting_trait_constants),
            ["classConstant.nonFinal"]
        );
    }

    #[test]
    fn matching_visibility_and_finality_is_ok() {
        let src = r#"<?php
            trait T { public const FOO = 1; }
            class C { use T; public const FOO = 1; }
        "#;
        assert!(codes(src, run_conflicting_trait_constants).is_empty());
    }

    #[test]
    fn unrelated_constant_name_is_ok() {
        let src = r#"<?php
            trait T { public const FOO = 1; }
            class C { use T; private const BAR = 1; }
        "#;
        assert!(codes(src, run_conflicting_trait_constants).is_empty());
    }

    #[test]
    fn class_without_traits_is_ok() {
        let src = r#"<?php class C { private const FOO = 1; }"#;
        assert!(codes(src, run_conflicting_trait_constants).is_empty());
    }

    #[test]
    fn final_overriding_non_final_is_flagged() {
        let src = r#"<?php
            trait T { public const FOO = 1; }
            class C { use T; final public const FOO = 1; }
        "#;
        assert_eq!(
            codes(src, run_conflicting_trait_constants),
            ["classConstant.final"]
        );
    }
}

#[cfg(test)]
mod local_class_tests {
    use crate::testutil::codes;

    /// Regression: `traits.rs` hand-rolled its own class visitor that did not
    /// descend into function bodies, so a trait (or class) declared inside a
    /// function was invisible to every rule in this file — a silent false
    /// negative. The canonical `decls::for_each_class_like` descends correctly.
    #[test]
    fn traits_declared_inside_a_function_are_analysed() {
        let src = "<?php function make() { trait LocalT { public function t(): void {} } }";
        assert_eq!(codes(src, super::run_not_analysed_trait), ["trait.unused"]);
    }
}
