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
//! - `NotAnalysedTraitRule` (`trait.unused`) — needs cross-file collected data
//!   (which traits are `use`d project-wide); our per-file engine has no collector.

#![allow(unused_imports)]
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{ClassDecl, ClassKind, Member, Stmt, StmtKind, Visibility};
use php_diagnostics::Diagnostic;
use php_reflect::{ConstReflection, ReflectionIndex};
use php_resolve::{for_each_region, Resolution, Scope};
use std::collections::HashMap;

/// Visit each class-like declaration with its enclosing namespace [`Scope`],
/// descending into nested/conditional blocks (so a class declared inside an
/// `if`/`try`/loop is still seen). Mirrors `classes.rs::for_each_class`.
fn for_each_class(
    program: &php_ast::Program,
    interner: &php_intern::Interner,
    mut f: impl FnMut(&Scope, &ClassDecl),
) {
    fn visit(scope: &Scope, st: &Stmt, f: &mut impl FnMut(&Scope, &ClassDecl)) {
        match &st.kind {
            StmtKind::Class(c) => f(scope, c),
            StmtKind::Block(b) => b.iter().for_each(|s| visit(scope, s, f)),
            StmtKind::If { then, elseifs, els, .. } => {
                visit(scope, then, f);
                for e in elseifs {
                    visit(scope, &e.body, f);
                }
                if let Some(e) = els {
                    visit(scope, e, f);
                }
            }
            StmtKind::While { body, .. }
            | StmtKind::DoWhile { body, .. }
            | StmtKind::For { body, .. }
            | StmtKind::Foreach { body, .. } => visit(scope, body, f),
            StmtKind::Try { body, catches, finally } => {
                body.iter().for_each(|s| visit(scope, s, f));
                for c in catches {
                    c.body.iter().for_each(|s| visit(scope, s, f));
                }
                if let Some(fin) = finally {
                    fin.iter().for_each(|s| visit(scope, s, f));
                }
            }
            StmtKind::Switch { cases, .. } => {
                for c in cases {
                    c.body.iter().for_each(|s| visit(scope, s, f));
                }
            }
            StmtKind::Declare { body: Some(b), .. } => visit(scope, b, f),
            _ => {}
        }
    }
    for_each_region(&program.stmts, interner, |scope, region| {
        for st in region {
            visit(scope, st, &mut f);
        }
    });
}

// ---------------------------------------------------------------------------
// TraitAttributesRule — `#[AllowDynamicProperties]` on a trait
// ---------------------------------------------------------------------------

fn run_trait_attributes(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |_scope, c| {
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
    for_each_class(fa.program, fa.interner, |scope, c| {
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
                let Some((tc, trait_fqn)) = trait_consts.get(cname) else { continue };
                let trait_bare = trait_fqn.trim_start_matches('\\').to_string();

                // Visibility mismatch (the overriding constant must keep the
                // trait constant's visibility).
                if let Some(msg) = visibility_message(
                    class_vis, tc.visibility, &class_bare, cname, &trait_bare,
                ) {
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

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "trait.allowDynamicProperties", level: 0, run: run_trait_attributes },
    RuleEntry {
        name: "trait.conflictingConstants",
        level: 0,
        run: run_conflicting_trait_constants,
    },
];

#[cfg(test)]
mod tests {
    use crate::testutil::codes;

    use super::*;

    // --- TraitAttributesRule ---

    #[test]
    fn allow_dynamic_properties_on_trait_is_flagged() {
        let src = r#"<?php #[AllowDynamicProperties] trait T {}"#;
        assert_eq!(codes(src, run_trait_attributes), ["trait.allowDynamicProperties"]);
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

    // --- ConflictingTraitConstantsRule ---

    #[test]
    fn private_overriding_public_trait_const_is_flagged() {
        let src = r#"<?php
            trait T { public const FOO = 1; }
            class C { use T; private const FOO = 1; }
        "#;
        assert_eq!(codes(src, run_conflicting_trait_constants), ["classConstant.visibility"]);
    }

    #[test]
    fn non_final_overriding_final_trait_const_is_flagged() {
        let src = r#"<?php
            trait T { final public const FOO = 1; }
            class C { use T; public const FOO = 1; }
        "#;
        assert_eq!(codes(src, run_conflicting_trait_constants), ["classConstant.nonFinal"]);
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
        assert_eq!(codes(src, run_conflicting_trait_constants), ["classConstant.final"]);
    }
}
