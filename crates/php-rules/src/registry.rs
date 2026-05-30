//! M-C1: the **rule registry** — a uniform interface so the engine can select
//! rules by level and run them per file.
//!
//! Each rule is a pure function of a [`FileAnalysis`] (the per-file read-only
//! inputs) returning diagnostics. Rules carry a `level`; [`rules_for_level`] is
//! cumulative (level N runs every rule with `level <= N`), mirroring phpstan's
//! 0–9 dial. Because [`analyze_file`] takes only the file plus immutable indexes
//! and has no shared mutable state, the engine's per-file loop is trivially
//! parallelizable later (Phase 2).

use crate::facts::FileFacts;
use php_ast::{Expr, Program};
use php_diagnostics::Diagnostic;
use php_index::ProjectIndex;
use php_infer::TypeMap;
use php_intern::Interner;
use php_reflect::ReflectionIndex;
use php_resolve::ResolvedRef;
use php_types::{PhpVersion, Type};

/// The read-only inputs a rule reads about one file. The shared project/reflection
/// indexes are borrowed (built once for the whole run).
pub struct FileAnalysis<'a> {
    pub path: &'a str,
    pub source: &'a str,
    pub program: &'a Program,
    pub interner: &'a Interner,
    /// Project symbol index (declarations + built-in stubs).
    pub project: &'a ProjectIndex,
    /// Project reflection index (member types, hierarchy).
    pub reflection: &'a ReflectionIndex,
    /// Resolved name references in this file.
    pub resolved_refs: &'a [ResolvedRef],
    /// Inferred type of every expression in the file, keyed by span.
    pub types: &'a TypeMap,
    /// Native-only inferred type of every expression (PHPDoc ignored), keyed by
    /// span — used by the type-compatibility rules when `treatPhpDocTypesAsCertain`
    /// is off, to suppress mismatches visible only at the PHPDoc-refined level.
    pub native_types: &'a TypeMap,
    /// Shared whole-file AST facts collected once for rules that do not need
    /// flow-sensitive local-scope traversal.
    pub facts: FileFacts<'a>,
    /// Target PHP version of the analyzed project (gates version-dependent rules).
    pub php_version: PhpVersion,
    /// phpstan's `treatPhpDocTypesAsCertain` (default `true`). When `false`, the
    /// always-true / impossible-type narrowing rules don't fire on redundancies
    /// only provable via PHPDoc-derived types.
    pub treat_phpdoc_types_as_certain: bool,
    /// phpstan's `checkUnionTypes` / `reportMaybes` strictness gate (level 7+).
    /// When `false`, partial union/nullable compatibility stays lenient.
    pub report_maybes: bool,
    /// phpstan's `checkNullables` strictness gate (level 8+). When `false` (levels
    /// 0–7), the type-compatibility rules strip `null` from the *value* type before
    /// checking it — so passing a nullable value where a non-null type is expected
    /// is not reported until level 8 (matching phpstan exactly).
    pub check_nullables: bool,
    /// phpstan's explicit `mixed` strictness gate (level 9+).
    pub check_explicit_mixed: bool,
    /// phpstan's implicit `mixed` strictness gate (`max`).
    pub check_implicit_mixed: bool,
}

impl FileAnalysis<'_> {
    /// The inferred type of expression `e` (`mixed` if it wasn't typed — e.g.
    /// inside a closure body, which the type map leaves opaque for now).
    pub fn type_of(&self, e: &Expr) -> Type {
        let r = e.span.range();
        self.types
            .get(&(r.start as u32, r.end as u32))
            .cloned()
            .unwrap_or(Type::Mixed)
    }

    /// The native-only inferred type of `e` (`mixed` if untyped/PHPDoc-only).
    pub fn native_type_of(&self, e: &Expr) -> Type {
        let r = e.span.range();
        self.native_types
            .get(&(r.start as u32, r.end as u32))
            .cloned()
            .unwrap_or(Type::Mixed)
    }

    /// Whether expression `e` may be assigned/passed/returned where `target`
    /// (native form `native_target`) is expected, honouring this run's
    /// `treatPhpDocTypesAsCertain`. Use this in the type-compatibility rules. When
    /// the flag is off, a merged mismatch is suppressed if the **native** types are
    /// compatible — i.e. the discrepancy was only at the PHPDoc-refined level.
    pub fn accepts(&self, e: &Expr, target: &Type, native_target: &Type) -> bool {
        if !crate::function_like::type_mismatch_reportable(
            self.reflection,
            &self.type_of(e),
            target,
            self.check_nullables,
            self.report_maybes,
        ) {
            return true;
        }
        if self.treat_phpdoc_types_as_certain {
            return false;
        }
        !crate::function_like::type_mismatch_reportable(
            self.reflection,
            &self.native_type_of(e),
            native_target,
            self.check_nullables,
            self.report_maybes,
        )
    }

    /// Apply the `checkNullables` strictness gate to a *value* type before a
    /// type-compatibility check: below level 8 (`check_nullables == false`), `null`
    /// is stripped, so a nullable value satisfies a non-null target (phpstan's
    /// behaviour). At level 8+ the type is checked as-is.
    pub fn lenient_src(&self, t: Type) -> Type {
        if self.check_nullables {
            t
        } else {
            php_infer::strip_null_lenient(&t)
        }
    }

    /// Whether `fqn` and *every* class it transitively extends/implements/uses/
    /// mixes-in is present in the reflection index. Member-existence rules MUST
    /// gate on this: a class with an unindexed parent (a vendor class, or a
    /// built-in like `ArrayObject` — built-in *classes* aren't reflected) may
    /// inherit the member, so reporting it absent would be a false positive.
    pub fn class_fully_known(&self, fqn: &str) -> bool {
        fn known(fa: &FileAnalysis, fqn: &str, seen: &mut Vec<String>) -> bool {
            let key = php_resolve::SymbolKey::class_like(fqn).into_string();
            if seen.contains(&key) {
                return true;
            }
            seen.push(key);
            let Some(c) = fa.reflection.class(fqn) else {
                return false;
            };
            c.parents
                .iter()
                .chain(&c.interfaces)
                .chain(&c.traits)
                .chain(&c.mixins)
                .all(|t| match t {
                    Type::Named { fqn, .. } => known(fa, fqn, seen),
                    _ => true,
                })
        }
        known(self, fqn, &mut Vec::new())
    }
}

/// A registered rule: a name, the level at which it activates, and its check.
pub struct RuleEntry {
    /// Stable rule name (the diagnostics it emits carry their own identifiers).
    pub name: &'static str,
    /// Minimum level at which this rule runs.
    pub level: u8,
    /// The check — pure over [`FileAnalysis`].
    pub run: fn(&FileAnalysis) -> Vec<Diagnostic>,
}

/// A diagnostic that may belong to a different analyzed file than the one whose
/// call site triggered the rule. `path == None` means "the current file".
#[derive(Debug, Clone)]
pub struct LocatedDiagnostic {
    pub path: Option<String>,
    pub diagnostic: Diagnostic,
}

impl LocatedDiagnostic {
    pub fn local(diagnostic: Diagnostic) -> Self {
        Self {
            path: None,
            diagnostic,
        }
    }

    pub fn at_path(path: impl Into<String>, diagnostic: Diagnostic) -> Self {
        Self {
            path: Some(path.into()),
            diagnostic,
        }
    }
}

impl From<Diagnostic> for LocatedDiagnostic {
    fn from(diagnostic: Diagnostic) -> Self {
        Self::local(diagnostic)
    }
}

/// A registered rule whose diagnostics may target another analyzed file.
pub struct LocatedRuleEntry {
    /// Stable rule name (the diagnostics it emits carry their own identifiers).
    pub name: &'static str,
    /// Minimum level at which this rule runs.
    pub level: u8,
    /// The check — pure over [`FileAnalysis`].
    pub run: fn(&FileAnalysis) -> Vec<LocatedDiagnostic>,
}

/// Machine-readable rule metadata exported for docs/tooling. Keep this as a
/// pure projection of the runtime registry so generated catalogs don't grow a
/// second source of truth for analyzer coverage.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RuleManifestEntry {
    pub name: &'static str,
    pub level: u8,
}

/// Return the analyzer's registered rule manifest, sorted for stable generated
/// output.
pub fn rule_manifest() -> Vec<RuleManifestEntry> {
    let mut out: Vec<_> = crate::rules::CATEGORY_RULES
        .iter()
        .flat_map(|cat| cat.iter())
        .map(|r| RuleManifestEntry {
            name: r.name,
            level: r.level,
        })
        .chain(
            crate::rules::LOCATED_CATEGORY_RULES
                .iter()
                .flat_map(|cat| cat.iter())
                .map(|r| RuleManifestEntry {
                    name: r.name,
                    level: r.level,
                }),
        )
        .collect();
    out.sort_by(|a, b| a.level.cmp(&b.level).then(a.name.cmp(b.name)));
    out
}

/// The rules active at `level` (cumulative: every rule with `rule.level <= level`),
/// gathered from every per-category module in [`crate::rules`].
pub fn rules_for_level(level: u8) -> impl Iterator<Item = &'static RuleEntry> {
    crate::rules::CATEGORY_RULES
        .iter()
        .flat_map(|cat| cat.iter())
        .filter(move |r| r.level <= level)
}

/// Located rules active at `level`.
pub fn located_rules_for_level(level: u8) -> impl Iterator<Item = &'static LocatedRuleEntry> {
    crate::rules::LOCATED_CATEGORY_RULES
        .iter()
        .flat_map(|cat| cat.iter())
        .filter(move |r| r.level <= level)
}

/// Run every rule active at `level` over one file and collect the diagnostics.
/// Pure over `fa` + the borrowed indexes — the engine's parallelizable unit.
pub fn analyze_file(fa: &FileAnalysis, level: u8) -> Vec<Diagnostic> {
    analyze_file_located(fa, level)
        .into_iter()
        .map(|d| d.diagnostic)
        .collect()
}

/// Run every rule active at `level`, preserving path-aware diagnostics for the
/// rules that can analyze context-specific bodies outside the current file.
pub fn analyze_file_located(fa: &FileAnalysis, level: u8) -> Vec<LocatedDiagnostic> {
    let mut out = Vec::new();
    for rule in rules_for_level(level) {
        out.extend((rule.run)(fa).into_iter().map(LocatedDiagnostic::local));
    }
    for rule in located_rules_for_level(level) {
        out.extend((rule.run)(fa));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_index::ProjectIndex;
    use php_reflect::ReflectionIndex;
    use php_resolve::{index_file, resolve_references};

    fn names_at(level: u8) -> Vec<&'static str> {
        rules_for_level(level).map(|r| r.name).collect()
    }

    #[test]
    fn level_selection_is_cumulative() {
        // Level 0 has the existence + cast rules but not the (level-3) return-type rule.
        let l0 = names_at(0);
        assert!(l0.contains(&"unknown-symbol"));
        assert!(l0.contains(&"cast.unset"));
        assert!(!l0.contains(&"return-type"));
        // The return-type rule appears at level 3.
        assert!(!names_at(2).contains(&"return-type"));
        assert!(names_at(3).contains(&"return-type"));
        // Cumulative: higher levels include everything from lower ones.
        assert!(names_at(9).len() >= names_at(3).len());
        assert!(names_at(3).len() > l0.len());
    }

    #[test]
    fn manifest_is_sorted_projection_of_registry() {
        let manifest = rule_manifest();
        assert!(!manifest.is_empty());
        assert!(manifest
            .windows(2)
            .all(|w| (w[0].level, w[0].name) <= (w[1].level, w[1].name)));
        let manifest_names: Vec<_> = manifest.iter().map(|r| r.name).collect();
        let mut registry_names: Vec<_> = crate::rules::CATEGORY_RULES
            .iter()
            .flat_map(|cat| cat.iter())
            .map(|r| r.name)
            .chain(
                crate::rules::LOCATED_CATEGORY_RULES
                    .iter()
                    .flat_map(|cat| cat.iter())
                    .map(|r| r.name),
            )
            .collect();
        registry_names.sort();
        let mut sorted_manifest_names = manifest_names;
        sorted_manifest_names.sort();
        assert_eq!(sorted_manifest_names, registry_names);
    }

    #[test]
    fn analyze_file_runs_selected_rules() {
        let src = r#"<?php
            function f(): int { return 'bad'; }
            new TotallyMadeUp();
        "#;
        let r = php_parser::parse(src);
        assert!(!r.has_errors());
        let mut project = ProjectIndex::with_builtins();
        project.add_file("t.php", &index_file(&r.program, &r.interner));
        let mut reflection = ReflectionIndex::new();
        reflection.add_file(&r.program, &r.interner);
        let refs = resolve_references(&r.program, &r.interner);
        let types = php_infer::type_map(&reflection, &r.program, &r.interner);
        let native_types = php_infer::native_type_map(&reflection, &r.program, &r.interner);
        let facts = FileFacts::new(&r.program, &r.interner);
        let fa = FileAnalysis {
            path: "t.php",
            source: src,
            program: &r.program,
            interner: &r.interner,
            project: &project,
            reflection: &reflection,
            resolved_refs: &refs,
            types: &types,
            native_types: &native_types,
            facts,
            php_version: PhpVersion::default(),
            treat_phpdoc_types_as_certain: true,
            report_maybes: true,
            check_nullables: true,
            check_explicit_mixed: true,
            check_implicit_mixed: true,
        };

        // Level 0: only the unknown-symbol rule fires.
        let l0: Vec<_> = analyze_file(&fa, 0)
            .into_iter()
            .map(|d| d.code.unwrap_or(""))
            .collect();
        assert!(l0.contains(&"class.notFound"));
        assert!(!l0.contains(&"return.type"));

        // Level 3: both fire.
        let l3: Vec<_> = analyze_file(&fa, 3)
            .into_iter()
            .map(|d| d.code.unwrap_or(""))
            .collect();
        assert!(l3.contains(&"class.notFound"));
        assert!(l3.contains(&"return.type"));
    }
}
