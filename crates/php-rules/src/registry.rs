//! M-C1: the **rule registry** — a uniform interface so the engine can select
//! rules by level and run them per file.
//!
//! Each rule is a pure function of a [`FileAnalysis`] (the per-file read-only
//! inputs) returning diagnostics. Rules carry a `level`; [`rules_for_level`] is
//! cumulative (level N runs every rule with `level <= N`), mirroring phpstan's
//! 0–9 dial. Because [`analyze_file`] takes only the file plus immutable indexes
//! and has no shared mutable state, the engine's per-file loop is trivially
//! parallelizable later (Phase 2).

use php_ast::{Expr, Program};
use php_diagnostics::Diagnostic;
use php_index::ProjectIndex;
use php_infer::TypeMap;
use php_intern::Interner;
use php_reflect::ReflectionIndex;
use php_resolve::ResolvedRef;
use php_types::Type;

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
}

impl FileAnalysis<'_> {
    /// The inferred type of expression `e` (`mixed` if it wasn't typed — e.g.
    /// inside a closure body, which the type map leaves opaque for now).
    pub fn type_of(&self, e: &Expr) -> Type {
        let r = e.span.range();
        self.types.get(&(r.start as u32, r.end as u32)).cloned().unwrap_or(Type::Mixed)
    }

    /// Whether `fqn` and *every* class it transitively extends/implements/uses/
    /// mixes-in is present in the reflection index. Member-existence rules MUST
    /// gate on this: a class with an unindexed parent (a vendor class, or a
    /// built-in like `ArrayObject` — built-in *classes* aren't reflected) may
    /// inherit the member, so reporting it absent would be a false positive.
    pub fn class_fully_known(&self, fqn: &str) -> bool {
        fn known(fa: &FileAnalysis, fqn: &str, seen: &mut Vec<String>) -> bool {
            let key = fqn.trim_start_matches('\\').to_ascii_lowercase();
            if seen.contains(&key) {
                return true;
            }
            seen.push(key);
            let Some(c) = fa.reflection.class(fqn) else { return false };
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

/// The rules active at `level` (cumulative: every rule with `rule.level <= level`),
/// gathered from every per-category module in [`crate::rules`].
pub fn rules_for_level(level: u8) -> impl Iterator<Item = &'static RuleEntry> {
    crate::rules::CATEGORY_RULES.iter().flat_map(|cat| cat.iter()).filter(move |r| r.level <= level)
}

/// Run every rule active at `level` over one file and collect the diagnostics.
/// Pure over `fa` + the borrowed indexes — the engine's parallelizable unit.
pub fn analyze_file(fa: &FileAnalysis, level: u8) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for rule in rules_for_level(level) {
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
        let fa = FileAnalysis {
            path: "t.php",
            source: src,
            program: &r.program,
            interner: &r.interner,
            project: &project,
            reflection: &reflection,
            resolved_refs: &refs,
            types: &types,
        };

        // Level 0: only the unknown-symbol rule fires.
        let l0: Vec<_> = analyze_file(&fa, 0).into_iter().map(|d| d.code.unwrap_or("")).collect();
        assert!(l0.contains(&"class.notFound"));
        assert!(!l0.contains(&"return.type"));

        // Level 3: both fire.
        let l3: Vec<_> = analyze_file(&fa, 3).into_iter().map(|d| d.code.unwrap_or("")).collect();
        assert!(l3.contains(&"class.notFound"));
        assert!(l3.contains(&"return.type"));
    }
}
