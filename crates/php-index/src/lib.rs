//! A project-wide symbol index: aggregates the per-file
//! [`FileIndex`](php_resolve::FileIndex)es produced by name resolution into one
//! queryable map of every class/function/constant declared across the project.
//!
//! This layer owns existence and source/origin metadata. Typed reflection and
//! hierarchy queries live in `php-reflect`. Lookups respect PHP's case rules —
//! class and function names are case-insensitive, constants case-sensitive —
//! while preserving each symbol's canonical (declared) casing.

use php_ast::ClassKind;
use php_resolve::{display_fqn, FileIndex, SymbolKey, SymbolOrigin};
use php_types::{builtins, PhpVersion};
use std::collections::HashMap;

/// A class/interface/trait/enum known to the project.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassEntry {
    /// Canonical fully-qualified name (the casing of the first declaration seen).
    pub fqn: String,
    pub kind: ClassKind,
    pub extends: Vec<String>,
    pub implements: Vec<String>,
    pub uses_traits: Vec<String>,
    /// File labels where this symbol is declared; more than one = a redeclaration.
    pub sources: Vec<String>,
    /// Origin category for each corresponding entry in [`sources`](Self::sources).
    pub origins: Vec<SourceKind>,
}

/// A function or constant known to the project.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolEntry {
    pub fqn: String,
    pub sources: Vec<String>,
    pub origins: Vec<SourceKind>,
}

/// How a parsed file participates in the project index.
pub type SourceKind = SymbolOrigin;

/// The aggregated symbol table for a whole project.
#[derive(Debug, Default, Clone)]
pub struct ProjectIndex {
    classes: HashMap<String, ClassEntry>,    // key: lowercased FQN
    functions: HashMap<String, SymbolEntry>, // key: lowercased FQN
    constants: HashMap<String, SymbolEntry>, // key: exact FQN (case-sensitive)
}

impl ProjectIndex {
    pub fn new() -> Self {
        Self::default()
    }

    /// A project index pre-populated with PHP's built-in functions, classes,
    /// interfaces, traits, enums and constants.
    pub fn with_builtins() -> Self {
        Self::with_builtins_for(PhpVersion::default())
    }

    /// A project index pre-populated with PHP built-in names for `version`, using
    /// the same versioned manifests as typed reflection.
    pub fn with_builtins_for(version: PhpVersion) -> Self {
        let mut idx = Self::new();
        idx.load_builtins(version);
        idx
    }

    fn load_builtins(&mut self, version: PhpVersion) {
        for f in builtins::functions_for(version) {
            push_symbol(
                &mut self.functions,
                SymbolKey::function(f.fqn).into_string(),
                f.fqn,
                builtins::BUILTIN_SOURCE,
                SourceKind::Builtin,
            );
        }
        for c in builtins::constants_for(version) {
            push_symbol(
                &mut self.constants,
                SymbolKey::constant(c.fqn).into_string(),
                c.fqn,
                builtins::BUILTIN_SOURCE,
                SourceKind::Builtin,
            );
        }
        for record in builtins::class_records_for(version) {
            let builtins::BuiltinClassRecord::Class {
                kind,
                fqn,
                parents,
                interfaces,
                traits,
                ..
            } = record
            else {
                continue;
            };
            if fqn.is_empty() {
                continue;
            }
            self.classes
                .entry(SymbolKey::class_like(fqn).into_string())
                .or_insert_with(|| ClassEntry {
                    fqn: fqn.to_string(),
                    kind: builtin_class_kind(kind),
                    extends: parents.into_iter().map(str::to_string).collect(),
                    implements: interfaces.into_iter().map(str::to_string).collect(),
                    uses_traits: traits.into_iter().map(str::to_string).collect(),
                    sources: vec![builtins::BUILTIN_SOURCE.to_string()],
                    origins: vec![SourceKind::Builtin],
                });
        }
    }

    /// Merge one file's resolved declarations into the project index, labelling
    /// each declaration with `source` (e.g. a file path).
    pub fn add_file(&mut self, source: &str, file: &FileIndex) {
        self.add_file_as(source, file, SourceKind::Analyzed);
    }

    /// Merge one file's declarations, distinguishing analyzed project files from
    /// scan-only symbol providers. Scan-only declarations never replace or
    /// duplicate a curated built-in.
    pub fn add_file_as(&mut self, source: &str, file: &FileIndex, kind: SourceKind) {
        for c in &file.classes {
            if kind == SourceKind::Scan
                && self
                    .classes
                    .get(&SymbolKey::class_like(&c.fqn).into_string())
                    .is_some_and(is_builtin_class)
            {
                continue;
            }
            match self
                .classes
                .entry(SymbolKey::class_like(&c.fqn).into_string())
            {
                std::collections::hash_map::Entry::Occupied(mut e) => {
                    e.get_mut().sources.push(source.to_string());
                    e.get_mut().origins.push(kind);
                }
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(ClassEntry {
                        fqn: c.fqn.clone(),
                        kind: c.kind,
                        extends: c.extends.clone(),
                        implements: c.implements.clone(),
                        uses_traits: c.uses_traits.clone(),
                        sources: vec![source.to_string()],
                        origins: vec![kind],
                    });
                }
            }
        }
        for f in &file.functions {
            let key = SymbolKey::function(&f.fqn).into_string();
            if kind == SourceKind::Scan && self.functions.get(&key).is_some_and(is_builtin_symbol) {
                continue;
            }
            push_symbol(&mut self.functions, key, &f.fqn, source, kind);
        }
        for k in &file.constants {
            let key = SymbolKey::constant(&k.fqn).into_string();
            if kind == SourceKind::Scan && self.constants.get(&key).is_some_and(is_builtin_symbol) {
                continue;
            }
            push_symbol(&mut self.constants, key, &k.fqn, source, kind);
        }
    }

    // --- lookups (respecting PHP case rules) ----------------------------

    pub fn class(&self, fqn: &str) -> Option<&ClassEntry> {
        self.classes.get(&SymbolKey::class_like(fqn).into_string())
    }
    pub fn function(&self, fqn: &str) -> Option<&SymbolEntry> {
        self.functions.get(&SymbolKey::function(fqn).into_string())
    }
    pub fn constant(&self, fqn: &str) -> Option<&SymbolEntry> {
        self.constants.get(&SymbolKey::constant(fqn).into_string())
    }

    pub fn has_class(&self, fqn: &str) -> bool {
        self.class(fqn).is_some()
    }
    pub fn has_function(&self, fqn: &str) -> bool {
        self.function(fqn).is_some()
    }
    pub fn has_constant(&self, fqn: &str) -> bool {
        self.constant(fqn).is_some()
    }

    pub fn class_count(&self) -> usize {
        self.classes.len()
    }
    /// All indexed class-like symbols (classes, interfaces, traits, enums).
    pub fn classes(&self) -> impl Iterator<Item = &ClassEntry> {
        self.classes.values()
    }
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }
    /// All indexed functions.
    pub fn functions(&self) -> impl Iterator<Item = &SymbolEntry> {
        self.functions.values()
    }
    pub fn constant_count(&self) -> usize {
        self.constants.len()
    }
    /// All indexed constants.
    pub fn constants(&self) -> impl Iterator<Item = &SymbolEntry> {
        self.constants.values()
    }

    /// Classes (and interfaces/traits/enums) declared in more than one file.
    pub fn duplicate_classes(&self) -> impl Iterator<Item = &ClassEntry> {
        self.classes.values().filter(|c| c.sources.len() > 1)
    }
}

fn is_builtin_class(e: &ClassEntry) -> bool {
    e.origins.contains(&SourceKind::Builtin)
}

fn is_builtin_symbol(e: &SymbolEntry) -> bool {
    e.origins.contains(&SourceKind::Builtin)
}

fn builtin_class_kind(kind: builtins::BuiltinClassKind) -> ClassKind {
    match kind {
        builtins::BuiltinClassKind::Class => ClassKind::Class,
        builtins::BuiltinClassKind::Interface => ClassKind::Interface,
        builtins::BuiltinClassKind::Trait => ClassKind::Trait,
        builtins::BuiltinClassKind::Enum => ClassKind::Enum,
    }
}

fn push_symbol(
    map: &mut HashMap<String, SymbolEntry>,
    key: String,
    fqn: &str,
    source: &str,
    origin: SourceKind,
) {
    map.entry(key)
        .and_modify(|e| {
            e.sources.push(source.to_string());
            e.origins.push(origin);
        })
        .or_insert_with(|| SymbolEntry {
            fqn: display_fqn(fqn),
            sources: vec![source.to_string()],
            origins: vec![origin],
        });
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_resolve::index_file;

    /// Build a project index from `(label, source)` files.
    fn project(files: &[(&str, &str)]) -> ProjectIndex {
        let mut idx = ProjectIndex::new();
        for (label, src) in files {
            let r = php_parser::parse(src);
            assert!(!r.has_errors(), "parse errors in {label}");
            idx.add_file(label, &index_file(&r.program, &r.interner));
        }
        idx
    }

    #[test]
    fn aggregates_symbols_across_files() {
        let idx = project(&[
            (
                "a.php",
                "<?php namespace App; class User {} function helper() {} const LIMIT = 1;",
            ),
            ("b.php", "<?php namespace App\\Http; class Controller {}"),
        ]);
        assert!(idx.has_class("App\\User"));
        assert!(idx.has_class("App\\Http\\Controller"));
        assert!(idx.has_function("App\\helper"));
        assert!(idx.has_constant("App\\LIMIT"));
        assert_eq!(idx.class_count(), 2);
    }

    #[test]
    fn class_and_function_lookups_are_case_insensitive() {
        let idx = project(&[(
            "a.php",
            "<?php namespace App; class User {} function Helper() {}",
        )]);
        assert!(idx.has_class("app\\user"));
        assert!(idx.has_class("APP\\USER"));
        assert!(idx.has_function("app\\HELPER"));
        // Canonical casing is preserved.
        assert_eq!(idx.class("app\\user").unwrap().fqn, "App\\User");
    }

    #[test]
    fn constants_are_case_sensitive() {
        let idx = project(&[("a.php", "<?php namespace App; const LIMIT = 1;")]);
        assert!(idx.has_constant("App\\LIMIT"));
        assert!(!idx.has_constant("App\\limit"));
    }

    #[test]
    fn leading_backslash_is_ignored_in_lookup() {
        let idx = project(&[("a.php", "<?php class Widget {}")]);
        assert!(idx.has_class("\\Widget"));
        assert!(idx.has_class("Widget"));
    }

    #[test]
    fn duplicate_declarations_are_tracked() {
        let idx = project(&[
            ("poly1.php", "<?php class JsonException {}"),
            ("poly2.php", "<?php class JsonException {}"),
        ]);
        let dups: Vec<_> = idx.duplicate_classes().collect();
        assert_eq!(dups.len(), 1);
        assert_eq!(dups[0].sources, ["poly1.php", "poly2.php"]);
    }

    #[test]
    fn builtins_are_loaded_with_correct_case_rules() {
        let idx = ProjectIndex::with_builtins();
        // Functions: case-insensitive.
        assert!(idx.has_function("strlen"));
        assert!(idx.has_function("STRLEN"));
        assert!(idx.has_function("array_map"));
        // Classes/interfaces: case-insensitive.
        assert!(idx.has_class("Exception"));
        assert!(idx.has_class("stdclass"));
        assert!(idx.has_class("Throwable"));
        // Constants: case-sensitive.
        assert!(idx.has_constant("PHP_EOL"));
        assert!(idx.has_constant("PHP_INT_MAX"));
        assert!(!idx.has_constant("php_eol"));
        // Nonsense isn't there.
        assert!(!idx.has_function("definitely_not_a_real_php_function"));
        // Sanity on scale.
        assert!(
            idx.function_count() > 1000,
            "expected many builtins, got {}",
            idx.function_count()
        );
    }

    #[test]
    fn user_files_merge_on_top_of_builtins() {
        let mut idx = ProjectIndex::with_builtins();
        let r = php_parser::parse("<?php namespace App; class User {}");
        idx.add_file("user.php", &index_file(&r.program, &r.interner));
        assert!(idx.has_class("App\\User"));
        assert!(idx.has_function("strlen"));
    }

    #[test]
    fn source_origins_distinguish_builtin_scan_and_analyzed_symbols() {
        let mut idx = ProjectIndex::with_builtins();
        assert!(idx
            .function("strlen")
            .unwrap()
            .origins
            .contains(&SourceKind::Builtin));

        let scan = php_parser::parse("<?php function strlen(): bool {} function helper(): void {}");
        assert!(!scan.has_errors());
        idx.add_file_as(
            "scan.php",
            &index_file(&scan.program, &scan.interner),
            SourceKind::Scan,
        );
        assert_eq!(
            idx.function("strlen").unwrap().origins,
            [SourceKind::Builtin]
        );
        assert_eq!(idx.function("helper").unwrap().origins, [SourceKind::Scan]);

        let analyzed = php_parser::parse("<?php function strlen(): bool {}");
        assert!(!analyzed.has_errors());
        idx.add_file(
            "analyzed.php",
            &index_file(&analyzed.program, &analyzed.interner),
        );
        assert_eq!(
            idx.function("strlen").unwrap().origins,
            [SourceKind::Builtin, SourceKind::Analyzed]
        );
    }
}
