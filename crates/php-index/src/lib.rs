//! A project-wide symbol index (reflection layer): aggregates the per-file
//! [`FileIndex`](php_resolve::FileIndex)es produced by name resolution into one
//! queryable map of every class/function/constant declared across the project.
//!
//! This is what the type system and cross-file rules build on. Lookups respect
//! PHP's case rules — class and function names are case-insensitive, constants
//! case-sensitive — while preserving each symbol's canonical (declared) casing.
//! Class hierarchies (`extends`/`implements`/used traits) can be walked
//! transitively for subtype queries.

use php_ast::ClassKind;
use php_resolve::FileIndex;
use std::collections::{HashMap, HashSet};

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
}

/// A function or constant known to the project.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolEntry {
    pub fqn: String,
    pub sources: Vec<String>,
}

/// How a parsed file participates in the project index.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceKind {
    /// User-facing analyzed source. May shadow a built-in symbol.
    Analyzed,
    /// Symbol-provider-only source. Must not shadow curated built-ins.
    Scan,
}

/// The aggregated symbol table for a whole project.
#[derive(Debug, Default, Clone)]
pub struct ProjectIndex {
    classes: HashMap<String, ClassEntry>,    // key: lowercased FQN
    functions: HashMap<String, SymbolEntry>, // key: lowercased FQN
    constants: HashMap<String, SymbolEntry>, // key: exact FQN (case-sensitive)
}

/// The committed manifest of built-in symbol names (see `xtask gen-stubs`).
const BUILTINS: &str = include_str!("../stubs/builtins.txt");

impl ProjectIndex {
    pub fn new() -> Self {
        Self::default()
    }

    /// A project index pre-populated with PHP's built-in functions, classes,
    /// interfaces, traits, enums and constants (names only — see `xtask
    /// gen-stubs`). Names are version-stable, so a single snapshot is safe for
    /// existence checks. Built-in *hierarchies* and *types* are intentionally not
    /// captured here; they come from version-aware stubs at the type-system stage.
    pub fn with_builtins() -> Self {
        let mut idx = Self::new();
        idx.load_builtins(BUILTINS);
        idx
    }

    fn load_builtins(&mut self, manifest: &str) {
        #[derive(Clone, Copy)]
        enum Sec {
            None,
            Functions,
            Classes(ClassKind),
            Constants,
        }
        let mut sec = Sec::None;
        for line in manifest.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if let Some(head) = line.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
                sec = match head {
                    "functions" => Sec::Functions,
                    "classes" => Sec::Classes(ClassKind::Class),
                    "interfaces" => Sec::Classes(ClassKind::Interface),
                    "traits" => Sec::Classes(ClassKind::Trait),
                    "enums" => Sec::Classes(ClassKind::Enum),
                    "constants" => Sec::Constants,
                    _ => Sec::None,
                };
                continue;
            }
            match sec {
                Sec::Functions => {
                    push_symbol(
                        &mut self.functions,
                        line.to_ascii_lowercase(),
                        line,
                        "<builtin>",
                    );
                }
                Sec::Constants => {
                    push_symbol(&mut self.constants, line.to_string(), line, "<builtin>")
                }
                Sec::Classes(kind) => {
                    self.classes
                        .entry(line.to_ascii_lowercase())
                        .or_insert_with(|| ClassEntry {
                            fqn: line.to_string(),
                            kind,
                            extends: Vec::new(),
                            implements: Vec::new(),
                            uses_traits: Vec::new(),
                            sources: vec!["<builtin>".to_string()],
                        });
                }
                Sec::None => {}
            }
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
                    .get(&c.fqn.to_ascii_lowercase())
                    .is_some_and(is_builtin_class)
            {
                continue;
            }
            match self.classes.entry(c.fqn.to_ascii_lowercase()) {
                std::collections::hash_map::Entry::Occupied(mut e) => {
                    e.get_mut().sources.push(source.to_string());
                }
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(ClassEntry {
                        fqn: c.fqn.clone(),
                        kind: c.kind,
                        extends: c.extends.clone(),
                        implements: c.implements.clone(),
                        uses_traits: c.uses_traits.clone(),
                        sources: vec![source.to_string()],
                    });
                }
            }
        }
        for f in &file.functions {
            let key = f.fqn.to_ascii_lowercase();
            if kind == SourceKind::Scan && self.functions.get(&key).is_some_and(is_builtin_symbol) {
                continue;
            }
            push_symbol(&mut self.functions, key, &f.fqn, source);
        }
        for k in &file.constants {
            if kind == SourceKind::Scan && self.constants.get(&k.fqn).is_some_and(is_builtin_symbol)
            {
                continue;
            }
            push_symbol(&mut self.constants, k.fqn.clone(), &k.fqn, source);
        }
    }

    // --- lookups (respecting PHP case rules) ----------------------------

    pub fn class(&self, fqn: &str) -> Option<&ClassEntry> {
        self.classes.get(&normalize(fqn).to_ascii_lowercase())
    }
    pub fn function(&self, fqn: &str) -> Option<&SymbolEntry> {
        self.functions.get(&normalize(fqn).to_ascii_lowercase())
    }
    pub fn constant(&self, fqn: &str) -> Option<&SymbolEntry> {
        self.constants.get(normalize(fqn))
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
    pub fn constant_count(&self) -> usize {
        self.constants.len()
    }

    /// Classes (and interfaces/traits/enums) declared in more than one file.
    pub fn duplicate_classes(&self) -> impl Iterator<Item = &ClassEntry> {
        self.classes.values().filter(|c| c.sources.len() > 1)
    }

    // --- hierarchy ------------------------------------------------------

    /// All transitive supertypes of `fqn` — parent classes, implemented
    /// interfaces, and used traits, reachable through the index. Excludes `fqn`
    /// itself; cycles and unknown links are handled gracefully.
    pub fn ancestors(&self, fqn: &str) -> Vec<String> {
        let mut out = Vec::new();
        let mut seen: HashSet<String> = HashSet::new();
        let mut stack: Vec<String> = self.supertypes(fqn);
        while let Some(name) = stack.pop() {
            let key = name.to_ascii_lowercase();
            if !seen.insert(key) {
                continue;
            }
            stack.extend(self.supertypes(&name));
            out.push(name);
        }
        out
    }

    /// Whether `sub` is `sup` or transitively extends/implements/uses it
    /// (case-insensitive, matching PHP class-name semantics).
    pub fn is_subclass_of(&self, sub: &str, sup: &str) -> bool {
        let sup = normalize(sup);
        if normalize(sub).eq_ignore_ascii_case(sup) {
            return true;
        }
        self.ancestors(sub)
            .iter()
            .any(|a| a.eq_ignore_ascii_case(sup))
    }

    /// The direct supertypes of a known class (its extends + implements + used
    /// traits); empty if the class is not in the index.
    fn supertypes(&self, fqn: &str) -> Vec<String> {
        match self.class(fqn) {
            Some(c) => c
                .extends
                .iter()
                .chain(&c.implements)
                .chain(&c.uses_traits)
                .cloned()
                .collect(),
            None => Vec::new(),
        }
    }
}

fn is_builtin_class(e: &ClassEntry) -> bool {
    e.sources.iter().any(|s| s == "<builtin>")
}

fn is_builtin_symbol(e: &SymbolEntry) -> bool {
    e.sources.iter().any(|s| s == "<builtin>")
}

fn push_symbol(map: &mut HashMap<String, SymbolEntry>, key: String, fqn: &str, source: &str) {
    map.entry(key)
        .and_modify(|e| e.sources.push(source.to_string()))
        .or_insert_with(|| SymbolEntry {
            fqn: fqn.to_string(),
            sources: vec![source.to_string()],
        });
}

/// Drop a single leading namespace separator so `\App\X` and `App\X` are one key.
fn normalize(fqn: &str) -> &str {
    fqn.strip_prefix('\\').unwrap_or(fqn)
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
    fn ancestors_span_extends_implements_and_traits_across_files() {
        let idx = project(&[
            ("base.php", "<?php namespace App; class Base implements Jsonable {} interface Jsonable {}"),
            ("model.php", "<?php namespace App; class User extends Base { use HasTimestamps; } trait HasTimestamps {}"),
        ]);
        let mut anc = idx.ancestors("App\\User");
        anc.sort();
        assert_eq!(anc, ["App\\Base", "App\\HasTimestamps", "App\\Jsonable"]);
    }

    #[test]
    fn is_subclass_of_is_transitive_and_reflexive() {
        let idx = project(&[(
            "a.php",
            "<?php namespace App; interface Arrayable {} class Base implements Arrayable {} class User extends Base {}",
        )]);
        assert!(idx.is_subclass_of("App\\User", "App\\User")); // reflexive
        assert!(idx.is_subclass_of("App\\User", "App\\Base")); // direct
        assert!(idx.is_subclass_of("App\\User", "App\\Arrayable")); // transitive via interface
        assert!(idx.is_subclass_of("app\\user", "APP\\BASE")); // case-insensitive
        assert!(!idx.is_subclass_of("App\\Base", "App\\User")); // not the other way
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
    fn ancestors_tolerate_unknown_links_and_cycles() {
        let idx = project(&[(
            "a.php",
            "<?php namespace App; class A extends B {} class B extends A {} class C extends Missing {}",
        )]);
        // Cyclic A/B: each is the other's ancestor, no infinite loop.
        assert!(idx.is_subclass_of("App\\A", "App\\B"));
        // Unknown parent is reported but not resolved further.
        assert_eq!(idx.ancestors("App\\C"), ["App\\Missing"]);
    }
}
