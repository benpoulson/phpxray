//! M-C1: the **rule registry** — a uniform interface so the engine can select
//! rules by level and run them per file.
//!
//! Each rule is a pure function of a [`FileAnalysis`] (the per-file read-only
//! inputs) returning diagnostics. Rules carry a `level`; [`rules_for_level`] is
//! cumulative (level N runs every rule with `level <= N`), mirroring phpstan's
//! 0–9 dial. Because [`analyze_file`] takes only the file plus immutable indexes
//! and has no shared mutable state, the engine's per-file loop is trivially
//! parallelizable later (Phase 2).

use crate::facts::{
    ArrayFact, AssignmentFact, BinaryFact, CallFact, CastFact, EchoFact, FileFacts, ForeachFact,
    IndexFact, MethodCallFact, PrintFact, StaticCallFact, UnaryFact,
};
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

/// Coarse input families used by the internal rule scheduler. V2 keeps rule
/// execution order stable, but recording the input shape makes the next
/// node-dispatch/caching step mechanical.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum RuleInputKind {
    Declarations,
    Expressions,
    ScopedCalls,
    TypeMapSensitive,
    LocalBodyFlow,
}

#[derive(Clone, Copy)]
pub(crate) struct ScheduledRule {
    pub(crate) input: RuleInputKind,
    pub(crate) rule: &'static RuleEntry,
}

#[derive(Clone, Copy)]
pub(crate) struct ScheduledLocatedRule {
    pub(crate) input: RuleInputKind,
    pub(crate) rule: &'static LocatedRuleEntry,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum FactKind {
    FunctionCall,
    MethodCall,
    StaticCall,
    Binary,
    Unary,
    Cast,
    Array,
    Index,
    Assignment,
    Foreach,
    Echo,
    Print,
    Expression,
    Statement,
}

#[derive(Clone, Copy)]
pub(crate) enum FactRuleHandler {
    FunctionCall(fn(&FileAnalysis, &CallFact, &mut Vec<Diagnostic>)),
    MethodCall(fn(&FileAnalysis, &MethodCallFact, &mut Vec<Diagnostic>)),
    StaticCall(fn(&FileAnalysis, &StaticCallFact, &mut Vec<Diagnostic>)),
    Binary(fn(&FileAnalysis, &BinaryFact, &mut Vec<Diagnostic>)),
    Unary(fn(&FileAnalysis, &UnaryFact, &mut Vec<Diagnostic>)),
    Cast(fn(&FileAnalysis, &CastFact, &mut Vec<Diagnostic>)),
    Array(fn(&FileAnalysis, &ArrayFact, &mut Vec<Diagnostic>)),
    Index(fn(&FileAnalysis, &IndexFact, &mut Vec<Diagnostic>)),
    Assignment(fn(&FileAnalysis, &AssignmentFact, &mut Vec<Diagnostic>)),
    Foreach(fn(&FileAnalysis, &ForeachFact, &mut Vec<Diagnostic>)),
    Echo(fn(&FileAnalysis, &EchoFact, &mut Vec<Diagnostic>)),
    Print(fn(&FileAnalysis, &PrintFact, &mut Vec<Diagnostic>)),
    Expression(fn(&FileAnalysis, &Expr, &mut Vec<Diagnostic>)),
    #[allow(dead_code)]
    Statement(fn(&FileAnalysis, &php_ast::Stmt, &mut Vec<Diagnostic>)),
}

impl FactRuleHandler {
    fn kind(self) -> FactKind {
        match self {
            FactRuleHandler::FunctionCall(_) => FactKind::FunctionCall,
            FactRuleHandler::MethodCall(_) => FactKind::MethodCall,
            FactRuleHandler::StaticCall(_) => FactKind::StaticCall,
            FactRuleHandler::Binary(_) => FactKind::Binary,
            FactRuleHandler::Unary(_) => FactKind::Unary,
            FactRuleHandler::Cast(_) => FactKind::Cast,
            FactRuleHandler::Array(_) => FactKind::Array,
            FactRuleHandler::Index(_) => FactKind::Index,
            FactRuleHandler::Assignment(_) => FactKind::Assignment,
            FactRuleHandler::Foreach(_) => FactKind::Foreach,
            FactRuleHandler::Echo(_) => FactKind::Echo,
            FactRuleHandler::Print(_) => FactKind::Print,
            FactRuleHandler::Expression(_) => FactKind::Expression,
            FactRuleHandler::Statement(_) => FactKind::Statement,
        }
    }
}

pub(crate) struct FactRuleEntry {
    pub(crate) name: &'static str,
    pub(crate) level: u8,
    pub(crate) kind: FactKind,
    pub(crate) handler: FactRuleHandler,
}

impl FactRuleEntry {
    pub(crate) const fn new(
        name: &'static str,
        level: u8,
        kind: FactKind,
        handler: FactRuleHandler,
    ) -> Self {
        Self {
            name,
            level,
            kind,
            handler,
        }
    }
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

fn fact_rule_for_name(name: &str, level: u8) -> Option<&'static FactRuleEntry> {
    crate::rules::FACT_CATEGORY_RULES
        .iter()
        .flat_map(|cat| cat.iter())
        .find(|r| r.name == name && r.level <= level)
}

/// Scheduled ordinary rules, preserving the registry's diagnostic order.
pub(crate) fn scheduled_rules_for_level(level: u8) -> Vec<ScheduledRule> {
    rules_for_level(level)
        .map(|rule| ScheduledRule {
            input: classify_rule_input(rule.name),
            rule,
        })
        .collect()
}

/// Scheduled located rules, preserving the located registry's diagnostic order.
pub(crate) fn scheduled_located_rules_for_level(level: u8) -> Vec<ScheduledLocatedRule> {
    located_rules_for_level(level)
        .map(|rule| ScheduledLocatedRule {
            input: classify_located_rule_input(rule.name),
            rule,
        })
        .collect()
}

fn classify_located_rule_input(_name: &str) -> RuleInputKind {
    RuleInputKind::ScopedCalls
}

fn classify_rule_input(name: &str) -> RuleInputKind {
    if name == "unknown-symbol"
        || name.starts_with("class.")
        || name.starts_with("method.")
        || name.starts_with("property.")
        || name.starts_with("constant.")
        || name.starts_with("enumCase.")
        || name.starts_with("trait.")
        || name.starts_with("namespace.")
        || name.starts_with("name.")
        || name.starts_with("phpdoc.")
        || name.starts_with("generics.")
        || name.starts_with("missing.")
        || name.starts_with("pure.")
    {
        return RuleInputKind::Declarations;
    }

    if name == "return-type"
        || name.starts_with("deadCode.")
        || name.starts_with("variables.defined")
        || name.starts_with("variables.maybeUndefined")
        || name.contains("paramOut")
        || name.contains("tooWide")
        || name.contains("missingReturn")
    {
        return RuleInputKind::LocalBodyFlow;
    }

    if name.contains("argument")
        || name.contains("type")
        || name.contains("Type")
        || name.contains("nullable")
        || name.contains("union")
        || name.contains("assign")
        || name.contains("access")
        || name.contains("call")
        || name.contains("clone")
        || name.contains("iterable")
        || name.contains("mixed")
    {
        return RuleInputKind::TypeMapSensitive;
    }

    RuleInputKind::Expressions
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
    let scheduled = scheduled_rules_for_level(level);
    let mut slots: Vec<Vec<Diagnostic>> = vec![Vec::new(); scheduled.len()];
    let mut fact_rules: Vec<(usize, &'static FactRuleEntry)> = Vec::new();

    for (idx, scheduled) in scheduled.iter().enumerate() {
        if let Some(fact_rule) = fact_rule_for_name(scheduled.rule.name, level) {
            debug_assert_eq!(fact_rule.kind, fact_rule.handler.kind());
            fact_rules.push((idx, fact_rule));
        } else {
            let _input = scheduled.input;
            slots[idx].extend((scheduled.rule.run)(fa));
        }
    }

    dispatch_fact_rules(fa, &fact_rules, &mut slots);

    let mut out: Vec<LocatedDiagnostic> = slots
        .into_iter()
        .flatten()
        .map(LocatedDiagnostic::local)
        .collect();
    for scheduled in scheduled_located_rules_for_level(level) {
        let _input = scheduled.input;
        out.extend((scheduled.rule.run)(fa));
    }
    out
}

fn dispatch_fact_rules(
    fa: &FileAnalysis,
    fact_rules: &[(usize, &'static FactRuleEntry)],
    slots: &mut [Vec<Diagnostic>],
) {
    for kind in [
        FactKind::FunctionCall,
        FactKind::MethodCall,
        FactKind::StaticCall,
        FactKind::Binary,
        FactKind::Unary,
        FactKind::Cast,
        FactKind::Array,
        FactKind::Index,
        FactKind::Assignment,
        FactKind::Foreach,
        FactKind::Echo,
        FactKind::Print,
        FactKind::Expression,
        FactKind::Statement,
    ] {
        let active: Vec<_> = fact_rules
            .iter()
            .copied()
            .filter(|(_, rule)| rule.kind == kind)
            .collect();
        if active.is_empty() {
            continue;
        }
        dispatch_fact_kind(fa, kind, &active, slots);
    }
}

fn dispatch_fact_kind(
    fa: &FileAnalysis,
    kind: FactKind,
    active: &[(usize, &'static FactRuleEntry)],
    slots: &mut [Vec<Diagnostic>],
) {
    match kind {
        FactKind::FunctionCall => {
            for fact in fa.facts.function_calls() {
                for (slot, rule) in active {
                    let FactRuleHandler::FunctionCall(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
        FactKind::MethodCall => {
            for fact in fa.facts.method_calls() {
                for (slot, rule) in active {
                    let FactRuleHandler::MethodCall(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
        FactKind::StaticCall => {
            for fact in fa.facts.static_calls() {
                for (slot, rule) in active {
                    let FactRuleHandler::StaticCall(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
        FactKind::Binary => {
            for fact in fa.facts.binaries() {
                for (slot, rule) in active {
                    let FactRuleHandler::Binary(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
        FactKind::Unary => {
            for fact in fa.facts.unaries() {
                for (slot, rule) in active {
                    let FactRuleHandler::Unary(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
        FactKind::Cast => {
            for fact in fa.facts.casts() {
                for (slot, rule) in active {
                    let FactRuleHandler::Cast(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
        FactKind::Array => {
            for fact in fa.facts.arrays() {
                for (slot, rule) in active {
                    let FactRuleHandler::Array(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
        FactKind::Index => {
            for fact in fa.facts.indexes() {
                for (slot, rule) in active {
                    let FactRuleHandler::Index(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
        FactKind::Assignment => {
            for fact in fa.facts.assignments() {
                for (slot, rule) in active {
                    let FactRuleHandler::Assignment(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
        FactKind::Foreach => {
            for fact in fa.facts.foreaches() {
                for (slot, rule) in active {
                    let FactRuleHandler::Foreach(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
        FactKind::Echo => {
            for fact in fa.facts.echoes() {
                for (slot, rule) in active {
                    let FactRuleHandler::Echo(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
        FactKind::Print => {
            for fact in fa.facts.prints() {
                for (slot, rule) in active {
                    let FactRuleHandler::Print(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
        FactKind::Expression => {
            for fact in fa.facts.expressions() {
                for (slot, rule) in active {
                    let FactRuleHandler::Expression(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
        FactKind::Statement => {
            for fact in fa.facts.statements() {
                for (slot, rule) in active {
                    let FactRuleHandler::Statement(handler) = rule.handler else {
                        continue;
                    };
                    handler(fa, fact, &mut slots[*slot]);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{codes, located_codes};
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
    fn scheduler_preserves_order_and_records_input_kinds() {
        let raw: Vec<_> = rules_for_level(10).map(|r| r.name).collect();
        let scheduled = scheduled_rules_for_level(10);
        let scheduled_names: Vec<_> = scheduled.iter().map(|r| r.rule.name).collect();
        assert_eq!(scheduled_names, raw);
        assert!(scheduled
            .iter()
            .any(|r| r.input == RuleInputKind::Declarations));
        assert!(scheduled
            .iter()
            .any(|r| r.input == RuleInputKind::Expressions));
        assert!(scheduled
            .iter()
            .any(|r| r.input == RuleInputKind::TypeMapSensitive));
        assert!(scheduled
            .iter()
            .any(|r| r.input == RuleInputKind::LocalBodyFlow));

        let located = scheduled_located_rules_for_level(10);
        assert!(!located.is_empty());
        assert!(located
            .iter()
            .all(|r| r.input == RuleInputKind::ScopedCalls));
    }

    #[test]
    fn fact_rules_are_registry_compatible_and_scheduled_in_registry_order() {
        let registry: Vec<_> = rules_for_level(10).map(|r| r.name).collect();
        for fact_rule in crate::rules::FACT_CATEGORY_RULES
            .iter()
            .flat_map(|cat| cat.iter())
        {
            assert!(
                registry.contains(&fact_rule.name),
                "fact rule {} must have a matching RuleEntry",
                fact_rule.name
            );
            assert_eq!(fact_rule.kind, fact_rule.handler.kind());
        }

        let scheduled = scheduled_rules_for_level(10);
        let dispatched_names: Vec<_> = scheduled
            .iter()
            .filter(|scheduled| fact_rule_for_name(scheduled.rule.name, 10).is_some())
            .map(|scheduled| scheduled.rule.name)
            .collect();
        let registry_filtered: Vec<_> = registry
            .into_iter()
            .filter(|name| fact_rule_for_name(name, 10).is_some())
            .collect();
        assert_eq!(dispatched_names, registry_filtered);
    }

    fn analyze_level_4(fa: &FileAnalysis) -> Vec<Diagnostic> {
        analyze_file(fa, 4)
    }

    fn analyze_located_level_4(fa: &FileAnalysis) -> Vec<LocatedDiagnostic> {
        analyze_file_located(fa, 4)
    }

    #[test]
    fn dispatched_and_whole_file_diagnostics_flatten_in_registry_order() {
        let src = r#"<?php
            $a = [1 => 'first', 1 => 'second'];
            $b = (unset) $a;
            $c = (void) $a;
            $d = 1 === '1';
        "#;
        assert_eq!(
            codes(src, analyze_level_4),
            [
                "array.duplicateKey",
                "cast.unset",
                "cast.void",
                "identical.alwaysFalse",
            ]
        );
    }

    #[test]
    fn located_callback_context_still_runs_after_local_diagnostics() {
        let src = r#"<?php
            class User {}
            $a = [1 => 'first', 1 => 'second'];
            /** @param list<User> $users */
            function run(array $users): void {
                $mapped = array_map('cb', $users);
            }
            function cb($u): void {
                $u->missing();
            }
        "#;
        assert_eq!(
            located_codes(src, analyze_located_level_4),
            ["array.duplicateKey", "method.notFound"]
        );
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
