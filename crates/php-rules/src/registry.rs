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
use php_ast::{ClassDecl, Expr, FunctionDecl, Program};
use php_diagnostics::Diagnostic;
use php_index::ProjectIndex;
use php_infer::TypeMap;
use php_intern::Interner;
use php_reflect::{
    reflect_class, reflect_function, ClassReflection, FunctionReflection, ReflectionIndex,
};
use php_resolve::{ResolvedRef, Scope};
use php_types::{PhpVersion, Type};
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

/// Per-file memo of declared (AST) reflections, so the many rules that need a
/// class/function's reflected signature don't each re-parse its docblock. Keyed by
/// the declaration's address (stable and unique within one file). Single-threaded
/// per file (rules run sequentially over one [`FileAnalysis`]), so `RefCell` is
/// sound. **AST-declared** semantics: this reflects from source, deliberately
/// *not* the project [`ReflectionIndex`] (which may carry inferred/PHPDoc-grade
/// signature-inference enrichment) — rules that want the declared view rely on it.
#[derive(Default)]
pub struct ReflectCache {
    classes: RefCell<HashMap<usize, Arc<ClassReflection>>>,
    functions: RefCell<HashMap<usize, Arc<FunctionReflection>>>,
}

/// The read-only inputs a rule reads about one file. The shared project/reflection
/// indexes are borrowed (built once for the whole run).
///
/// # Invariant: one analyzed file per thread, no nested parallelism
///
/// Rules must not fan out with rayon (or otherwise move work to another thread)
/// *inside* the analysis of one file. Cross-file dependency recording
/// ([`php_resolve::depsrec`]) is a **thread-local**: the incremental engine
/// brackets each file with `depsrec::start()`/`finish()` on the worker thread
/// that analyzes it, so index lookups performed on a different thread are simply
/// not recorded. The failure mode is silent — that file under-records its
/// dependencies and watch mode then serves stale findings for it, with no crash
/// and no failing test. Parallelism belongs *across* files (which is where the
/// engines already put it), never within one.
///
/// `depsrec::start()` carries a `debug_assert!` for the nesting half of this.
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
    /// Inferred [`Facets`] (merged + native views) of every expression in the
    /// file, keyed by span. Read via [`type_of`](Self::type_of) /
    /// [`native_type_of`](Self::native_type_of); the native facet is present only
    /// under `treatPhpDocTypesAsCertain: false`.
    pub types: &'a TypeMap,
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
    /// phpstan's `checkUninitializedProperties` gate (default off) — enables the
    /// `property.uninitialized` rule.
    pub check_uninitialized_properties: bool,
    /// phpstan's `checkTooWideReturnTypesInProtectedAndPublicMethods` gate
    /// (default off) — extends `return.unusedType` to final non-private methods.
    pub check_too_wide_return_public: bool,
    /// When `true` (`--fix` runs only), rules that know a machine-applicable
    /// repair attach a [`php_diagnostics::DocTagFix`] to their diagnostics.
    /// Default `false`: normal runs pay nothing for fix computation.
    pub collect_fixes: bool,
    /// Call-site evidence for explicitly-typed bare `array` params (`--fix`
    /// runs only; see [`php_infer::ExplicitParamEvidence`]). `None` otherwise.
    pub iterable_param_evidence: Option<&'a php_infer::ExplicitParamEvidence>,
    /// User-configured always-terminating calls (`earlyTerminating*` config).
    pub terminators: std::sync::Arc<php_infer::Terminators>,
    /// Per-file memo of declared reflections (see [`ReflectCache`]). Default-init
    /// at every construction site; consume via [`FileAnalysis::reflect_class`] /
    /// [`FileAnalysis::reflect_function`].
    pub reflect_cache: ReflectCache,
}

impl FileAnalysis<'_> {
    /// Reflect a class-like declaration, memoized per file. Returns the same
    /// declared reflection (`Arc`-shared) for repeated calls on the same decl, so
    /// rules don't each re-parse its docblock. `fqn` is its resolved name.
    pub fn reflect_class(&self, scope: &Scope, fqn: &str, c: &ClassDecl) -> Arc<ClassReflection> {
        let key = std::ptr::from_ref(c) as usize;
        if let Some(r) = self.reflect_cache.classes.borrow().get(&key) {
            return Arc::clone(r);
        }
        let r = Arc::new(reflect_class(scope, self.interner, fqn, c));
        self.reflect_cache
            .classes
            .borrow_mut()
            .insert(key, Arc::clone(&r));
        r
    }

    /// Reflect a free-function declaration, memoized per file (see
    /// [`reflect_class`](Self::reflect_class)).
    pub fn reflect_function(&self, scope: &Scope, f: &FunctionDecl) -> Arc<FunctionReflection> {
        let key = std::ptr::from_ref(f) as usize;
        if let Some(r) = self.reflect_cache.functions.borrow().get(&key) {
            return Arc::clone(r);
        }
        let r = Arc::new(reflect_function(scope, self.interner, f));
        self.reflect_cache
            .functions
            .borrow_mut()
            .insert(key, Arc::clone(&r));
        r
    }

    /// The inferred type of expression `e` (`mixed` if it wasn't typed). Closure
    /// and arrow-fn bodies *are* recorded (params, `use` captures and `$this` are
    /// seeded), so this resolves inside them too; `mixed` means genuinely unknown
    /// (e.g. an untyped parameter), as anywhere else.
    pub fn type_of(&self, e: &Expr) -> Type {
        self.types
            .get(&php_span::NodeKey::of(e.span))
            .map(|f| f.merged.clone())
            .unwrap_or(Type::Mixed)
    }

    /// The native-only inferred type of `e` (`mixed` if untyped/PHPDoc-only).
    /// Reads the native facet of the single faceted map; it is only meaningful
    /// (and only consulted) under `treatPhpDocTypesAsCertain: false`.
    pub fn native_type_of(&self, e: &Expr) -> Type {
        self.types
            .get(&php_span::NodeKey::of(e.span))
            .map(|f| f.native().clone())
            .unwrap_or(Type::Mixed)
    }

    /// The type of `e` evaluated **on its own**, with no variable environment.
    ///
    /// Use this only where the expression genuinely has no surrounding flow to
    /// consult — a property default, a class-constant value, or a node the type
    /// map does not record (a `yield` operand's children). Any variable in `e`
    /// infers as `mixed`, since nothing here knows what it holds; literals,
    /// arrays, `new`, and calls still resolve.
    ///
    /// Prefer [`type_of`](Self::type_of) everywhere else: it reads the
    /// flow-sensitive map and is strictly better informed.
    pub fn type_of_isolated(&self, scope: &Scope, e: &Expr) -> Type {
        self.type_of_isolated_in(scope, None, e)
    }

    /// [`type_of_isolated`](Self::type_of_isolated) with a class context, so
    /// `self::CONST` / `static::` inside the expression resolve. Pass the FQN of
    /// the class the expression is written in.
    pub fn type_of_isolated_in(&self, scope: &Scope, class: Option<&str>, e: &Expr) -> Type {
        let mut ctx = php_infer::TypeCtx::new(self.reflection, scope, self.interner);
        ctx.class = class.map(ToString::to_string);
        ctx.infer(e)
    }

    /// [`type_of_isolated`](Self::type_of_isolated) restricted to native types,
    /// ignoring PHPDoc refinement. Only meaningful under
    /// `treatPhpDocTypesAsCertain: false`, like [`native_type_of`](Self::native_type_of).
    pub fn native_type_of_isolated(&self, scope: &Scope, e: &Expr) -> Type {
        let mut ctx = php_infer::TypeCtx::new(self.reflection, scope, self.interner);
        ctx.native = true;
        ctx.infer(e)
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
    /// mixes-in is present in the reflection index.
    ///
    /// **Member-existence rules MUST gate on this** (§8p): a class with an
    /// unindexed ancestor — a vendor class outside the analyzed/scanned paths —
    /// may inherit the member, so reporting it absent would be a false positive.
    /// Built-in classes *are* reflected (methods/properties/constants/hierarchy,
    /// §8m), so a built-in base like `ArrayObject` does **not** make a class
    /// unknown; an earlier version of this comment claimed otherwise.
    ///
    /// `@mixin` targets count as part of the hierarchy, deliberately: a class
    /// mixing in something unindexed can receive members from it. This is the
    /// only implementation of the guard — a mixin-blind variant used to exist
    /// alongside it in `classes.rs` and produced exactly that false positive.
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

/// A rule that opts into the shared node dispatcher, so many rules share one
/// traversal instead of each walking the file.
///
/// Carries only what cannot be derived: the `name` that joins it to its
/// [`RuleEntry`] (which owns the level) and the `handler` (which determines the
/// node kind). It used to repeat both the level and the kind, with tests
/// asserting the copies agreed — a disagreement would have made the rule run at
/// one level and dispatch at another. Not storing them is a stronger guarantee
/// than checking them.
pub(crate) struct FactRuleEntry {
    pub(crate) name: &'static str,
    pub(crate) handler: FactRuleHandler,
}

impl FactRuleEntry {
    pub(crate) const fn new(name: &'static str, handler: FactRuleHandler) -> Self {
        Self { name, handler }
    }

    /// The node kind this rule is dispatched on, determined by its handler.
    pub(crate) fn kind(&self) -> FactKind {
        self.handler.kind()
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

/// The dispatcher entry for a registry rule, if it has one. Callers iterate
/// `rules_for_level`, so the level filter has already been applied by the
/// `RuleEntry` that owns it.
fn fact_rule_for_name(name: &str) -> Option<&'static FactRuleEntry> {
    crate::rules::FACT_CATEGORY_RULES
        .iter()
        .flat_map(|cat| cat.iter())
        .find(|r| r.name == name)
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
    // One slot per rule, filled in registry order so diagnostic order is stable
    // regardless of which dispatch path a rule takes.
    let active: Vec<&'static RuleEntry> = rules_for_level(level).collect();
    let mut slots: Vec<Vec<Diagnostic>> = vec![Vec::new(); active.len()];
    let mut fact_rules: Vec<(usize, &'static FactRuleEntry)> = Vec::new();

    for (idx, rule) in active.iter().enumerate() {
        if let Some(fact_rule) = fact_rule_for_name(rule.name) {
            fact_rules.push((idx, fact_rule));
        } else {
            slots[idx].extend((rule.run)(fa));
        }
    }

    dispatch_fact_rules(fa, &fact_rules, &mut slots);

    let mut out: Vec<LocatedDiagnostic> = slots
        .into_iter()
        .flatten()
        .map(LocatedDiagnostic::local)
        .collect();
    for rule in located_rules_for_level(level) {
        out.extend((rule.run)(fa));
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
            .filter(|(_, rule)| rule.kind() == kind)
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
        }

        let dispatched_names: Vec<_> = rules_for_level(10)
            .filter(|rule| fact_rule_for_name(rule.name).is_some())
            .map(|rule| rule.name)
            .collect();
        let registry_filtered: Vec<_> = registry
            .into_iter()
            .filter(|name| fact_rule_for_name(name).is_some())
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
        // The test harness force-enables `check_implicit_mixed`, so the
        // strict-mixed rule (now scheduled at every level, gated on that flag)
        // also flags the untyped `$u->missing()` as `method.nonObject`. In the
        // real engine that flag is off below level max, so this extra finding is
        // a harness artifact, not an engine behavior change.
        assert_eq!(
            located_codes(src, analyze_located_level_4),
            ["array.duplicateKey", "method.nonObject", "method.notFound"]
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
        let types = php_infer::type_map(&reflection, &r.program, &r.interner, true);
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
            facts,
            php_version: PhpVersion::default(),
            treat_phpdoc_types_as_certain: true,
            report_maybes: true,
            check_nullables: true,
            check_explicit_mixed: true,
            check_implicit_mixed: true,
            check_uninitialized_properties: true,
            check_too_wide_return_public: true,
            collect_fixes: false,
            iterable_param_evidence: None,
            terminators: Default::default(),
            reflect_cache: Default::default(),
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

    /// The contract every `type_of_isolated` caller depends on: literals resolve,
    /// but a variable is `mixed` because there is no environment to consult.
    /// Callers use it only where that is the honest answer.
    #[test]
    fn isolated_inference_resolves_literals_but_not_variables() {
        crate::testutil::with_analysis(
            "<?php $bound = 42; $x = [42, $bound];",
            crate::testutil::Harness::default(),
            |_| {},
            |fa| {
                let scope = Scope::global();
                let mut seen = Vec::new();
                php_ast::walk::for_each_expr(fa.program, &mut |e| match &e.kind {
                    php_ast::ExprKind::Int(_) | php_ast::ExprKind::Variable(_) => {
                        seen.push((
                            fa.source[e.span.start as usize..e.span.end as usize].to_string(),
                            fa.type_of_isolated(&scope, e).to_string(),
                        ));
                    }
                    _ => {}
                });
                assert!(
                    seen.contains(&("42".to_string(), "42".to_string())),
                    "{seen:?}"
                );
                // `$bound` is `int` to the flow map, but isolated inference has no
                // environment, so it must answer `mixed`.
                assert!(
                    seen.iter()
                        .all(|(src, ty)| src != "$bound" || ty == "mixed"),
                    "{seen:?}"
                );
            },
        );
    }

    /// `self::` only resolves when the caller supplies the class the expression
    /// is written in — the whole reason both entry points exist.
    #[test]
    fn isolated_inference_needs_a_class_for_self_references() {
        crate::testutil::with_analysis(
            "<?php class C { const int N = 5; public function m() { $x = self::N; } }",
            crate::testutil::Harness::default(),
            |_| {},
            |fa| {
                let scope = Scope::global();
                let mut found = false;
                php_ast::walk::for_each_expr(fa.program, &mut |e| {
                    if !matches!(e.kind, php_ast::ExprKind::ClassConst { .. }) {
                        return;
                    }
                    found = true;
                    assert_eq!(fa.type_of_isolated(&scope, e).to_string(), "mixed");
                    assert_eq!(
                        fa.type_of_isolated_in(&scope, Some("\\C"), e).to_string(),
                        "5"
                    );
                });
                assert!(found, "expected a class-constant expression");
            },
        );
    }
}
