//! Test-only helpers for exercising a single rule against a PHP snippet.

use crate::{FileAnalysis, FileFacts, LocatedDiagnostic, PhpVersion};
use php_diagnostics::Diagnostic;
use php_index::ProjectIndex;
use php_infer::type_map;
use php_reflect::ReflectionIndex;
use php_resolve::{index_file, resolve_references};

/// How a test harness should configure the analysis.
///
/// The strictness switches come from [`php_config::Level::rule_options`] — the
/// same derivation the engine uses — rather than being hard-coded. The harness
/// used to force **all six** on, so every rule was exercised at a strictness no
/// default run has: `checkUninitializedProperties` and `checkTooWideReturnPublic`
/// are config-only and off unless asked for, and the other four only switch on at
/// levels 7/8/9/max. Tests that genuinely need the strict gates ask for them.
#[derive(Clone, Copy)]
pub(crate) struct Harness {
    pub(crate) php_version: PhpVersion,
    pub(crate) options: php_config::RuleOptions,
    pub(crate) collect_fixes: bool,
    /// Run whole-project untyped-signature inference first (the `--fix` shape).
    pub(crate) infer_signatures: bool,
}

impl Default for Harness {
    fn default() -> Self {
        Harness {
            php_version: PhpVersion::default(),
            // Level max: every level-derived switch on, both config-only switches
            // off — what `phpxray -l max` actually produces.
            options: php_config::Level::MAX.rule_options(),
            collect_fixes: false,
            infer_signatures: false,
        }
    }
}

impl Harness {
    /// The two config-only switches turned on, for rules that exist to serve them.
    pub(crate) fn strict(mut self) -> Self {
        self.options.check_uninitialized_properties = true;
        self.options.check_too_wide_return_public = true;
        self
    }

    /// The switches a given level produces, for level-gating coverage.
    pub(crate) fn at_level(mut self, level: u8) -> Self {
        self.options = php_config::Level(level).rule_options();
        self
    }
}

/// Parse `src`, build every per-file analysis input, and hand a [`FileAnalysis`]
/// to `f`.
///
/// The single place the harness constructs a `FileAnalysis` — adding a field is a
/// one-site edit here rather than three near-identical blocks.
pub(crate) fn with_analysis<R>(
    src: &str,
    h: Harness,
    configure: impl FnOnce(&mut FileAnalysis),
    f: impl FnOnce(&FileAnalysis) -> R,
) -> R {
    let r = php_parser::parse(src);
    assert!(!r.has_errors(), "parse errors in test source: {src}");
    let mut project = ProjectIndex::with_builtins();
    project.add_file("test.php", &index_file(&r.program, &r.interner));
    let mut reflection = ReflectionIndex::with_builtins_for(h.php_version);
    reflection.add_file_labeled_as(
        Some("test.php"),
        &r.program,
        &r.interner,
        php_reflect::SourceKind::Analyzed,
    );
    let evidence = h.infer_signatures.then(|| {
        php_infer::infer_and_apply(
            &mut reflection,
            &[&r.program],
            &r.interner,
            php_infer::InferOpts::default(),
        );
        php_infer::explicit_iterable_param_evidence(&reflection, &[&r.program], &r.interner)
    });
    let refs = resolve_references(&r.program, &r.interner);
    let types = type_map(&reflection, &r.program, &r.interner, true);
    let facts = FileFacts::new(&r.program, &r.interner);
    let mut fa = FileAnalysis {
        path: "test.php",
        source: src,
        program: &r.program,
        interner: &r.interner,
        project: &project,
        reflection: &reflection,
        resolved_refs: &refs,
        types: &types,
        facts,
        php_version: h.php_version,
        treat_phpdoc_types_as_certain: true,
        report_maybes: h.options.report_maybes,
        check_nullables: h.options.check_nullables,
        check_explicit_mixed: h.options.check_explicit_mixed,
        check_implicit_mixed: h.options.check_implicit_mixed,
        check_uninitialized_properties: h.options.check_uninitialized_properties,
        check_too_wide_return_public: h.options.check_too_wide_return_public,
        collect_fixes: h.collect_fixes,
        iterable_param_evidence: evidence.as_ref(),
        terminators: Default::default(),
        reflect_cache: Default::default(),
    };
    configure(&mut fa);
    f(&fa)
}

/// Parse `src`, build the per-file analysis inputs, run `rule`, and return its
/// diagnostics. `src` must parse without errors.
pub(crate) fn run(src: &str, rule: fn(&FileAnalysis) -> Vec<Diagnostic>) -> Vec<Diagnostic> {
    run_version(src, rule, PhpVersion::default())
}

pub(crate) fn run_with(
    src: &str,
    rule: fn(&FileAnalysis) -> Vec<Diagnostic>,
    configure: impl FnOnce(&mut FileAnalysis),
) -> Vec<Diagnostic> {
    run_version_with(src, rule, PhpVersion::default(), configure)
}

/// Like [`run`] but with an explicit target PHP version (for version-gated rules).
pub(crate) fn run_version(
    src: &str,
    rule: fn(&FileAnalysis) -> Vec<Diagnostic>,
    php_version: PhpVersion,
) -> Vec<Diagnostic> {
    run_version_with(src, rule, php_version, |_| {})
}

pub(crate) fn run_version_with(
    src: &str,
    rule: impl FnOnce(&FileAnalysis) -> Vec<Diagnostic>,
    php_version: PhpVersion,
    configure: impl FnOnce(&mut FileAnalysis),
) -> Vec<Diagnostic> {
    let h = Harness {
        php_version,
        ..Harness::default()
    };
    with_analysis(src, h, configure, rule)
}

/// Like [`run`], but with whole-project untyped-signature inference applied to
/// the reflection index and `collect_fixes` enabled — the `--fix` environment.
/// For fix tests on the `missingType.*` rules.
pub(crate) fn run_fixes(src: &str, rule: fn(&FileAnalysis) -> Vec<Diagnostic>) -> Vec<Diagnostic> {
    let h = Harness {
        collect_fixes: true,
        infer_signatures: true,
        ..Harness::default()
    };
    with_analysis(src, h, |_| {}, rule)
}

/// The `(tag, anchor, indent)` triples of the fixes [`run_fixes`] produced
/// (diagnostics without a fix are skipped).
pub(crate) fn fixes(
    src: &str,
    rule: fn(&FileAnalysis) -> Vec<Diagnostic>,
) -> Vec<(String, php_diagnostics::FixAnchor, String)> {
    run_fixes(src, rule)
        .into_iter()
        .filter_map(|d| d.fix)
        .filter_map(|f| match f {
            php_diagnostics::Fix::DocTag(f) => Some((f.tag, f.anchor, f.indent)),
            php_diagnostics::Fix::Replace(_) => None,
        })
        .collect()
}

/// The `Replace` fixes [`run_fixes`] produced, as `(span, replacement)` pairs.
pub(crate) fn replace_fixes(
    src: &str,
    rule: fn(&FileAnalysis) -> Vec<Diagnostic>,
) -> Vec<(php_span::Span, String)> {
    run_fixes(src, rule)
        .into_iter()
        .filter_map(|d| d.fix)
        .filter_map(|f| match f {
            php_diagnostics::Fix::Replace(r) => Some((r.span, r.replacement)),
            php_diagnostics::Fix::DocTag(_) => None,
        })
        .collect()
}

pub(crate) fn run_located(
    src: &str,
    rule: fn(&FileAnalysis) -> Vec<LocatedDiagnostic>,
) -> Vec<LocatedDiagnostic> {
    run_located_version(src, rule, PhpVersion::default())
}

pub(crate) fn run_located_version(
    src: &str,
    rule: fn(&FileAnalysis) -> Vec<LocatedDiagnostic>,
    php_version: PhpVersion,
) -> Vec<LocatedDiagnostic> {
    let h = Harness {
        php_version,
        ..Harness::default()
    };
    with_analysis(src, h, |_| {}, rule)
}

/// Like [`run`] but with the **config-only** strictness switches on
/// (`checkUninitializedProperties`, `checkTooWideReturnPublic`).
///
/// Those are off in every default run, so a rule that only exists to serve them
/// must ask for them explicitly rather than relying on the harness forcing them.
pub(crate) fn run_strict(
    src: &str,
    rule: impl FnOnce(&FileAnalysis) -> Vec<Diagnostic>,
) -> Vec<Diagnostic> {
    with_analysis(src, Harness::default().strict(), |_| {}, rule)
}

/// [`run_strict`], reduced to error identifiers.
pub(crate) fn codes_strict(
    src: &str,
    rule: impl FnOnce(&FileAnalysis) -> Vec<Diagnostic>,
) -> Vec<&'static str> {
    run_strict(src, rule)
        .into_iter()
        .map(|d| d.code.unwrap_or(""))
        .collect()
}

/// Identifiers a rule emits under the switches a given **level** produces —
/// for pinning level-gating behaviour.
pub(crate) fn codes_at_level(
    src: &str,
    rule: impl FnOnce(&FileAnalysis) -> Vec<Diagnostic>,
    level: u8,
) -> Vec<&'static str> {
    with_analysis(src, Harness::default().at_level(level), |_| {}, rule)
        .into_iter()
        .map(|d| d.code.unwrap_or(""))
        .collect()
}

/// Run `rule` and return the error identifiers (`Diagnostic::code`) it emits.
pub(crate) fn codes(src: &str, rule: fn(&FileAnalysis) -> Vec<Diagnostic>) -> Vec<&'static str> {
    run(src, rule)
        .into_iter()
        .map(|d| d.code.unwrap_or(""))
        .collect()
}

pub(crate) fn codes_with(
    src: &str,
    rule: fn(&FileAnalysis) -> Vec<Diagnostic>,
    configure: impl FnOnce(&mut FileAnalysis),
) -> Vec<&'static str> {
    run_with(src, rule, configure)
        .into_iter()
        .map(|d| d.code.unwrap_or(""))
        .collect()
}

pub(crate) fn located_codes(
    src: &str,
    rule: fn(&FileAnalysis) -> Vec<LocatedDiagnostic>,
) -> Vec<&'static str> {
    run_located(src, rule)
        .into_iter()
        .map(|d| d.diagnostic.code.unwrap_or(""))
        .collect()
}

/// Run *every* rule registered at `level` and return the error identifiers.
///
/// For regression tests that assert an identifier is emitted by exactly one
/// rule — twin rules emitting the same code is a recurring defect class.
pub(crate) fn all_codes_at(src: &str, level: u8) -> Vec<&'static str> {
    run_version_with(
        src,
        |fa| crate::analyze_file(fa, level),
        PhpVersion::default(),
        |_| {},
    )
    .into_iter()
    .map(|d| d.code.unwrap_or(""))
    .collect()
}

/// Like [`codes`] but with an explicit target PHP version (for version-gated rules).
#[allow(dead_code)]
pub(crate) fn codes_version(
    src: &str,
    rule: fn(&FileAnalysis) -> Vec<Diagnostic>,
    php_version: PhpVersion,
) -> Vec<&'static str> {
    run_version(src, rule, php_version)
        .into_iter()
        .map(|d| d.code.unwrap_or(""))
        .collect()
}

#[cfg(test)]
mod harness_tests {
    use super::Harness;

    /// The harness must mirror the engine's own level derivation.
    ///
    /// It used to hard-code all six strictness switches to `true`, so every rule
    /// was exercised at a strictness no real run produces — the two config-only
    /// switches are off unless configured, and the rest turn on at levels
    /// 7/8/9/max. That masked level-gating bugs and gave rules zero coverage
    /// under default gates.
    #[test]
    fn default_harness_matches_the_engines_max_level_options() {
        let h = Harness::default();
        assert_eq!(h.options, php_config::Level::MAX.rule_options());
        // The config-only switches are OFF by default, as in a real run.
        assert!(!h.options.check_uninitialized_properties);
        assert!(!h.options.check_too_wide_return_public);
        // ...and available explicitly for the rules that serve them.
        let strict = Harness::default().strict();
        assert!(strict.options.check_uninitialized_properties);
        assert!(strict.options.check_too_wide_return_public);
    }

    /// Level gating is the engine's, not the harness's invention.
    #[test]
    fn at_level_tracks_the_engines_thresholds() {
        for (level, maybes, nullables, explicit, implicit) in [
            (0, false, false, false, false),
            (6, false, false, false, false),
            (7, true, false, false, false),
            (8, true, true, false, false),
            (9, true, true, true, false),
            (10, true, true, true, true),
        ] {
            let o = Harness::default().at_level(level).options;
            assert_eq!(o.report_maybes, maybes, "level {level} report_maybes");
            assert_eq!(
                o.check_nullables, nullables,
                "level {level} check_nullables"
            );
            assert_eq!(
                o.check_explicit_mixed, explicit,
                "level {level} explicit mixed"
            );
            assert_eq!(
                o.check_implicit_mixed, implicit,
                "level {level} implicit mixed"
            );
        }
    }
}
