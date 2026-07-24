//! Test-only helpers for exercising a single rule against a PHP snippet.

use crate::{FileAnalysis, FileFacts, LocatedDiagnostic, PhpVersion};
use php_diagnostics::Diagnostic;
use php_index::ProjectIndex;
use php_infer::type_map;
use php_reflect::ReflectionIndex;
use php_resolve::{index_file, resolve_references};

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
    rule: fn(&FileAnalysis) -> Vec<Diagnostic>,
    php_version: PhpVersion,
    configure: impl FnOnce(&mut FileAnalysis),
) -> Vec<Diagnostic> {
    let r = php_parser::parse(src);
    assert!(!r.has_errors(), "parse errors in test source: {src}");
    let mut project = ProjectIndex::with_builtins();
    project.add_file("test.php", &index_file(&r.program, &r.interner));
    let mut reflection = ReflectionIndex::with_builtins_for(php_version);
    reflection.add_file_labeled_as(
        Some("test.php"),
        &r.program,
        &r.interner,
        php_reflect::SourceKind::Analyzed,
    );
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
        php_version,
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
    configure(&mut fa);
    rule(&fa)
}

/// Like [`run`], but with whole-project untyped-signature inference applied to
/// the reflection index and `collect_fixes` enabled — the `--fix` environment.
/// For fix tests on the `missingType.*` rules.
pub(crate) fn run_fixes(src: &str, rule: fn(&FileAnalysis) -> Vec<Diagnostic>) -> Vec<Diagnostic> {
    let r = php_parser::parse(src);
    assert!(!r.has_errors(), "parse errors in test source: {src}");
    let mut project = ProjectIndex::with_builtins();
    project.add_file("test.php", &index_file(&r.program, &r.interner));
    let mut reflection = ReflectionIndex::with_builtins_for(PhpVersion::default());
    reflection.add_file_labeled_as(
        Some("test.php"),
        &r.program,
        &r.interner,
        php_reflect::SourceKind::Analyzed,
    );
    php_infer::infer_and_apply(
        &mut reflection,
        &[&r.program],
        &r.interner,
        php_infer::InferOpts::default(),
    );
    let evidence =
        php_infer::explicit_iterable_param_evidence(&reflection, &[&r.program], &r.interner);
    let refs = resolve_references(&r.program, &r.interner);
    let types = type_map(&reflection, &r.program, &r.interner, true);
    let facts = FileFacts::new(&r.program, &r.interner);
    let fa = FileAnalysis {
        path: "test.php",
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
        collect_fixes: true,
        iterable_param_evidence: Some(&evidence),
        terminators: Default::default(),
        reflect_cache: Default::default(),
    };
    rule(&fa)
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
        .map(|f| (f.tag, f.anchor, f.indent))
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
    let r = php_parser::parse(src);
    assert!(!r.has_errors(), "parse errors in test source: {src}");
    let mut project = ProjectIndex::with_builtins();
    project.add_file("test.php", &index_file(&r.program, &r.interner));
    let mut reflection = ReflectionIndex::with_builtins_for(php_version);
    reflection.add_file_labeled_as(
        Some("test.php"),
        &r.program,
        &r.interner,
        php_reflect::SourceKind::Analyzed,
    );
    let refs = resolve_references(&r.program, &r.interner);
    let types = type_map(&reflection, &r.program, &r.interner, true);
    let facts = FileFacts::new(&r.program, &r.interner);
    let fa = FileAnalysis {
        path: "test.php",
        source: src,
        program: &r.program,
        interner: &r.interner,
        project: &project,
        reflection: &reflection,
        resolved_refs: &refs,
        types: &types,
        facts,
        php_version,
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
    rule(&fa)
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
