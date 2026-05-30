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

/// Like [`run`] but with an explicit target PHP version (for version-gated rules).
pub(crate) fn run_version(
    src: &str,
    rule: fn(&FileAnalysis) -> Vec<Diagnostic>,
    php_version: PhpVersion,
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
    let types = type_map(&reflection, &r.program, &r.interner);
    let native_types = php_infer::native_type_map(&reflection, &r.program, &r.interner);
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
        native_types: &native_types,
        facts,
        php_version,
        treat_phpdoc_types_as_certain: true,
        report_maybes: true,
        check_nullables: true,
        check_explicit_mixed: true,
        check_implicit_mixed: true,
    };
    rule(&fa)
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
    let types = type_map(&reflection, &r.program, &r.interner);
    let native_types = php_infer::native_type_map(&reflection, &r.program, &r.interner);
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
        native_types: &native_types,
        facts,
        php_version,
        treat_phpdoc_types_as_certain: true,
        report_maybes: true,
        check_nullables: true,
        check_explicit_mixed: true,
        check_implicit_mixed: true,
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
