//! Test-only helpers for exercising a single rule against a PHP snippet.

use crate::FileAnalysis;
use php_diagnostics::Diagnostic;
use php_index::ProjectIndex;
use php_reflect::ReflectionIndex;
use php_resolve::{index_file, resolve_references};

/// Parse `src`, build the per-file analysis inputs, run `rule`, and return its
/// diagnostics. `src` must parse without errors.
pub(crate) fn run(src: &str, rule: fn(&FileAnalysis) -> Vec<Diagnostic>) -> Vec<Diagnostic> {
    let r = php_parser::parse(src);
    assert!(!r.has_errors(), "parse errors in test source: {src}");
    let mut project = ProjectIndex::with_builtins();
    project.add_file("test.php", &index_file(&r.program, &r.interner));
    let mut reflection = ReflectionIndex::new();
    reflection.add_file(&r.program, &r.interner);
    let refs = resolve_references(&r.program, &r.interner);
    let fa = FileAnalysis {
        path: "test.php",
        source: src,
        program: &r.program,
        interner: &r.interner,
        project: &project,
        reflection: &reflection,
        resolved_refs: &refs,
    };
    rule(&fa)
}

/// Run `rule` and return the error identifiers (`Diagnostic::code`) it emits.
pub(crate) fn codes(src: &str, rule: fn(&FileAnalysis) -> Vec<Diagnostic>) -> Vec<&'static str> {
    run(src, rule).into_iter().map(|d| d.code.unwrap_or("")).collect()
}
