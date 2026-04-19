//! M-C2: the **analysis engine** — config in, findings out.
//!
//! Pipeline: discover files (per the config's `paths`/`exclude`/`extensions`) →
//! parse each once → build the shared, immutable project + reflection indexes
//! once → run the level-selected rules over each file. The per-file step
//! ([`php_rules::analyze_file`]) is pure over the file plus the borrowed indexes,
//! so the loop here is single-threaded in Phase 1 but is the exact point a
//! `rayon` parallel map (and a result cache) drop in for Phase 2.

use php_config::{Config, ExcludeMatcher};
use php_diagnostics::Severity;
use php_index::ProjectIndex;
use php_reflect::ReflectionIndex;
use php_resolve::{index_file, resolve_references};
use php_rules::{analyze_file, FileAnalysis};
use php_span::LineIndex;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

pub mod baseline;
pub mod report;
pub mod suppress;

use std::collections::HashMap;

/// One parsed source file kept alive for analysis.
pub struct ParsedFile {
    /// Display path (relative to the project root, forward slashes).
    pub path: String,
    pub source: String,
    pub parse: php_parser::ParseResult,
}

impl ParsedFile {
    /// Parse `source` under display `path`.
    pub fn new(path: impl Into<String>, source: impl Into<String>) -> ParsedFile {
        let source = source.into();
        let parse = php_parser::parse(&source);
        ParsedFile { path: path.into(), source, parse }
    }
}

/// A single reported problem, located by line/column for display.
#[derive(Debug, Clone)]
pub struct Finding {
    pub path: String,
    pub line: u32,
    pub column: u32,
    pub message: String,
    /// phpstan-style identifier (e.g. `return.type`), if the rule set one.
    pub identifier: Option<&'static str>,
    pub severity: Severity,
}

/// The result of an analysis run.
#[derive(Debug, Clone, Default)]
pub struct Report {
    pub findings: Vec<Finding>,
    pub files_analyzed: usize,
}

impl Report {
    /// Number of error-severity findings.
    pub fn error_count(&self) -> usize {
        self.findings.iter().filter(|f| f.severity == Severity::Error).count()
    }

    /// Whether any error-severity finding was reported.
    pub fn has_errors(&self) -> bool {
        self.findings.iter().any(|f| f.severity == Severity::Error)
    }
}

/// Run analysis described by `config`, resolving `paths` relative to `root`.
pub fn run(config: &Config, root: &Path) -> Report {
    let files = discover_files(config, root);
    let parsed: Vec<ParsedFile> = files
        .iter()
        .map(|abs| {
            let source = std::fs::read_to_string(abs).unwrap_or_default();
            let display = rel_path(abs, root);
            ParsedFile::new(display, source)
        })
        .collect();
    let php_version = config
        .php_version
        .as_deref()
        .and_then(php_rules::PhpVersion::parse)
        .unwrap_or_default();
    let report =
        analyze_parsed(&parsed, config.level.value(), php_version, config.treat_phpdoc_types_as_certain);
    let sources: HashMap<&str, &str> =
        parsed.iter().map(|f| (f.path.as_str(), f.source.as_str())).collect();
    suppress::apply(report, &config.ignore, config.report_unmatched_ignored, &sources)
}

/// Analyze already-parsed files at `level`. Pure over its inputs (no disk I/O) —
/// the testable core of [`run`], and the Phase-2 parallelism/caching boundary.
pub fn analyze_parsed(
    parsed: &[ParsedFile],
    level: u8,
    php_version: php_rules::PhpVersion,
    treat_phpdoc_types_as_certain: bool,
) -> Report {
    // Build the shared immutable indexes once.
    let mut project = ProjectIndex::with_builtins();
    let mut reflection = ReflectionIndex::with_builtins();
    for f in parsed {
        project.add_file(&f.path, &index_file(&f.parse.program, &f.parse.interner));
        reflection.add_file(&f.parse.program, &f.parse.interner);
    }

    // Per-file analysis (the parallelizable map in Phase 2).
    let mut findings = Vec::new();
    for f in parsed {
        let refs = resolve_references(&f.parse.program, &f.parse.interner);
        let types = php_rules::type_map(&reflection, &f.parse.program, &f.parse.interner);
        let fa = FileAnalysis {
            path: &f.path,
            source: &f.source,
            program: &f.parse.program,
            interner: &f.parse.interner,
            project: &project,
            reflection: &reflection,
            resolved_refs: &refs,
            types: &types,
            php_version,
            treat_phpdoc_types_as_certain,
        };
        let line_index = LineIndex::new(&f.source);
        for d in analyze_file(&fa, level) {
            let lc = line_index.line_col(d.primary.range().start as u32);
            findings.push(Finding {
                path: f.path.clone(),
                line: lc.line,
                column: lc.col,
                message: d.message,
                identifier: d.code,
                severity: d.severity,
            });
        }
    }
    Report { findings, files_analyzed: parsed.len() }
}

/// Collect the files to analyze: every file under a configured `path` whose
/// extension is configured and whose root-relative path isn't excluded.
fn discover_files(config: &Config, root: &Path) -> Vec<PathBuf> {
    let exclude = ExcludeMatcher::new(&config.exclude);
    let wanted_ext = |p: &Path| {
        p.extension()
            .and_then(|e| e.to_str())
            .map(|e| config.extensions.iter().any(|w| w == e))
            .unwrap_or(false)
    };
    let mut out = Vec::new();
    for entry_path in &config.paths {
        let base = root.join(entry_path);
        for found in WalkDir::new(&base).into_iter().filter_map(Result::ok) {
            let p = found.path();
            if !p.is_file() || !wanted_ext(p) {
                continue;
            }
            if exclude.is_excluded(&rel_path(p, root)) {
                continue;
            }
            out.push(p.to_path_buf());
        }
    }
    out.sort();
    out.dedup();
    out
}

/// `path` relative to `root` (forward slashes); falls back to the full path.
fn rel_path(path: &Path, root: &Path) -> String {
    path.strip_prefix(root).unwrap_or(path).to_string_lossy().replace('\\', "/")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn file(path: &str, src: &str) -> ParsedFile {
        ParsedFile::new(path, src)
    }

    #[test]
    fn reports_findings_with_locations_and_identifiers() {
        let files = vec![file(
            "src/Bad.php",
            "<?php\nfunction f(): int { return 'nope'; }\nnew TotallyMadeUp();\n",
        )];
        let report = analyze_parsed(&files, 9, php_rules::PhpVersion::default(), true);
        assert_eq!(report.files_analyzed, 1);

        let ids: Vec<_> = report.findings.iter().filter_map(|f| f.identifier).collect();
        assert!(ids.contains(&"return.type"), "{ids:?}");
        assert!(ids.contains(&"class.notFound"), "{ids:?}");

        // Findings carry a 1-based line/column and the file path.
        let rt = report.findings.iter().find(|f| f.identifier == Some("return.type")).unwrap();
        assert_eq!(rt.path, "src/Bad.php");
        assert_eq!(rt.line, 2);
        assert!(report.has_errors());
    }

    #[test]
    fn level_gates_rules() {
        let files = vec![file("a.php", "<?php\nfunction f(): int { return 'x'; }\n")];
        // Below level 3 the return-type rule is inactive.
        assert!(analyze_parsed(&files, 0, php_rules::PhpVersion::default(), true).findings.iter().all(|f| f.identifier != Some("return.type")));
        assert!(analyze_parsed(&files, 3, php_rules::PhpVersion::default(), true).findings.iter().any(|f| f.identifier == Some("return.type")));
    }

    #[test]
    fn cross_file_class_resolution() {
        // A class defined in one file is known to another — no false unknown.
        let files = vec![
            file("Animal.php", "<?php class Animal {}"),
            file("use.php", "<?php $a = new Animal();"),
        ];
        let report = analyze_parsed(&files, 9, php_rules::PhpVersion::default(), true);
        assert!(
            !report.findings.iter().any(|f| f.identifier == Some("class.notFound")),
            "{:?}",
            report.findings
        );
    }
}
