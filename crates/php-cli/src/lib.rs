//! M-C2: the **analysis engine** — config in, findings out.
//!
//! Pipeline: discover files (per the config's `paths`/`exclude`/`extensions`) →
//! parse each once → build the shared, immutable project + reflection indexes
//! once → run the level-selected rules over each file. The per-file step
//! ([`php_rules::analyze_file`]) is pure over the file plus the borrowed indexes,
//! so it runs in parallel across the global Rayon worker pool.

use indicatif::{ProgressBar, ProgressStyle};
use php_config::{Config, ExcludeMatcher, Level};
use php_diagnostics::Severity;
use php_index::{ProjectIndex, SourceKind as ProjectSourceKind};
use php_reflect::{ReflectionIndex, SourceKind as ReflectSourceKind};
use php_resolve::{index_file, resolve_references};
use php_rules::{analyze_file, FileAnalysis};
use php_span::LineIndex;
use rayon::prelude::*;
use std::collections::{BTreeMap, HashMap};
use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::time::Duration;
use walkdir::WalkDir;

pub mod baseline;
pub mod report;
pub mod suppress;

/// One parsed source file kept alive for analysis. The AST's symbols are interned
/// into a **shared, project-wide** interner (see [`parse_files`]) so they resolve
/// across files — the prerequisite for cross-file / interprocedural analysis.
pub struct ParsedFile {
    /// Display path (relative to the project root, forward slashes).
    pub path: String,
    /// Whether diagnostics should be reported for this file.
    pub analyze: bool,
    pub source: String,
    pub program: php_ast::Program,
    pub diagnostics: Vec<php_diagnostics::Diagnostic>,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct RunOptions {
    /// Show transient progress indicators on stderr when stderr is a terminal.
    pub progress: bool,
}

/// Parse `(path, source)` inputs into a single shared interner, returned alongside
/// the parsed files. Every file's symbols live in this one interner, so a symbol
/// from any file is resolvable while analyzing any other.
pub fn parse_files(
    inputs: impl IntoIterator<Item = (String, String)>,
) -> (Vec<ParsedFile>, php_intern::Interner) {
    parse_files_with_mode(
        inputs
            .into_iter()
            .map(|(path, source)| (path, source, true)),
    )
}

pub fn parse_files_with_mode(
    inputs: impl IntoIterator<Item = (String, String, bool)>,
) -> (Vec<ParsedFile>, php_intern::Interner) {
    parse_files_with_mode_progress(inputs, &Progress::hidden())
}

fn parse_files_with_mode_progress(
    inputs: impl IntoIterator<Item = (String, String, bool)>,
    progress: &Progress,
) -> (Vec<ParsedFile>, php_intern::Interner) {
    let mut interner = php_intern::Interner::new();
    let inputs: Vec<_> = inputs.into_iter().collect();
    let counter = progress.counter(inputs.len(), "Parsing files");
    let parsed = inputs
        .into_iter()
        .map(|(path, source, analyze)| {
            let (program, diagnostics) = php_parser::parse_into(&source, &mut interner);
            counter.inc(1);
            ParsedFile {
                path,
                analyze,
                source,
                program,
                diagnostics,
            }
        })
        .collect();
    counter.finish();
    (parsed, interner)
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
        self.findings
            .iter()
            .filter(|f| f.severity == Severity::Error)
            .count()
    }

    /// Whether any error-severity finding was reported.
    pub fn has_errors(&self) -> bool {
        self.findings.iter().any(|f| f.severity == Severity::Error)
    }
}

/// Run analysis described by `config`, resolving `paths` relative to `root`.
pub fn run(config: &Config, root: &Path) -> Report {
    run_with_options(config, root, RunOptions::default())
}

/// Run analysis with CLI/UI options such as progress reporting.
pub fn run_with_options(config: &Config, root: &Path, options: RunOptions) -> Report {
    let progress = Progress::new(options.progress);
    let discovery = progress.spinner("Discovering files");
    let files = discover_inputs(config, root);
    discovery.finish();
    let read = progress.counter(files.len(), "Reading files");
    let inputs: Vec<(String, String, bool)> = files
        .iter()
        .map(|f| {
            let input = (
                rel_path(&f.path, root),
                std::fs::read_to_string(&f.path).unwrap_or_default(),
                f.analyze,
            );
            read.inc(1);
            input
        })
        .collect();
    read.finish();
    let (parsed, interner) = parse_files_with_mode_progress(inputs, &progress);
    let php_version = config
        .php_version
        .as_deref()
        .and_then(php_rules::PhpVersion::parse)
        .unwrap_or_default();
    let report = analyze_parsed_progress(
        &parsed,
        &interner,
        config.level.value(),
        php_version,
        config.treat_phpdoc_types_as_certain,
        config.level.rule_options().check_nullables,
        &progress,
    );
    let sources: HashMap<&str, &str> = parsed
        .iter()
        .map(|f| (f.path.as_str(), f.source.as_str()))
        .collect();
    suppress::apply(
        report,
        &config.ignore,
        config.report_unmatched_ignored,
        &sources,
    )
}

/// Analyze already-parsed files at `level`. Pure over its inputs (no disk I/O) —
/// the testable core of [`run`], and the Phase-2 parallelism/caching boundary.
pub fn analyze_parsed(
    parsed: &[ParsedFile],
    interner: &php_intern::Interner,
    level: u8,
    php_version: php_rules::PhpVersion,
    treat_phpdoc_types_as_certain: bool,
) -> Report {
    analyze_parsed_progress(
        parsed,
        interner,
        level,
        php_version,
        treat_phpdoc_types_as_certain,
        Level(level).rule_options().check_nullables,
        &Progress::hidden(),
    )
}

fn analyze_parsed_progress(
    parsed: &[ParsedFile],
    interner: &php_intern::Interner,
    level: u8,
    php_version: php_rules::PhpVersion,
    treat_phpdoc_types_as_certain: bool,
    check_nullables: bool,
    progress: &Progress,
) -> Report {
    // Build the shared immutable indexes once, over the one shared interner.
    let indexing = progress.counter(parsed.len(), "Indexing files");
    let mut project = ProjectIndex::with_builtins_for(php_version);
    let mut reflection = ReflectionIndex::with_builtins_for(php_version);
    for f in parsed {
        let project_kind = if f.analyze {
            ProjectSourceKind::Analyzed
        } else {
            ProjectSourceKind::Scan
        };
        let reflect_kind = if f.analyze {
            ReflectSourceKind::Analyzed
        } else {
            ReflectSourceKind::Scan
        };
        project.add_file_as(&f.path, &index_file(&f.program, interner), project_kind);
        reflection.add_file_as(&f.program, interner, reflect_kind);
        indexing.inc(1);
    }
    indexing.finish();

    let analyzed_count = parsed.iter().filter(|f| f.analyze).count();
    let workers = rayon::current_num_threads();
    let analyzing = progress.counter(
        analyzed_count,
        format!("Analyzing files on {workers} workers"),
    );
    let ctx = AnalysisContext {
        interner,
        level,
        php_version,
        treat_phpdoc_types_as_certain,
        check_nullables,
        project: &project,
        reflection: &reflection,
    };
    let mut findings_by_file = parsed
        .par_iter()
        .enumerate()
        .filter(|(_, f)| f.analyze)
        .map(|(idx, f)| {
            let findings = analyze_one_file(f, &ctx);
            analyzing.inc(1);
            (idx, findings)
        })
        .collect::<Vec<_>>();
    findings_by_file.sort_by_key(|(idx, _)| *idx);
    let findings = findings_by_file
        .into_iter()
        .flat_map(|(_, findings)| findings)
        .collect();
    analyzing.finish();
    Report {
        findings,
        files_analyzed: analyzed_count,
    }
}

struct AnalysisContext<'a> {
    interner: &'a php_intern::Interner,
    level: u8,
    php_version: php_rules::PhpVersion,
    treat_phpdoc_types_as_certain: bool,
    check_nullables: bool,
    project: &'a ProjectIndex,
    reflection: &'a ReflectionIndex,
}

fn analyze_one_file(f: &ParsedFile, ctx: &AnalysisContext<'_>) -> Vec<Finding> {
    let mut findings = Vec::new();
    let line_index = LineIndex::new(&f.source);
    for d in &f.diagnostics {
        let lc = line_index.line_col(d.primary.start);
        findings.push(Finding {
            path: f.path.clone(),
            line: lc.line,
            column: lc.col,
            message: d.message.clone(),
            identifier: d.code,
            severity: d.severity,
        });
    }

    let refs = resolve_references(&f.program, ctx.interner);
    let types = php_rules::type_map(ctx.reflection, &f.program, ctx.interner);
    let native_types = php_rules::native_type_map(ctx.reflection, &f.program, ctx.interner);
    let fa = FileAnalysis {
        path: &f.path,
        source: &f.source,
        program: &f.program,
        interner: ctx.interner,
        project: ctx.project,
        reflection: ctx.reflection,
        resolved_refs: &refs,
        types: &types,
        native_types: &native_types,
        php_version: ctx.php_version,
        treat_phpdoc_types_as_certain: ctx.treat_phpdoc_types_as_certain,
        check_nullables: ctx.check_nullables,
    };
    for d in analyze_file(&fa, ctx.level) {
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
    findings
}

#[derive(Debug, Clone)]
struct DiscoveredFile {
    path: PathBuf,
    analyze: bool,
}

/// Collect analyzed and scan-only files. If a file is present in both sets, it
/// remains analyzed.
fn discover_inputs(config: &Config, root: &Path) -> Vec<DiscoveredFile> {
    let mut files: BTreeMap<String, DiscoveredFile> = BTreeMap::new();
    for path in discover_paths(&config.paths, config, root) {
        insert_discovered(&mut files, root, path, true);
    }
    for path in discover_paths(&config.scan_paths, config, root) {
        insert_discovered(&mut files, root, path, false);
    }
    for entry_path in &config.scan_files {
        let path = root.join(entry_path);
        if path.is_file() {
            insert_discovered(&mut files, root, path, false);
        }
    }
    files.into_values().collect()
}

fn insert_discovered(
    files: &mut BTreeMap<String, DiscoveredFile>,
    root: &Path,
    path: PathBuf,
    analyze: bool,
) {
    let key = rel_path(&path, root);
    files
        .entry(key)
        .and_modify(|f| f.analyze |= analyze)
        .or_insert(DiscoveredFile { path, analyze });
}

/// Collect every file under a configured path whose extension is configured and
/// whose root-relative path is not excluded.
fn discover_paths(paths: &[String], config: &Config, root: &Path) -> Vec<PathBuf> {
    let exclude = ExcludeMatcher::new(&config.exclude);
    let wanted_ext = |p: &Path| {
        p.extension()
            .and_then(|e| e.to_str())
            .map(|e| config.extensions.iter().any(|w| w == e))
            .unwrap_or(false)
    };
    let mut out = Vec::new();
    for entry_path in paths {
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
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

#[derive(Debug, Clone, Copy)]
struct Progress {
    enabled: bool,
}

impl Progress {
    fn new(enabled: bool) -> Self {
        Self {
            enabled: enabled && std::io::stderr().is_terminal(),
        }
    }

    fn hidden() -> Self {
        Self { enabled: false }
    }

    fn spinner(&self, message: impl Into<String>) -> ProgressStep {
        if !self.enabled {
            return ProgressStep::hidden();
        }
        let pb = ProgressBar::new_spinner();
        pb.set_style(
            ProgressStyle::with_template("{spinner:.green} {wide_msg} [{elapsed_precise}]")
                .unwrap(),
        );
        pb.set_message(message.into());
        pb.enable_steady_tick(Duration::from_millis(80));
        ProgressStep { pb: Some(pb) }
    }

    fn counter(&self, len: usize, message: impl Into<String>) -> ProgressStep {
        if !self.enabled {
            return ProgressStep::hidden();
        }
        let pb = ProgressBar::new(len as u64);
        pb.set_style(
            ProgressStyle::with_template(
                "{spinner:.green} {wide_msg} {pos}/{len} [{elapsed_precise}]",
            )
            .unwrap(),
        );
        pb.set_message(message.into());
        pb.enable_steady_tick(Duration::from_millis(80));
        ProgressStep { pb: Some(pb) }
    }
}

#[derive(Clone)]
struct ProgressStep {
    pb: Option<ProgressBar>,
}

impl ProgressStep {
    fn hidden() -> Self {
        Self { pb: None }
    }

    fn inc(&self, delta: u64) {
        if let Some(pb) = &self.pb {
            pb.inc(delta);
        }
    }

    fn finish(&self) {
        if let Some(pb) = &self.pb {
            pb.finish_and_clear();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Analyze `(path, src)` files at `level` over one shared interner.
    fn analyze(files: &[(&str, &str)], level: u8) -> Report {
        let (parsed, interner) =
            parse_files(files.iter().map(|(p, s)| (p.to_string(), s.to_string())));
        analyze_parsed(
            &parsed,
            &interner,
            level,
            php_rules::PhpVersion::default(),
            true,
        )
    }

    fn analyze_with_modes(files: &[(&str, &str, bool)], level: u8) -> Report {
        let (parsed, interner) = parse_files_with_mode(
            files
                .iter()
                .map(|(p, s, analyze)| (p.to_string(), s.to_string(), *analyze)),
        );
        analyze_parsed(
            &parsed,
            &interner,
            level,
            php_rules::PhpVersion::default(),
            true,
        )
    }

    #[test]
    fn reports_findings_with_locations_and_identifiers() {
        let report = analyze(
            &[(
                "src/Bad.php",
                "<?php\nfunction f(): int { return 'nope'; }\nnew TotallyMadeUp();\n",
            )],
            9,
        );
        assert_eq!(report.files_analyzed, 1);

        let ids: Vec<_> = report
            .findings
            .iter()
            .filter_map(|f| f.identifier)
            .collect();
        assert!(ids.contains(&"return.type"), "{ids:?}");
        assert!(ids.contains(&"class.notFound"), "{ids:?}");

        // Findings carry a 1-based line/column and the file path.
        let rt = report
            .findings
            .iter()
            .find(|f| f.identifier == Some("return.type"))
            .unwrap();
        assert_eq!(rt.path, "src/Bad.php");
        assert_eq!(rt.line, 2);
        assert!(report.has_errors());
    }

    #[test]
    fn level_gates_rules() {
        let files = [("a.php", "<?php\nfunction f(): int { return 'x'; }\n")];
        // Below level 3 the return-type rule is inactive.
        assert!(analyze(&files, 0)
            .findings
            .iter()
            .all(|f| f.identifier != Some("return.type")));
        assert!(analyze(&files, 3)
            .findings
            .iter()
            .any(|f| f.identifier == Some("return.type")));
    }

    #[test]
    fn missing_parameter_type_points_at_parameter() {
        let report = analyze(&[("a.php", "<?php\nfunction f($x) {}\n")], 6);
        let param = report
            .findings
            .iter()
            .find(|f| f.identifier == Some("missingType.parameter"))
            .unwrap();
        assert_eq!((param.line, param.column), (2, 12));
    }

    #[test]
    fn reports_parser_diagnostics() {
        let report = analyze(&[("bad.php", "<?php\nfunction f( {}\n")], 0);
        let parse = report
            .findings
            .iter()
            .find(|f| f.path == "bad.php" && f.identifier == Some("parse.expected"))
            .unwrap();
        assert_eq!(parse.line, 2);
        assert!(parse.column > 1, "{parse:?}");
        assert_eq!(parse.severity, Severity::Error);
        assert!(
            report.findings.iter().all(|f| f.identifier.is_some()),
            "{:?}",
            report.findings
        );
    }

    #[test]
    fn cross_file_class_resolution() {
        // A class defined in one file is known to another — no false unknown.
        let report = analyze(
            &[
                ("Animal.php", "<?php class Animal {}"),
                ("use.php", "<?php $a = new Animal();"),
            ],
            9,
        );
        assert!(
            !report
                .findings
                .iter()
                .any(|f| f.identifier == Some("class.notFound")),
            "{:?}",
            report.findings
        );
    }

    #[test]
    fn scan_only_files_are_indexed_but_not_reported() {
        let report = analyze_with_modes(
            &[
                ("src/use.php", "<?php new Vendor\\Thing();", true),
                (
                    "vendor/Thing.php",
                    "<?php namespace Vendor; class Thing {}",
                    false,
                ),
                ("vendor/bad.php", "<?php function broken( {}", false),
            ],
            9,
        );
        assert_eq!(report.files_analyzed, 1);
        assert!(
            report.findings.iter().all(|f| f.path != "vendor/bad.php"),
            "{:?}",
            report.findings
        );
        assert!(
            !report
                .findings
                .iter()
                .any(|f| f.identifier == Some("class.notFound")),
            "{:?}",
            report.findings
        );
    }
}
