//! M-C2: the **analysis engine** — config in, findings out.
//!
//! Pipeline: discover files (per the config's `paths`/`exclude`/`extensions`) →
//! parse each once → build the shared, immutable project + reflection indexes
//! once → run the level-selected rules over each file. The per-file step
//! ([`php_rules::analyze_file`]) is pure over the file plus the borrowed indexes,
//! so it runs in parallel across the global Rayon worker pool.

use indicatif::{ProgressBar, ProgressStyle};
use php_config::{Config, ExcludeMatcher, Level, RuleOptions};
use php_diagnostics::Severity;
use php_index::{ProjectIndex, SourceKind as ProjectSourceKind};
use php_reflect::{ReflectionIndex, SourceKind as ReflectSourceKind};
use php_resolve::{index_file, resolve_references};
use php_rules::{analyze_file_located, FileAnalysis, FileFacts};
use php_span::LineIndex;
use rayon::prelude::*;
use std::collections::{BTreeMap, HashMap};
use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};
use walkdir::WalkDir;

pub mod baseline;
pub mod fix;
pub mod incremental;
pub mod report;
mod result_cache;
pub mod suppress;
pub mod watch;

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

#[derive(Debug, Clone)]
pub struct RunOptions {
    /// Show transient progress indicators on stderr when stderr is a terminal.
    pub progress: bool,
    /// Fire a desktop notification when there are errors (on notification
    /// only, not on clean passes). Only meaningful when combined with
    /// `--watch`.
    pub notify: bool,
    /// Collect internal wall-clock timings in [`Report::timings`].
    pub collect_timings: bool,
    /// Reuse final post-suppression reports for identical project reruns.
    pub use_result_cache: bool,
    /// Override the result cache directory. Defaults under the project root.
    pub cache_dir: Option<PathBuf>,
    /// Compute machine-applicable fixes for supported findings (`--fix` runs).
    pub collect_fixes: bool,
    /// Debug mode (`--debug`): print each analyzed file to stderr as analysis
    /// reaches it and bypass the result cache, so every run is a real run.
    pub debug: bool,
}

impl Default for RunOptions {
    fn default() -> Self {
        Self {
            notify: false,
            progress: false,
            collect_timings: false,
            use_result_cache: true,
            cache_dir: None,
            collect_fixes: false,
            debug: false,
        }
    }
}

/// Build the flow-terminator set from the config's `earlyTerminating*` lists
/// (method names are matched without re-checking the class — see
/// [`php_rules::Terminators`]).
fn terminators_from_config(config: &Config) -> std::sync::Arc<php_rules::Terminators> {
    std::sync::Arc::new(php_rules::Terminators {
        functions: config
            .early_terminating_function_calls
            .iter()
            .map(|f| f.trim_start_matches('\\').to_ascii_lowercase())
            .collect(),
        methods: config
            .early_terminating_method_calls
            .values()
            .flatten()
            .map(|m| m.to_ascii_lowercase())
            .collect(),
    })
}

/// The effective result-cache directory for a project: `RunOptions::cache_dir`
/// wins, then the config's `resultCachePath` (relative to the root), then the
/// default `.phpxray/cache/results-v1`.
pub fn result_cache_dir(config: &Config, root: &Path, override_dir: Option<&Path>) -> PathBuf {
    if let Some(d) = override_dir {
        return d.to_path_buf();
    }
    match &config.result_cache_path {
        Some(p) => root.join(p),
        None => result_cache::default_cache_dir(root),
    }
}

/// Read a source file, **lossily** decoding any non-UTF-8 bytes (legal in PHP
/// source — string literals can carry arbitrary bytes) so the file is actually
/// analyzed instead of being silently treated as empty. Returns an empty string
/// only on a real I/O error (the file was already discovered, so this is rare).
pub(crate) fn read_source_lossy(path: impl AsRef<std::path::Path>) -> String {
    std::fs::read(path)
        .map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
        .unwrap_or_default()
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
    // One shared, concurrent interner: every file parses into it (so symbols are
    // global), but the interner takes `&self`, so files parse in parallel across
    // rayon workers. `par_iter().map().collect()` preserves input order, keeping
    // the downstream finding order deterministic.
    let interner = php_intern::Interner::new();
    let inputs: Vec<_> = inputs.into_iter().collect();
    let counter = progress.counter(inputs.len(), "Parsing files");
    let parsed = inputs
        .into_par_iter()
        .map(|(path, source, analyze)| {
            let (program, diagnostics) = php_parser::parse_into(&source, &interner);
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
    /// A machine-applicable repair (`--fix` runs only). Byte offsets are valid
    /// in `path`'s analyzed source; only kept for findings local to their file.
    pub fix: Option<php_diagnostics::DocTagFix>,
}

/// The result of an analysis run.
#[derive(Debug, Clone, Default)]
pub struct Report {
    pub findings: Vec<Finding>,
    pub files_analyzed: usize,
    /// Scan-only files (indexed for symbols but not rule-checked), e.g. vendor.
    pub files_scanned: usize,
    pub timings: Option<AnalysisTimings>,
}

/// Internal timing breakdown for one analysis run. Durations are wall-clock and
/// intended for coarse performance comparisons, not stable assertions.
#[derive(Debug, Clone, Default)]
pub struct AnalysisTimings {
    pub cache_hit: bool,
    pub discovery: Duration,
    pub read: Duration,
    pub parse: Duration,
    pub index: Duration,
    pub infer_signatures: Duration,
    pub analyze: Duration,
    pub resolve: Duration,
    pub facts: Duration,
    pub type_map: Duration,
    pub rules: Duration,
}

#[derive(Debug, Clone, Copy, Default)]
struct FileTimings {
    resolve: Duration,
    facts: Duration,
    type_map: Duration,
    rules: Duration,
}

impl AnalysisTimings {
    fn add_file(&mut self, file: FileTimings) {
        self.resolve += file.resolve;
        self.facts += file.facts;
        self.type_map += file.type_map;
        self.rules += file.rules;
    }
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
    run_pipeline(config, root, options).0
}

/// The result of [`run_fix`]: what was repaired, plus the post-fix report.
pub struct FixReport {
    pub summary: fix::FixSummary,
    pub report: Report,
}

/// Run analysis with fix collection, write the repairs into the analyzed
/// sources, and repeat: each round's added types sharpen inference, which can
/// make previously-unfixable findings fixable (a `@return` written in round 1
/// becomes call-site evidence in round 2). Iterates until a round writes
/// nothing (monotone — a repaired declaration stops reporting — so this
/// terminates; `MAX_ROUNDS` is a backstop), then re-runs once so the returned
/// report reflects the repaired code. The result cache is bypassed throughout —
/// files change mid-run.
pub fn run_fix(config: &Config, root: &Path, options: RunOptions) -> FixReport {
    const MAX_ROUNDS: usize = 5;
    let fix_options = RunOptions {
        use_result_cache: false,
        collect_fixes: true,
        ..options.clone()
    };
    let mut summary = fix::FixSummary::default();
    for round in 0..MAX_ROUNDS {
        let (report, parsed) = run_pipeline(config, root, fix_options.clone());
        let sources: HashMap<String, String> = parsed
            .into_iter()
            .map(|f| (f.path, f.source))
            .collect();
        let round_summary = fix::apply_fixes(&report.findings, &sources, root);
        summary.findings_fixed += round_summary.findings_fixed;
        for path in round_summary.changed_paths.iter() {
            if !summary.changed_paths.contains(path) {
                summary.changed_paths.push(path.clone());
            }
        }
        summary.files_changed = summary.changed_paths.len();
        // Skip reasons are terminal (non-UTF-8, conflicts): report them once.
        if round == 0 {
            summary.files_skipped = round_summary.files_skipped;
        }
        if round_summary.files_changed == 0 {
            // Converged without writing this round: this report is already
            // accurate (fixes don't alter findings, only annotate them).
            let mut report = report;
            for f in &mut report.findings {
                f.fix = None;
            }
            return FixReport { summary, report };
        }
    }
    let rerun_options = RunOptions {
        use_result_cache: false,
        collect_fixes: false,
        ..options
    };
    let report = run_with_options(config, root, rerun_options);
    FixReport { summary, report }
}

/// The full single-shot pipeline. Returns the post-suppression report plus the
/// parsed files (empty on a result-cache hit) so callers that need the analyzed
/// sources afterwards — `--fix`'s disk-byte verification — can keep them.
fn run_pipeline(config: &Config, root: &Path, options: RunOptions) -> (Report, Vec<ParsedFile>) {
    let mut timings = options.collect_timings.then(AnalysisTimings::default);
    let progress = Progress::new(options.progress);
    let started = Instant::now();
    let discovery = progress.spinner("Discovering files");
    let files = discover_inputs(config, root);
    discovery.finish();
    if let Some(t) = &mut timings {
        t.discovery = started.elapsed();
    }
    let started = Instant::now();
    let read = progress.counter(files.len(), "Reading files");
    let inputs: Vec<(String, String, bool)> = files
        .iter()
        .map(|f| {
            let input = (
                rel_path(&f.path, root),
                read_source_lossy(&f.path),
                f.analyze,
            );
            read.inc(1);
            input
        })
        .collect();
    read.finish();
    if let Some(t) = &mut timings {
        t.read = started.elapsed();
    }
    let php_version = config
        .php_version
        .as_deref()
        .and_then(php_rules::PhpVersion::parse)
        .unwrap_or_default();
    let rule_options = config.level.rule_options();
    let analysis_options = AnalyzeParsedOptions {
        level: config.level.value(),
        php_version,
        treat_phpdoc_types_as_certain: config.treat_phpdoc_types_as_certain,
        infer_untyped_signatures: config.infer_untyped_signatures,
        rule_options,
        collect_fixes: options.collect_fixes,
        debug: options.debug,
        terminators: terminators_from_config(config),
    };
    let cache = (options.use_result_cache && !options.debug).then(|| {
        let cache_dir = result_cache_dir(config, root, options.cache_dir.as_deref());
        let cache_files: Vec<_> = inputs
            .iter()
            .map(|(path, source, analyze)| result_cache::CacheFileInput {
                path,
                source,
                analyze: *analyze,
            })
            .collect();
        let key = result_cache::key(config, root, php_version, rule_options, &cache_files);
        (cache_dir, key)
    });
    if let Some((cache_dir, key)) = &cache {
        if let Some(mut report) = result_cache::load(cache_dir, key) {
            if let Some(mut t) = timings {
                t.cache_hit = true;
                report.timings = Some(t);
            }
            return (report, Vec::new());
        }
    }
    let started = Instant::now();
    let (parsed, interner) = parse_files_with_mode_progress(inputs, &progress);
    if let Some(t) = &mut timings {
        t.parse = started.elapsed();
    }
    let mut report = analyze_parsed_progress(
        &parsed,
        &interner,
        analysis_options,
        &progress,
        timings.as_mut(),
    );
    report.timings = timings;
    let sources: HashMap<&str, &str> = parsed
        .iter()
        .map(|f| (f.path.as_str(), f.source.as_str()))
        .collect();
    let report = suppress::apply(
        report,
        &config.ignore,
        config.report_unmatched_ignored,
        &sources,
    );
    if let Some((cache_dir, key)) = &cache {
        result_cache::store(cache_dir, key, &report);
    }
    (report, parsed)
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
        AnalyzeParsedOptions {
            level,
            php_version,
            treat_phpdoc_types_as_certain,
            // Dev affordance (mirrors PHPXRAY_WATCH_FULL): `PHPXRAY_NO_INFER=1`
            // disables untyped-signature inference for batch tooling / audits.
            infer_untyped_signatures: std::env::var_os("PHPXRAY_NO_INFER").is_none(),
            rule_options: Level(level).rule_options(),
            collect_fixes: false,
            debug: false,
            terminators: Default::default(),
        },
        &Progress::hidden(),
        None,
    )
}

#[derive(Debug, Clone)]
struct AnalyzeParsedOptions {
    level: u8,
    php_version: php_rules::PhpVersion,
    treat_phpdoc_types_as_certain: bool,
    /// Run whole-project signature inference for untyped functions before rules.
    infer_untyped_signatures: bool,
    rule_options: RuleOptions,
    /// Attach machine-applicable fixes to supported diagnostics (`--fix` runs).
    collect_fixes: bool,
    /// Print each analyzed file to stderr as analysis reaches it (`--debug`).
    debug: bool,
    /// User-configured always-terminating calls (`earlyTerminating*` config).
    terminators: std::sync::Arc<php_rules::Terminators>,
}

fn analyze_parsed_progress(
    parsed: &[ParsedFile],
    interner: &php_intern::Interner,
    options: AnalyzeParsedOptions,
    progress: &Progress,
    mut timings: Option<&mut AnalysisTimings>,
) -> Report {
    // Build the shared immutable indexes once, over the one shared interner.
    let started = Instant::now();
    let indexing = progress.counter(parsed.len(), "Indexing files");
    let mut project = ProjectIndex::with_builtins_for(options.php_version);
    let mut reflection = ReflectionIndex::with_builtins_for(options.php_version);
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
        reflection.add_file_labeled_as(Some(&f.path), &f.program, interner, reflect_kind);
        indexing.inc(1);
    }
    // Cross-class `@phpstan-import-type` needs every class indexed first.
    reflection.resolve_type_imports();
    indexing.finish();
    if let Some(t) = &mut timings {
        t.index = started.elapsed();
    }

    // Whole-project pre-pass: synthesize signatures for fully untyped
    // functions/methods from their bodies and call sites, folding them into the
    // shared reflection index so all downstream inference/rules see them. Runs
    // sequentially before the parallel per-file analysis. Scan-only files
    // contribute call sites and bodies too (they were reflected above).
    if options.infer_untyped_signatures {
        let started = Instant::now();
        let inferring = progress.spinner("Inferring untyped signatures");
        let programs: Vec<&php_ast::Program> = parsed.iter().map(|f| &f.program).collect();
        php_infer::infer_and_apply(
            &mut reflection,
            &programs,
            interner,
            php_infer::InferOpts::default(),
        );
        inferring.finish();
        if let Some(t) = &mut timings {
            t.infer_signatures = started.elapsed();
        }
    }

    // `--fix` only: call-site evidence for explicitly-`array`-typed params (a
    // side map consumed by fix rendering — never applied to the reflection).
    let iterable_param_evidence = options.collect_fixes.then(|| {
        let programs: Vec<&php_ast::Program> = parsed.iter().map(|f| &f.program).collect();
        php_infer::explicit_iterable_param_evidence(&reflection, &programs, interner)
    });

    let analyzed_count = parsed.iter().filter(|f| f.analyze).count();
    let workers = rayon::current_num_threads();
    let analyzing = progress.counter(
        analyzed_count,
        format!("Analyzing files on {workers} workers"),
    );
    let ctx = AnalysisContext {
        interner,
        level: options.level,
        php_version: options.php_version,
        treat_phpdoc_types_as_certain: options.treat_phpdoc_types_as_certain,
        rule_options: options.rule_options,
        collect_fixes: options.collect_fixes,
        terminators: options.terminators.clone(),
        iterable_param_evidence: iterable_param_evidence.as_ref(),
        project: &project,
        reflection: &reflection,
        sources: parsed
            .iter()
            .filter(|f| f.analyze)
            .map(|f| (f.path.as_str(), f.source.as_str()))
            .collect(),
    };
    let started = Instant::now();
    let mut findings_by_file = parsed
        .par_iter()
        .enumerate()
        .filter(|(_, f)| f.analyze)
        .map(|(idx, f)| {
            if options.debug {
                eprintln!("{}", f.path);
            }
            let (findings, file_timings) = analyze_one_file(f, &ctx);
            analyzing.inc(1);
            (idx, findings, file_timings)
        })
        .collect::<Vec<_>>();
    findings_by_file.sort_by_key(|(idx, _, _)| *idx);
    if let Some(t) = &mut timings {
        t.analyze = started.elapsed();
        for (_, _, file_timings) in &findings_by_file {
            t.add_file(*file_timings);
        }
    }
    let findings = findings_by_file
        .into_iter()
        .flat_map(|(_, findings, _)| findings)
        .collect();
    analyzing.finish();
    Report {
        findings,
        files_analyzed: analyzed_count,
        files_scanned: parsed.len() - analyzed_count,
        timings: None,
    }
}

struct AnalysisContext<'a> {
    interner: &'a php_intern::Interner,
    level: u8,
    php_version: php_rules::PhpVersion,
    treat_phpdoc_types_as_certain: bool,
    rule_options: RuleOptions,
    collect_fixes: bool,
    terminators: std::sync::Arc<php_rules::Terminators>,
    iterable_param_evidence: Option<&'a php_infer::ExplicitParamEvidence>,
    project: &'a ProjectIndex,
    reflection: &'a ReflectionIndex,
    sources: HashMap<&'a str, &'a str>,
}

fn analyze_one_file(f: &ParsedFile, ctx: &AnalysisContext<'_>) -> (Vec<Finding>, FileTimings) {
    let mut findings = Vec::new();
    let mut timings = FileTimings::default();
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
            fix: None,
        });
    }

    let started = Instant::now();
    let refs = resolve_references(&f.program, ctx.interner);
    timings.resolve = started.elapsed();
    let started = Instant::now();
    let facts = FileFacts::new(&f.program, ctx.interner);
    timings.facts = started.elapsed();
    let started = Instant::now();
    // One faceted inference pass. The native facet is computed only when
    // `treatPhpDocTypesAsCertain` is off (otherwise nothing consults it), so the
    // common case is a single pass.
    let types = php_rules::type_map_with(
        ctx.reflection,
        &f.program,
        ctx.interner,
        !ctx.treat_phpdoc_types_as_certain,
        &ctx.terminators,
    );
    timings.type_map = started.elapsed();
    let fa = FileAnalysis {
        path: &f.path,
        source: &f.source,
        program: &f.program,
        interner: ctx.interner,
        project: ctx.project,
        reflection: ctx.reflection,
        resolved_refs: &refs,
        types: &types,
        facts,
        php_version: ctx.php_version,
        treat_phpdoc_types_as_certain: ctx.treat_phpdoc_types_as_certain,
        report_maybes: ctx.rule_options.report_maybes,
        check_nullables: ctx.rule_options.check_nullables,
        check_explicit_mixed: ctx.rule_options.check_explicit_mixed,
        check_implicit_mixed: ctx.rule_options.check_implicit_mixed,
        collect_fixes: ctx.collect_fixes,
        iterable_param_evidence: ctx.iterable_param_evidence,
        terminators: ctx.terminators.clone(),
        reflect_cache: Default::default(),
    };
    let mut target_line_indices: HashMap<String, LineIndex> = HashMap::new();
    let started = Instant::now();
    for located in analyze_file_located(&fa, ctx.level) {
        let target_path = located.path.as_deref().unwrap_or(&f.path);
        let Some(target_source) = ctx.sources.get(target_path) else {
            continue;
        };
        let target_line_index = target_line_indices
            .entry(target_path.to_string())
            .or_insert_with(|| LineIndex::new(target_source));
        let local = located.path.is_none();
        let d = located.diagnostic;
        let lc = target_line_index.line_col(d.primary.range().start as u32);
        findings.push(Finding {
            path: target_path.to_string(),
            line: lc.line,
            column: lc.col,
            message: d.message,
            identifier: d.code,
            severity: d.severity,
            // Cross-file located diagnostics carry spans for *this* file's
            // source, not the target's — never apply them there.
            fix: if local { d.fix } else { None },
        });
    }
    timings.rules = started.elapsed();
    (findings, timings)
}

#[derive(Debug, Clone)]
struct DiscoveredFile {
    path: PathBuf,
    analyze: bool,
}

/// File discovery for external tooling (examples/benches). Returns
/// `(root-relative path, absolute path, analyze)` triples in stable order.
#[doc(hidden)]
pub fn discover_files(config: &Config, root: &Path) -> Vec<(String, PathBuf, bool)> {
    discover_inputs(config, root)
        .into_iter()
        .map(|f| (rel_path(&f.path, root), f.path.clone(), f.analyze))
        .collect()
}

/// Collect analyzed and scan-only files. If a file is present in both sets, it
/// remains analyzed.
fn discover_inputs(config: &Config, root: &Path) -> Vec<DiscoveredFile> {
    let mut files: BTreeMap<String, DiscoveredFile> = BTreeMap::new();
    let hard_exclude = hard_exclude_matcher(config);
    let analyze_exclude = ExcludeMatcher::new(&config.exclude_paths.analyse);

    for path in discover_paths(&config.paths, config, root, &hard_exclude) {
        let analyze = !analyze_exclude.is_excluded(&rel_path(&path, root));
        insert_discovered(&mut files, root, path, analyze);
    }
    for path in discover_paths(&config.scan_paths, config, root, &hard_exclude) {
        insert_discovered(&mut files, root, path, false);
    }
    for entry_path in &config.scan_files {
        let path = root.join(entry_path);
        if path.is_file() && !hard_exclude.is_excluded(&rel_path(&path, root)) {
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
fn discover_paths(
    paths: &[String],
    config: &Config,
    root: &Path,
    hard_exclude: &ExcludeMatcher,
) -> Vec<PathBuf> {
    let wanted_ext = |p: &Path| {
        p.extension()
            .and_then(|e| e.to_str())
            .map(|e| config.extensions.iter().any(|w| w == e))
            .unwrap_or(false)
    };
    let mut out = Vec::new();
    for entry_path in paths {
        let base = root.join(entry_path);
        for found in WalkDir::new(&base)
            .into_iter()
            .filter_entry(|entry| {
                let rel = rel_path(entry.path(), root);
                !hard_exclude.is_excluded(&rel)
                    && !(entry.file_type().is_dir() && is_nested_vendor_dir(&rel))
            })
            .filter_map(Result::ok)
        {
            let p = found.path();
            if !p.is_file() || !wanted_ext(p) {
                continue;
            }
            if hard_exclude.is_excluded(&rel_path(p, root)) {
                continue;
            }
            out.push(p.to_path_buf());
        }
    }
    out.sort();
    out.dedup();
    out
}

fn hard_exclude_matcher(config: &Config) -> ExcludeMatcher {
    let mut patterns = config.exclude.clone();
    patterns.extend(config.exclude_paths.analyse_and_scan.iter().cloned());
    ExcludeMatcher::new(&patterns)
}

/// Whether `rel` is a `vendor` directory nested inside another `vendor` tree
/// (e.g. `vendor/rector/rector/vendor`). Composer never autoloads nested
/// vendor dirs — packages that bundle their own dependencies (rector, some
/// phars) ship *different versions* of libraries the project also uses
/// directly, and indexing both makes the nested copy shadow the real one
/// (symbol tables are last-wins). Pruning them matches runtime reality.
fn is_nested_vendor_dir(rel: &str) -> bool {
    let Some(prefix) = rel.strip_suffix("/vendor") else {
        return false;
    };
    prefix.split('/').any(|c| c == "vendor")
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
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn nested_vendor_dirs_are_pruned_from_discovery() {
        assert!(!is_nested_vendor_dir("vendor"));
        assert!(!is_nested_vendor_dir("src/vendor"));
        assert!(!is_nested_vendor_dir("vendor/nikic/php-parser"));
        assert!(is_nested_vendor_dir("vendor/rector/rector/vendor"));
        assert!(is_nested_vendor_dir("src/vendor/foo/vendor"));
        // Only the nested `vendor` dir itself is the prune point.
        assert!(!is_nested_vendor_dir("vendor/rector/rector/vendor/nikic"));

        let dir = std::env::temp_dir().join(format!(
            "phpxray-nested-vendor-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let real = dir.join("vendor/pkg/lib");
        let nested = dir.join("vendor/pkg/vendor/other/lib");
        fs::create_dir_all(&real).unwrap();
        fs::create_dir_all(&nested).unwrap();
        fs::write(real.join("A.php"), "<?php class A {}\n").unwrap();
        fs::write(nested.join("A.php"), "<?php class A { public function shadow(): void {} }\n")
            .unwrap();

        let config = Config::from_yaml("level: 0\npaths: []\nscanPaths:\n  - vendor\n").unwrap();
        let files: Vec<String> = discover_inputs(&config, &dir)
            .into_iter()
            .map(|f| rel_path(&f.path, &dir))
            .collect();
        assert_eq!(files, ["vendor/pkg/lib/A.php"], "nested copy must be pruned");

        let _ = fs::remove_dir_all(dir);
    }

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

    fn analyze_with_phpdoc_certainty(
        files: &[(&str, &str)],
        level: u8,
        treat_phpdoc_types_as_certain: bool,
    ) -> Report {
        let (parsed, interner) =
            parse_files(files.iter().map(|(p, s)| (p.to_string(), s.to_string())));
        analyze_parsed(
            &parsed,
            &interner,
            level,
            php_rules::PhpVersion::default(),
            treat_phpdoc_types_as_certain,
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
    fn level_7_reports_maybe_argument_and_return_types() {
        let files = [(
            "a.php",
            "<?php\nfunction takesString(string $s): void {}\nfunction f(string|int $x): string { takesString($x); return $x; }\n",
        )];
        let l6: Vec<_> = analyze(&files, 6)
            .findings
            .into_iter()
            .filter_map(|f| f.identifier)
            .collect();
        assert!(!l6.contains(&"argument.type"), "{l6:?}");
        assert!(!l6.contains(&"return.type"), "{l6:?}");

        let l7: Vec<_> = analyze(&files, 7)
            .findings
            .into_iter()
            .filter_map(|f| f.identifier)
            .collect();
        assert!(l7.contains(&"argument.type"), "{l7:?}");
        assert!(l7.contains(&"return.type"), "{l7:?}");
    }

    #[test]
    fn mixed_strictness_waits_for_level_9_and_max() {
        let files = [(
            "a.php",
            "<?php\nfunction takesInt(int $i): void {}\nfunction explicit(mixed $x): void { takesInt($x); }\nfunction implicit($x): void { takesInt($x); }\n",
        )];
        let l8 = analyze(&files, 8)
            .findings
            .into_iter()
            .filter(|f| f.identifier == Some("argument.type"))
            .count();
        assert_eq!(l8, 0);

        let l9 = analyze(&files, 9)
            .findings
            .into_iter()
            .filter(|f| f.identifier == Some("argument.type"))
            .count();
        assert_eq!(l9, 1);

        let max = analyze(&files, 10)
            .findings
            .into_iter()
            .filter(|f| f.identifier == Some("argument.type"))
            .count();
        assert_eq!(max, 2);
    }

    #[test]
    fn phpdoc_uncertain_suppresses_phpdoc_only_maybe_return() {
        let files = [(
            "a.php",
            "<?php\n/** @param string|int $x */\nfunction f($x): string { return $x; }\n",
        )];
        assert!(analyze_with_phpdoc_certainty(&files, 7, true)
            .findings
            .iter()
            .any(|f| f.identifier == Some("return.type")));
        assert!(analyze_with_phpdoc_certainty(&files, 7, false)
            .findings
            .iter()
            .all(|f| f.identifier != Some("return.type")));
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
    fn cross_file_literal_callback_reports_at_callback_body_path() {
        let report = analyze(
            &[
                ("src/User.php", "<?php class User {}"),
                (
                    "src/Use.php",
                    "<?php\n/** @param list<User> $users */\nfunction run(array $users): void { array_map('cb', $users); }\n",
                ),
                (
                    "src/Callback.php",
                    "<?php\nfunction cb($u): void { $u->missing(); }\n",
                ),
            ],
            0,
        );
        let finding = report
            .findings
            .iter()
            .find(|f| f.identifier == Some("method.notFound"))
            .unwrap();
        assert_eq!(finding.path, "src/Callback.php");
        assert_eq!(finding.line, 2);
    }

    #[test]
    fn cross_file_method_callback_reports_at_method_body_path() {
        let report = analyze(
            &[
                ("src/User.php", "<?php class User {}"),
                (
                    "src/Use.php",
                    "<?php\n/** @param list<User> $users */\nfunction run(array $users, Mapper $mapper): void { array_map([$mapper, 'toDto'], $users); }\n",
                ),
                (
                    "src/Mapper.php",
                    "<?php\nclass Mapper {\n    public function toDto($u): void {\n        echo $u->missing;\n    }\n}\n",
                ),
            ],
            0,
        );
        let finding = report
            .findings
            .iter()
            .find(|f| f.identifier == Some("property.notFound"))
            .unwrap();
        assert_eq!(finding.path, "src/Mapper.php");
        assert_eq!(finding.line, 4);
    }

    #[test]
    fn cross_file_callback_argument_and_return_type_use_target_path() {
        let report = analyze(
            &[
                ("src/User.php", "<?php class User {}"),
                (
                    "src/Use.php",
                    "<?php\n/** @param list<User> $users */\nfunction run(array $users): void { array_filter($users, 'cb'); }\n",
                ),
                (
                    "src/Callback.php",
                    "<?php\nfunction takes_string(string $s): void {}\nfunction cb($u): string {\n    takes_string($u);\n    return $u;\n}\n",
                ),
            ],
            5,
        );
        let arg = report
            .findings
            .iter()
            .find(|f| f.identifier == Some("argument.type"))
            .unwrap();
        assert_eq!(arg.path, "src/Callback.php");
        assert_eq!(arg.line, 4);
        let ret = report
            .findings
            .iter()
            .find(|f| f.identifier == Some("return.type"))
            .unwrap();
        assert_eq!(ret.path, "src/Callback.php");
        assert_eq!(ret.line, 5);
    }

    #[test]
    fn scan_only_callback_bodies_do_not_emit_context_diagnostics() {
        let report = analyze_with_modes(
            &[
                ("src/User.php", "<?php class User {}", true),
                (
                    "src/Use.php",
                    "<?php\n/** @param list<User> $users */\nfunction run(array $users): void { array_map('cb', $users); }\n",
                    true,
                ),
                (
                    "vendor/Callback.php",
                    "<?php\nfunction cb($u): void { $u->missing(); }\n",
                    false,
                ),
            ],
            0,
        );
        assert!(
            report
                .findings
                .iter()
                .all(|f| f.identifier != Some("method.notFound")),
            "{:?}",
            report.findings
        );
    }

    #[test]
    fn same_file_named_callback_still_reports_at_current_path() {
        let report = analyze(
            &[(
                "src/Use.php",
                "<?php\nclass User {}\n/** @param list<User> $users */\nfunction run(array $users): void { array_map('cb', $users); }\nfunction cb($u): void { $u->missing(); }\n",
            )],
            0,
        );
        let finding = report
            .findings
            .iter()
            .find(|f| f.identifier == Some("method.notFound"))
            .unwrap();
        assert_eq!(finding.path, "src/Use.php");
        assert_eq!(finding.line, 5);
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

    #[test]
    fn exclude_paths_analyse_demotes_files_to_scan_only() {
        let root = temp_dir("exclude-paths-analyse");
        write_file(&root, "app/use.php", "<?php new Vendor\\Thing();");
        write_file(
            &root,
            "vendor/Thing.php",
            "<?php namespace Vendor; class Thing {}",
        );
        write_file(&root, "vendor/bad.php", "<?php function broken( {}");
        write_file(&root, "storage/nope.php", "<?php function broken( {}");

        let config = Config::from_yaml(
            r#"
level: 9
paths:
  - .
excludePaths:
  analyse:
    - vendor
  analyseAndScan:
    - storage
"#,
        )
        .unwrap();

        let report = run(&config, &root);

        assert_eq!(report.files_analyzed, 1);
        assert!(
            report
                .findings
                .iter()
                .all(|f| !f.path.starts_with("vendor/")),
            "{:?}",
            report.findings
        );
        assert!(
            report
                .findings
                .iter()
                .all(|f| !f.path.starts_with("storage/")),
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

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn run_with_options_collects_internal_timings() {
        let root = temp_dir("timings");
        write_file(&root, "src/ok.php", "<?php class User {}\n");
        let config = Config::from_yaml("level: 0\npaths:\n  - src\n").unwrap();

        let report = run_with_options(
            &config,
            &root,
            RunOptions {
                collect_timings: true,
                ..RunOptions::default()
            },
        );

        assert_eq!(report.files_analyzed, 1);
        report.timings.as_ref().expect("timings should be present");

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn result_cache_hits_identical_project_rerun() {
        let root = temp_dir("cache-hit");
        write_file(&root, "src/bad.php", "<?php new MissingCachedClass();\n");
        let config = Config::from_yaml("level: 0\npaths:\n  - src\n").unwrap();
        let cache_dir = root.join("cache");

        let first = run_cached(&config, &root, &cache_dir);
        assert!(!first.timings.unwrap().cache_hit);
        assert_eq!(first.findings.len(), 1);

        let second = run_cached(&config, &root, &cache_dir);
        assert!(second.timings.unwrap().cache_hit);
        assert_eq!(second.findings.len(), 1);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn result_cache_source_content_change_misses() {
        let root = temp_dir("cache-source-change");
        write_file(&root, "src/bad.php", "<?php new MissingBeforeChange();\n");
        let config = Config::from_yaml("level: 0\npaths:\n  - src\n").unwrap();
        let cache_dir = root.join("cache");

        assert!(
            !run_cached(&config, &root, &cache_dir)
                .timings
                .unwrap()
                .cache_hit
        );
        assert!(
            run_cached(&config, &root, &cache_dir)
                .timings
                .unwrap()
                .cache_hit
        );

        write_file(&root, "src/bad.php", "<?php class MissingBeforeChange {}\n");
        let changed = run_cached(&config, &root, &cache_dir);
        assert!(!changed.timings.as_ref().unwrap().cache_hit);
        assert!(changed.findings.is_empty(), "{:?}", changed.findings);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn result_cache_rule_option_changes_miss() {
        let root = temp_dir("cache-rule-options");
        write_file(
            &root,
            "src/bad.php",
            "<?php\n/** @param string|int $x */\nfunction f($x): string { return $x; }\n",
        );
        let cache_dir = root.join("cache");
        let level6 = Config::from_yaml("level: 6\npaths:\n  - src\n").unwrap();
        let level7 = Config::from_yaml("level: 7\npaths:\n  - src\n").unwrap();

        assert!(
            !run_cached(&level6, &root, &cache_dir)
                .timings
                .unwrap()
                .cache_hit
        );
        assert!(
            run_cached(&level6, &root, &cache_dir)
                .timings
                .unwrap()
                .cache_hit
        );

        let l7 = run_cached(&level7, &root, &cache_dir);
        assert!(!l7.timings.as_ref().unwrap().cache_hit);
        assert!(l7
            .findings
            .iter()
            .any(|f| f.identifier == Some("return.type")));

        let phpdoc_uncertain =
            Config::from_yaml("level: 7\ntreatPhpDocTypesAsCertain: false\npaths:\n  - src\n")
                .unwrap();
        let uncertain = run_cached(&phpdoc_uncertain, &root, &cache_dir);
        assert!(!uncertain.timings.as_ref().unwrap().cache_hit);
        assert!(uncertain
            .findings
            .iter()
            .all(|f| f.identifier != Some("return.type")));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn result_cache_ignore_and_baseline_changes_miss() {
        let root = temp_dir("cache-ignore-baseline");
        write_file(&root, "src/bad.php", "<?php new MissingIgnoredClass();\n");
        write_file(
            &root,
            "baseline.yaml",
            "ignore:\n  - identifier: class.notFound\n    path: src/bad.php\n",
        );
        let cache_dir = root.join("cache");
        let base = Config::from_yaml("level: 0\npaths:\n  - src\n").unwrap();
        let ignored = Config::from_yaml(
            "level: 0\npaths:\n  - src\nignore:\n  - identifier: class.notFound\n",
        )
        .unwrap();
        let mut baselined =
            Config::from_yaml("level: 0\npaths:\n  - src\nbaseline: baseline.yaml\n").unwrap();
        baselined.ignore = ignored.ignore.clone();

        assert!(
            !run_cached(&base, &root, &cache_dir)
                .timings
                .unwrap()
                .cache_hit
        );

        let ignored_report = run_cached(&ignored, &root, &cache_dir);
        assert!(!ignored_report.timings.as_ref().unwrap().cache_hit);
        assert!(
            ignored_report.findings.is_empty(),
            "{:?}",
            ignored_report.findings
        );
        assert!(
            run_cached(&ignored, &root, &cache_dir)
                .timings
                .unwrap()
                .cache_hit
        );

        let baseline_report = run_cached(&baselined, &root, &cache_dir);
        assert!(!baseline_report.timings.as_ref().unwrap().cache_hit);
        write_file(
            &root,
            "baseline.yaml",
            "ignore:\n  - identifier: method.notFound\n    path: src/bad.php\n",
        );
        let changed_baseline = run_cached(&baselined, &root, &cache_dir);
        assert!(!changed_baseline.timings.as_ref().unwrap().cache_hit);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn result_cache_analyze_vs_scan_mode_change_misses() {
        let root = temp_dir("cache-scan-mode");
        write_file(
            &root,
            "vendor/bad.php",
            "<?php new MissingScanModeClass();\n",
        );
        let cache_dir = root.join("cache");
        let scan_only =
            Config::from_yaml("level: 0\npaths:\n  - src\nscanPaths:\n  - vendor\n").unwrap();
        let analyze_vendor = Config::from_yaml("level: 0\npaths:\n  - vendor\n").unwrap();

        let scan = run_cached(&scan_only, &root, &cache_dir);
        assert!(!scan.timings.as_ref().unwrap().cache_hit);
        assert_eq!(scan.files_analyzed, 0);
        assert!(scan.findings.is_empty(), "{:?}", scan.findings);

        let analyzed = run_cached(&analyze_vendor, &root, &cache_dir);
        assert!(!analyzed.timings.as_ref().unwrap().cache_hit);
        assert_eq!(analyzed.files_analyzed, 1);
        assert!(analyzed
            .findings
            .iter()
            .any(|f| f.identifier == Some("class.notFound")));

        let _ = fs::remove_dir_all(root);
    }

    fn run_cached(config: &Config, root: &Path, cache_dir: &Path) -> Report {
        run_with_options(
            config,
            root,
            RunOptions {
                collect_timings: true,
                cache_dir: Some(cache_dir.to_path_buf()),
                ..RunOptions::default()
            },
        )
    }

    fn write_file(root: &Path, path: &str, source: &str) {
        let path = root.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, source).unwrap();
    }

    fn temp_dir(label: &str) -> PathBuf {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir =
            std::env::temp_dir().join(format!("phpxray-{label}-{}-{now}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        dir
    }
}
