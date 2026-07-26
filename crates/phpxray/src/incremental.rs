//! **Incremental analysis session** for watch mode: keep per-file artifacts
//! (sources, symbol indexes, reflection artifacts, findings, recorded
//! dependencies) across passes and re-analyze only what a change can affect.
//!
//! # How invalidation works
//!
//! Every cross-file information channel in the analyzer flows through
//! `ProjectIndex`/`ReflectionIndex` lookups. While a file is analyzed, those
//! lookups are recorded (`php_resolve::depsrec`) as the file's dependency set,
//! split into *surface* dependencies (signatures/members/hierarchy — recorded
//! by `class()`/`function()`/member lookups) and *body* dependencies
//! (interprocedural inference and callback-context diagnostics — recorded by
//! `function_body()`/`method_body()`). This is sound by construction: type-flow
//! chains (`$repo->find()->getName()` consulting `User` without naming it),
//! callbacks referenced as plain strings, hierarchy walks, and `@mixin`s all
//! end in a recorded lookup.
//!
//! On a change, a file re-analyzes iff:
//! - it changed itself (or was added), or
//! - one of its **body** deps is declared in a changed file (the body may have
//!   changed), or
//! - one of its **surface** deps had its reflected surface actually change
//!   (reflections are span-free, so a body-only edit leaves surfaces equal —
//!   the common case stays fast), or
//! - it recorded a whole-index scan (global dep) and any surface changed, or
//! - it previously emitted findings *into* a changed file (their line/column
//!   mapping depends on that file's source).
//!
//! Anything the session can't account for (config changes affecting discovery,
//! file reads failing mid-pass, create/remove events) escalates to a full pass
//! — conservative over clever. Equivalence with the batch engine is enforced by
//! tests that diff entire reports after edit scenarios.

use crate::inputs::AnalysisInputs;
use crate::suppress::{self, CompiledIgnores, InlineIgnores};
use crate::{analyze_one_file, discover_inputs, rel_path, Finding, ParsedFile, Report};
use php_config::Config;
use php_index::ProjectIndex;
use php_reflect::{reflect_artifact, FileReflectionArtifact, ReflectionIndex};
use php_resolve::depsrec::{self, RecordedDeps};
use php_resolve::{index_file, FileIndex};
use rayon::prelude::*;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};

/// A changed file: `(root-relative path, absolute path, analyze flag)`.
type ChangedFile = (String, PathBuf, bool);
/// The result of diffing the on-disk project against the cache:
/// `(changed-or-added files, removed rel paths)`.
type FileDiff = (Vec<ChangedFile>, Vec<String>);

/// What the caller knows about the change that triggered this pass. `None`
/// means "no idea" (first pass, watcher restart) and forces full rediscovery.
#[derive(Debug, Clone, Default)]
pub struct ChangeHint {
    /// Absolute paths the OS watcher reported as changed.
    pub paths: Vec<PathBuf>,
    /// Whether any event could have added/removed/renamed files — forces
    /// rediscovery so the file set stays accurate.
    pub saw_creates_or_removes: bool,
}

/// Per-file cached state. The parsed AST is deliberately *not* kept — re-parsing
/// one file is ~sub-millisecond and dropping ASTs keeps a 20k-file session's
/// memory at sources + artifacts instead of whole syntax trees.
struct FileEntry {
    abs: PathBuf,
    analyze: bool,
    source: String,
    /// Per-file symbol table (project-index artifact).
    file_index: FileIndex,
    /// Per-file reflection artifact (`Arc`-shared; cheap to re-merge each pass).
    reflect_artifact: FileReflectionArtifact,
    /// Inline `@phpstan-ignore` prescan (suppression artifact).
    inline: InlineIgnores,
    /// Findings produced by analyzing THIS file (pre-suppression). May contain
    /// findings located at *other* files' paths (cross-file callback context).
    findings: Vec<Finding>,
    /// Symbol lookups recorded during this file's last analysis.
    deps: RecordedDeps,
    /// Target paths (≠ own) this file's findings were located at.
    emitted_into: Vec<String>,
}

/// Config fields that determine *which files* are discovered.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct DiscoveryFingerprint {
    paths: Vec<String>,
    scan_paths: Vec<String>,
    scan_files: Vec<String>,
    exclude: Vec<String>,
    exclude_analyse: Vec<String>,
    exclude_analyse_and_scan: Vec<String>,
    extensions: Vec<String>,
}

impl DiscoveryFingerprint {
    fn of(config: &Config) -> Self {
        Self {
            paths: config.paths.clone(),
            scan_paths: config.scan_paths.clone(),
            scan_files: config.scan_files.clone(),
            exclude: config.exclude.clone(),
            exclude_analyse: config.exclude_paths.analyse.clone(),
            exclude_analyse_and_scan: config.exclude_paths.analyse_and_scan.clone(),
            extensions: config.extensions.clone(),
        }
    }
}

/// Config inputs that determine analysis *results* (per-file findings).
///
/// Derived wholly from [`AnalysisInputs`] — the one registration point for
/// analysis inputs — so it can never drift from the result-cache key again. It
/// deliberately does NOT cover discovery inputs; those change the file *set* and
/// live in [`DiscoveryFingerprint`].
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct AnalysisFingerprint {
    /// Opaque digest of every analysis input; equality means "reuse findings".
    digest: String,
    /// Kept out of the digest because it is needed as a *value*: a change here
    /// rebuilds the builtin universe rather than just re-analyzing.
    php_version_raw: Option<String>,
}

impl AnalysisFingerprint {
    fn of(inputs: &AnalysisInputs) -> Self {
        Self {
            digest: inputs.fingerprint(),
            php_version_raw: inputs.php_version_raw.clone(),
        }
    }
}

/// A long-lived incremental analysis session (one per watched project).
pub struct Session {
    interner: php_intern::Interner,
    /// Keyed by root-relative path — BTreeMap order matches the batch engine's
    /// discovery order, so concatenated findings come out in the same order.
    files: BTreeMap<String, FileEntry>,
    /// Builtin-only index bases, built once and cloned per pass.
    project_base: ProjectIndex,
    reflect_base: ReflectionIndex,
    php_version: php_rules::PhpVersion,
    compiled_ignores: CompiledIgnores,
    ignore_fingerprint: Vec<php_config::IgnoreEntry>,
    discovery_fingerprint: DiscoveryFingerprint,
    analysis_fingerprint: AnalysisFingerprint,
    /// The signature-inference result of the previous pass. Diffed against the
    /// current pass's result so files depending on an *inferred* signature that
    /// changed are invalidated (declared-artifact diffing alone can't see it).
    prev_inferred: Option<php_reflect::InferredSignatures>,
    /// The `(display-path, source)` of each configured stub file as of the last
    /// pass. Stubs are re-read/parsed every pass and indexed last (winning over
    /// source); when their content changes, every analyzed file is re-checked
    /// (a stub edit can affect any symbol), keeping the session batch-equivalent.
    stub_sources: Vec<(String, String)>,
    /// The Laravel facade aliases (`alias` -> target FQN) as of the last pass.
    /// Re-collected every pass when `laravelAliases` is on (two small JSON/PHP
    /// files); diffing it feeds changed alias names into `changed_surface`, so a
    /// file that looked the alias up — including a *negative* lookup that
    /// produced `class.notFound` — is invalidated when the alias map moves.
    facade_aliases: Vec<(String, String)>,
    first_pass: bool,
    stats: PassStats,
}

/// What the most recent [`Session::run`] actually did — for status display
/// ("re-analyzed 3 of 1091 files") and for tests asserting selectivity.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PassStats {
    /// Files whose content changed (or were added) this pass.
    pub files_changed: usize,
    /// Files re-analyzed (changed + invalidated dependents).
    pub files_reanalyzed: usize,
    /// Total files in the project (analyzed + scan-only).
    pub files_total: usize,
}

impl Session {
    pub fn new(config: &Config) -> Self {
        let php_version = config
            .php_version
            .as_deref()
            .and_then(php_rules::PhpVersion::parse)
            .unwrap_or_default();
        Session {
            interner: php_intern::Interner::new(),
            files: BTreeMap::new(),
            project_base: ProjectIndex::with_builtins_for(php_version),
            reflect_base: ReflectionIndex::with_builtins_for(php_version),
            php_version,
            compiled_ignores: CompiledIgnores::compile(&config.ignore),
            ignore_fingerprint: config.ignore.clone(),
            discovery_fingerprint: DiscoveryFingerprint::of(config),
            // Left empty on purpose: the first pass analyzes everything anyway,
            // and resolving the real inputs needs the project root, which only
            // `run` has. The empty digest simply reads as "inputs changed".
            analysis_fingerprint: AnalysisFingerprint::default(),
            prev_inferred: None,
            stub_sources: Vec::new(),
            facade_aliases: Vec::new(),
            first_pass: true,
            stats: PassStats::default(),
        }
    }

    /// What the most recent pass did.
    pub fn last_pass(&self) -> PassStats {
        self.stats
    }

    /// Run one analysis pass, reusing everything the change allows.
    pub fn run(&mut self, config: &Config, root: &Path, hint: Option<&ChangeHint>) -> Report {
        // Config-level invalidation.
        let discovery_fp = DiscoveryFingerprint::of(config);
        let inputs = AnalysisInputs::resolve(config, root);
        let analysis_fp = AnalysisFingerprint::of(&inputs);
        let discovery_changed = discovery_fp != self.discovery_fingerprint;
        let analysis_changed = analysis_fp != self.analysis_fingerprint;
        if analysis_fp.php_version_raw != self.analysis_fingerprint.php_version_raw {
            // New builtin universe: rebuild the bases.
            self.php_version = config
                .php_version
                .as_deref()
                .and_then(php_rules::PhpVersion::parse)
                .unwrap_or_default();
            self.project_base = ProjectIndex::with_builtins_for(self.php_version);
            self.reflect_base = ReflectionIndex::with_builtins_for(self.php_version);
        }
        if config.ignore != self.ignore_fingerprint {
            self.compiled_ignores = CompiledIgnores::compile(&config.ignore);
            self.ignore_fingerprint = config.ignore.clone();
        }
        self.discovery_fingerprint = discovery_fp;
        self.analysis_fingerprint = analysis_fp;

        // Decide between a hinted pass (stat only the reported paths) and a
        // full rediscovery (walk the tree and diff everything).
        let was_first_pass = self.first_pass;
        let use_hint = !was_first_pass
            && !discovery_changed
            && hint.is_some_and(|h| !h.saw_creates_or_removes && !h.paths.is_empty());

        let (changed, removed) = if use_hint {
            match self.diff_hinted(hint.unwrap(), root) {
                Some(diff) => diff,
                // A hinted path was unknown or unreadable — fall back to a walk.
                None => {
                    trace_incremental(|| {
                        format!(
                            "hinted diff failed for {:?} — falling back to a full walk",
                            hint.unwrap().paths
                        )
                    });
                    self.diff_full(config, root)
                }
            }
        } else {
            self.diff_full(config, root)
        };
        self.first_pass = false;

        // Drop removed files, remembering their declared symbols.
        let mut changed_surface: HashSet<u64> = HashSet::new();
        let mut changed_body: HashSet<u64> = HashSet::new();
        // `changed_files` feeds two checks: "this file changed → re-analyze it"
        // (removed files are gone from `self.files`, so including them there is
        // harmless) and "I emitted findings INTO that file" — which MUST see
        // removed files too, or a producer keeps stale findings located at the
        // dead path.
        let mut changed_files: HashSet<String> =
            changed.iter().map(|(rel, _, _)| rel.clone()).collect();
        changed_files.extend(removed.iter().cloned());
        for rel in &removed {
            if let Some(old) = self.files.remove(rel) {
                for key in old.reflect_artifact.declared_keys() {
                    changed_surface.insert(depsrec::symbol_hash(key));
                    changed_body.insert(depsrec::symbol_hash(key));
                }
                note_file_index_names(&old.file_index, &mut changed_surface);
            }
        }

        // (Re)parse changed files; compute their new artifacts and the changed
        // symbol sets. Parsed programs are kept for this pass's analysis.
        let mut parsed_changed: HashMap<String, ParsedFile> = HashMap::new();
        for (rel, abs, analyze) in changed {
            // Non-UTF-8-tolerant read (matches the batch engine); a real I/O
            // error degrades to empty source.
            let source = crate::read_source_lossy(&abs);
            let (program, diagnostics) = php_parser::parse_into(&source, &self.interner);
            let kind = if analyze {
                php_reflect::SourceKind::Analyzed
            } else {
                php_reflect::SourceKind::Scan
            };
            let file_index = index_file(&program, &self.interner);
            let artifact = reflect_artifact(Some(&rel), &program, &self.interner, kind);
            let inline = suppress::inline_ignores(&source);

            // Symbol-level change detection against the previous artifacts.
            match self.files.get(&rel) {
                Some(old) => {
                    diff_artifacts(
                        &old.reflect_artifact,
                        &artifact,
                        &mut changed_surface,
                        &mut changed_body,
                    );
                    if old.file_index != file_index {
                        note_file_index_names(&old.file_index, &mut changed_surface);
                        note_file_index_names(&file_index, &mut changed_surface);
                    }
                    // Bodies in this file may have changed even when surfaces
                    // did not — everything it declares is body-changed.
                    for key in artifact.declared_keys() {
                        changed_body.insert(depsrec::symbol_hash(key));
                    }
                    for key in old.reflect_artifact.declared_keys() {
                        changed_body.insert(depsrec::symbol_hash(key));
                    }
                }
                None => {
                    // Added file: everything it declares is new.
                    for key in artifact.declared_keys() {
                        changed_surface.insert(depsrec::symbol_hash(key));
                        changed_body.insert(depsrec::symbol_hash(key));
                    }
                    note_file_index_names(&file_index, &mut changed_surface);
                }
            }

            let entry = self.files.entry(rel.clone()).or_insert_with(|| FileEntry {
                abs: abs.clone(),
                analyze,
                source: String::new(),
                file_index: FileIndex::default(),
                reflect_artifact: artifact.clone(),
                inline: suppress::inline_ignores(""),
                findings: Vec::new(),
                deps: RecordedDeps::default(),
                emitted_into: Vec::new(),
            });
            // A file demoted from analyzed to scan-only keeps its parse
            // artifacts (it is still indexed) but must lose everything that
            // belongs to *having been analyzed*. Nothing else clears these: the
            // invalid set skips non-analyzed entries, so the file is never
            // re-analyzed, while report assembly flat-maps the findings of every
            // entry — so its last findings would be reported forever, on every
            // pass, until the watcher restarted.
            if entry.analyze && !analyze {
                entry.findings.clear();
                entry.emitted_into.clear();
                entry.deps = RecordedDeps::default();
            }
            entry.abs = abs;
            entry.analyze = analyze;
            entry.source = source.clone();
            entry.file_index = file_index;
            entry.reflect_artifact = artifact;
            entry.inline = inline;

            parsed_changed.insert(
                rel.clone(),
                ParsedFile {
                    path: rel,
                    analyze,
                    stub: false,
                    source,
                    program,
                    diagnostics,
                },
            );
        }

        // Stub files: re-read + parsed fresh each pass (a handful of files; this
        // matches the batch engine, which re-reads them every run) and indexed
        // LAST so their reflection wins over project source. A change in stub
        // content forces every analyzed file to be re-checked (below), since a
        // stub can redefine any symbol.
        let stub_srcs = crate::stub_inputs(config, root);
        let stub_programs: Vec<(String, php_ast::Program)> = stub_srcs
            .iter()
            .map(|(path, source, _)| {
                (
                    path.clone(),
                    php_parser::parse_into(source, &self.interner).0,
                )
            })
            .collect();
        let stub_now: Vec<(String, String)> = stub_srcs
            .iter()
            .map(|(path, source, _)| (path.clone(), source.clone()))
            .collect();
        let stubs_changed = stubs_changed(was_first_pass, &stub_now, &self.stub_sources);
        self.stub_sources = stub_now;

        // Rebuild the shared indexes from cached artifacts (Arc merges).
        let mut project = self.project_base.clone();
        let mut reflection = self.reflect_base.clone();
        for (rel, e) in &self.files {
            let kind = if e.analyze {
                php_index::SourceKind::Analyzed
            } else {
                php_index::SourceKind::Scan
            };
            project.add_file_as(rel, &e.file_index, kind);
            reflection.add_artifact(&e.reflect_artifact);
        }
        // Stubs indexed last (win over source).
        crate::pipeline::index_stubs(
            &mut project,
            &mut reflection,
            &self.interner,
            &stub_programs,
        );
        let aliases_now = inputs.facade_aliases().to_vec();
        crate::pipeline::register_facade_aliases(&mut project, &aliases_now);
        // Any alias name that appeared, vanished, or changed target invalidates
        // the files that consulted it (alias lookups go through `ProjectIndex`,
        // so they are recorded surface deps like any other class lookup).
        if aliases_now != self.facade_aliases {
            for (alias, _) in aliases_now
                .iter()
                .filter(|e| !self.facade_aliases.contains(e))
                .chain(
                    self.facade_aliases
                        .iter()
                        .filter(|e| !aliases_now.contains(e)),
                )
            {
                changed_surface.insert(depsrec::symbol_hash(alias));
            }
            self.facade_aliases = aliases_now;
        }
        crate::pipeline::finalize_indexes(&mut reflection, &inputs.type_aliases);

        // Whole-project signature inference (untyped functions). It needs every
        // file's call sites, so each pass re-parses the whole tree (in parallel)
        // and recomputes inference in full, then **diffs the inferred signatures
        // against the previous pass**: a file whose findings depend on another
        // file's *inferred* signature recorded a surface dep on that symbol when
        // it analyzed, so feeding changed inferred keys into `changed_surface`
        // makes the ordinary invalidation below re-analyze it. (Declared-artifact
        // diffing alone cannot see inferred changes — a call-site edit in file C
        // can change file A's inferred signature without touching A.)
        if inputs.infer_untyped_signatures {
            let sources: Vec<&str> = self.files.values().map(|e| e.source.as_str()).collect();
            let programs: Vec<php_ast::Program> = sources
                .par_iter()
                .map(|src| php_parser::parse_into(src, &self.interner).0)
                .collect();
            // Stub programs contribute signatures too, and are ordered last to
            // mirror the batch engine (where stubs trail `parsed`).
            let prog_refs: Vec<&php_ast::Program> = programs
                .iter()
                .chain(stub_programs.iter().map(|(_, p)| p))
                .collect();
            let inferred =
                crate::pipeline::infer_signatures(&mut reflection, &prog_refs, &self.interner);
            if let Some(prev) = &self.prev_inferred {
                diff_inferred(prev, &inferred, &mut changed_surface);
            }
            self.prev_inferred = Some(inferred);
        } else {
            self.prev_inferred = None;
        }

        // Decide which files to (re)analyze.
        let any_surface_changed = !changed_surface.is_empty();
        let invalid: Vec<String> = self
            .files
            .iter()
            .filter(|(_, e)| e.analyze)
            .filter(|(rel, e)| {
                if analysis_changed || stubs_changed || changed_files.contains(*rel) {
                    return true;
                }
                if e.deps.global && any_surface_changed {
                    return true;
                }
                if changed_body.iter().any(|h| e.deps.body.contains(h)) {
                    return true;
                }
                if changed_surface.iter().any(|h| e.deps.surface.contains(h)) {
                    return true;
                }
                // Findings this file emitted into a changed file need their
                // line/column re-derived from the new source.
                if e.emitted_into.iter().any(|t| changed_files.contains(t)) {
                    return true;
                }
                false
            })
            .map(|(rel, _)| rel.clone())
            .collect();

        self.stats = PassStats {
            files_changed: changed_files.len(),
            files_reanalyzed: invalid.len(),
            files_total: self.files.len(),
        };

        // Re-parse invalidated-but-unchanged files (their cached ASTs were
        // dropped to save memory; re-parsing a handful of files is cheap).
        let mut to_analyze: Vec<ParsedFile> = Vec::with_capacity(invalid.len());
        for rel in &invalid {
            if let Some(p) = parsed_changed.remove(rel) {
                to_analyze.push(p);
                continue;
            }
            let e = &self.files[rel];
            let (program, diagnostics) = php_parser::parse_into(&e.source, &self.interner);
            to_analyze.push(ParsedFile {
                path: rel.clone(),
                analyze: e.analyze,
                stub: false,
                source: e.source.clone(),
                program,
                diagnostics,
            });
        }

        // Analyze in parallel, recording each file's dependencies.
        let ctx = crate::build_analysis_context(
            &inputs,
            &self.interner,
            &project,
            &reflection,
            self.files
                .iter()
                .filter(|(_, e)| e.analyze)
                .map(|(rel, e)| (rel.as_str(), e.source.as_str()))
                .collect(),
            None,
            false,
        );
        let results: Vec<(String, Vec<Finding>, RecordedDeps)> = to_analyze
            .par_iter()
            .map(|f| {
                depsrec::start();
                let (findings, _timings) = analyze_one_file(f, &ctx);
                let deps = depsrec::finish();
                (f.path.clone(), findings, deps)
            })
            .collect();
        drop(ctx);

        for (rel, findings, deps) in results {
            if let Some(e) = self.files.get_mut(&rel) {
                e.emitted_into = findings
                    .iter()
                    .filter(|f| f.path != rel)
                    .map(|f| f.path.clone())
                    .collect::<HashSet<_>>()
                    .into_iter()
                    .collect();
                e.findings = findings;
                e.deps = deps;
            }
        }

        // Assemble the report in engine order and apply suppression.
        let findings: Vec<Finding> = self
            .files
            .values()
            .flat_map(|e| e.findings.iter().cloned())
            .collect();
        let files_analyzed = self.files.values().filter(|e| e.analyze).count();
        // Analyzed files only — matching the batch engine. An inline ignore
        // suppresses findings in its own file, and a scan-only file produces
        // none; scanning them also turns a stray marker in vendored code into a
        // user-visible `ignore.parseError` on a path they excluded.
        let inline_refs: HashMap<&str, &InlineIgnores> = self
            .files
            .iter()
            .filter(|(_, e)| e.analyze)
            .map(|(rel, e)| (rel.as_str(), &e.inline))
            .collect();
        suppress::apply_compiled(
            Report {
                findings,
                files_analyzed,
                files_scanned: self.files.len() - files_analyzed,
                timings: None,
            },
            &self.compiled_ignores,
            config.report_unmatched_ignored,
            &inline_refs,
        )
    }

    /// Diff using only the hinted paths: returns `(changed, removed)` or `None`
    /// when a hinted path is outside the known file set (forces a full walk).
    fn diff_hinted(&self, hint: &ChangeHint, root: &Path) -> Option<FileDiff> {
        // The root must be canonicalized to match: event paths are canonical, so
        // comparing them against a symlinked or relative root makes every
        // `strip_prefix` fail, every path look unknown, and every keystroke fall
        // back to a full walk. On macOS this hits any project under `/tmp`
        // (-> `/private/tmp`).
        let root = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());
        let mut changed = Vec::new();
        for abs in &hint.paths {
            let canonical = abs.canonicalize().unwrap_or_else(|_| abs.clone());
            let rel = rel_path(&canonical, &root);
            let entry = self.files.get(&rel)?; // unknown path → full walk
                                               // Read bytes + lossy-decode (non-UTF-8 PHP is legal); a genuine I/O
                                               // error → `None` → full walk.
            let source = std::fs::read(&canonical)
                .ok()
                .map(|b| String::from_utf8_lossy(&b).into_owned())?;
            if source != entry.source {
                changed.push((rel, canonical, entry.analyze));
            }
        }
        Some((changed, Vec::new()))
    }

    /// Walk the project and diff the discovered set against the cache.
    fn diff_full(&self, config: &Config, root: &Path) -> FileDiff {
        let discovered = discover_inputs(config, root);
        let mut seen: HashSet<String> = HashSet::with_capacity(discovered.len());
        let mut changed = Vec::new();
        for f in discovered {
            let rel = rel_path(&f.path, root);
            seen.insert(rel.clone());
            let source = crate::read_source_lossy(&f.path);
            match self.files.get(&rel) {
                Some(e) if e.source == source && e.analyze == f.analyze => {}
                _ => changed.push((rel, f.path, f.analyze)),
            }
        }
        let removed = self
            .files
            .keys()
            .filter(|rel| !seen.contains(*rel))
            .cloned()
            .collect();
        (changed, removed)
    }
}

/// Record every name a `FileIndex` declares (classes, functions, constants)
/// into the changed-surface set. Used when symbol *existence* may have changed
/// — `has_class`/`has_function`/`has_constant` dependents must re-check.
/// Emit an incremental-analysis trace line when `PHPXRAY_DEBUG_INCREMENTAL` is
/// set. Falling back from a hinted diff to a full walk is a silent performance
/// cliff otherwise — the results stay correct, so nothing else surfaces it.
fn trace_incremental(msg: impl FnOnce() -> String) {
    if std::env::var_os("PHPXRAY_DEBUG_INCREMENTAL").is_some() {
        eprintln!("[incremental] {}", msg());
    }
}

/// Did the configured stub files' content change since the previous pass?
///
/// `was_first_pass` must be the value captured **before** `Session::run` clears
/// `self.first_pass`: on the very first pass `prev` is still empty, so a bare
/// content comparison always reports a change. (Currently masked — the first
/// pass analyzes everything regardless — but a wrong answer here silently
/// forces a whole-project re-analysis.)
fn stubs_changed(
    was_first_pass: bool,
    now: &[(String, String)],
    prev: &[(String, String)],
) -> bool {
    !was_first_pass && now != prev
}

fn note_file_index_names(fi: &FileIndex, out: &mut HashSet<u64>) {
    for c in &fi.classes {
        out.insert(depsrec::symbol_hash(&c.fqn));
    }
    for f in &fi.functions {
        out.insert(depsrec::symbol_hash(&f.fqn));
    }
    for k in &fi.constants {
        out.insert(depsrec::symbol_hash(&k.fqn));
    }
}

/// Diff two reflection artifacts symbol-by-symbol: any key present on one side
/// only, or whose reflection compares unequal, lands in `changed_surface`.
/// Reflections carry no spans, so a body-only edit produces an empty diff.
/// Diff two passes' inferred-signature results: any function FQN (or method's
/// declaring class) whose inferred signature was added, removed, or changed lands
/// in `changed_surface`. The hashes match the surface deps dependents recorded
/// when they looked the symbol up (`function()` notes the FQN, member lookups
/// note the class key — both via the case-normalizing `symbol_hash`).
fn diff_inferred(
    old: &php_reflect::InferredSignatures,
    new: &php_reflect::InferredSignatures,
    changed_surface: &mut HashSet<u64>,
) {
    for (fqn, sig) in &old.fns {
        if new.fns.get(fqn) != Some(sig) {
            changed_surface.insert(depsrec::symbol_hash(fqn));
        }
    }
    for fqn in new.fns.keys() {
        if !old.fns.contains_key(fqn) {
            changed_surface.insert(depsrec::symbol_hash(fqn));
        }
    }
    for ((class_fqn, method), sig) in &old.methods {
        if new.methods.get(&(class_fqn.clone(), method.clone())) != Some(sig) {
            changed_surface.insert(depsrec::symbol_hash(class_fqn));
        }
    }
    for (class_fqn, method) in new.methods.keys() {
        if !old
            .methods
            .contains_key(&(class_fqn.clone(), method.clone()))
        {
            changed_surface.insert(depsrec::symbol_hash(class_fqn));
        }
    }
}

fn diff_artifacts(
    old: &FileReflectionArtifact,
    new: &FileReflectionArtifact,
    changed_surface: &mut HashSet<u64>,
    _changed_body: &mut HashSet<u64>,
) {
    let old_classes: HashMap<&str, _> = old.class_reflections().collect();
    let new_classes: HashMap<&str, _> = new.class_reflections().collect();
    for (key, r) in &old_classes {
        match new_classes.get(key) {
            Some(n) if n == r => {}
            _ => {
                changed_surface.insert(depsrec::symbol_hash(key));
            }
        }
    }
    for key in new_classes.keys() {
        if !old_classes.contains_key(key) {
            changed_surface.insert(depsrec::symbol_hash(key));
        }
    }
    let old_fns: HashMap<&str, _> = old.function_reflections().collect();
    let new_fns: HashMap<&str, _> = new.function_reflections().collect();
    for (key, r) in &old_fns {
        match new_fns.get(key) {
            Some(n) if n == r => {}
            _ => {
                changed_surface.insert(depsrec::symbol_hash(key));
            }
        }
    }
    for key in new_fns.keys() {
        if !old_fns.contains_key(key) {
            changed_surface.insert(depsrec::symbol_hash(key));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::stubs_changed;

    fn stub(path: &str, src: &str) -> (String, String) {
        (path.to_string(), src.to_string())
    }

    /// Regression: the guard read `self.first_pass` *after* `Session::run` had
    /// already cleared it, so on a genuine first pass with stubs configured it
    /// wrongly reported a stub change.
    #[test]
    fn first_pass_never_reports_a_stub_change() {
        let now = vec![stub("stubs/lib.stub", "<?php class A {}")];
        assert!(!stubs_changed(true, &now, &[]));
        assert!(!stubs_changed(true, &now, &now));
    }

    #[test]
    fn later_passes_compare_stub_content() {
        let a = vec![stub("stubs/lib.stub", "<?php class A {}")];
        let b = vec![stub("stubs/lib.stub", "<?php class B {}")];
        assert!(!stubs_changed(false, &a, &a));
        assert!(stubs_changed(false, &b, &a));
        assert!(stubs_changed(false, &a, &[]));
    }
}
