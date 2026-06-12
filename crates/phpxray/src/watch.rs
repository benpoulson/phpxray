//! `--watch` mode: re-run the analysis whenever a watched source file (or the
//! config file) changes, with debouncing so a burst of editor saves coalesces
//! into a single run.
//!
//! The OS-facing wiring (the `notify` debouncer + the blocking event loop) lives
//! in [`run_watch`] and is deliberately thin and untested — filesystem events are
//! non-deterministic across platforms. The decision logic that is worth testing —
//! "is this changed path relevant?" and "what should we hand the OS watcher?" —
//! is factored into the pure [`is_relevant`] and [`watch_targets`] helpers.
//!
//! Passes run through the incremental [`Session`] by default (re-analyzing only
//! what each change can affect); `PHPXRAY_WATCH_FULL=1` falls back to full batch
//! passes. On Linux a recursive watch registers one inotify watch per directory
//! and can hit `max_user_watches` on very large trees — excluded *events* are
//! filtered, but excluded directories are not yet pruned from the watch set.

use crate::incremental::{ChangeHint, Session};
use crate::{report, run_with_options, RunOptions};
use indicatif::{ProgressBar, ProgressDrawTarget, ProgressStyle};
use notify::event::ModifyKind;
use notify::{EventKind, RecursiveMode};
use notify_debouncer_full::new_debouncer;
use php_config::{Config, ExcludeMatcher};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

/// Whether a changed `path` should trigger a re-run.
///
/// True for the config file (editing `level`/`paths`/`ignore` must re-analyze)
/// and for any file whose extension is analyzed and whose root-relative path is
/// not hard-excluded. Everything else (editor temp files, `.swp`, excluded
/// directories) is ignored. `root` and `config_file` are expected to be
/// canonical, matching the absolute paths the OS watcher reports.
pub fn is_relevant(
    path: &Path,
    root: &Path,
    config: &Config,
    exclude: &ExcludeMatcher,
    config_file: Option<&Path>,
) -> bool {
    if let Some(cf) = config_file {
        if path == cf {
            return true;
        }
    }
    let ext_ok = path
        .extension()
        .and_then(|e| e.to_str())
        .map(|e| config.extensions.iter().any(|w| w == e))
        .unwrap_or(false);
    if !ext_ok {
        return false;
    }
    !exclude.is_excluded(&rel_path(path, root))
}

/// The set of paths to register with the OS watcher, each with its recursion
/// mode. Analyzed/scanned directories are watched recursively (so new files are
/// picked up); single files are watched directly; the config file is watched via
/// its parent directory (non-recursively) so atomic-save renames are still seen.
/// Duplicates are removed, preferring a recursive watch over a non-recursive one
/// for the same path.
pub fn watch_targets(
    config: &Config,
    root: &Path,
    config_file: Option<&Path>,
) -> Vec<(PathBuf, RecursiveMode)> {
    let mut targets: Vec<(PathBuf, RecursiveMode)> = Vec::new();
    let mut add = |path: PathBuf, mode: RecursiveMode| {
        match targets.iter_mut().find(|(p, _)| *p == path) {
            Some(entry) => {
                // Prefer recursive coverage if any source asked for it.
                if mode == RecursiveMode::Recursive {
                    entry.1 = RecursiveMode::Recursive;
                }
            }
            None => targets.push((path, mode)),
        }
    };

    for entry in config.paths.iter().chain(config.scan_paths.iter()) {
        let path = root.join(entry);
        let mode = if path.is_dir() {
            RecursiveMode::Recursive
        } else {
            RecursiveMode::NonRecursive
        };
        add(path, mode);
    }
    for entry in &config.scan_files {
        add(root.join(entry), RecursiveMode::NonRecursive);
    }
    if let Some(cf) = config_file {
        // Watch the config file's directory so atomic saves (write-temp +
        // rename) are observed; `is_relevant` filters back down to the file.
        match cf.parent().filter(|p| !p.as_os_str().is_empty()) {
            Some(dir) => add(dir.to_path_buf(), RecursiveMode::NonRecursive),
            None => add(cf.to_path_buf(), RecursiveMode::NonRecursive),
        }
    }
    targets
}

/// Run the analysis in a loop, re-running on each debounced batch of relevant
/// filesystem changes. Blocks until the process is interrupted (Ctrl-C); only
/// returns `Err` if the OS watcher could not be set up.
///
/// `reload` rebuilds the effective config from disk (applying the same CLI
/// overrides and baseline merge as the initial run). It is called whenever the
/// config file changes so edits to `level`/`ignore`/`exclude`/… take effect
/// without a restart; if it returns `None` (the new config failed to load) the
/// previous config is kept. The *set of watched paths* is fixed at startup, so
/// adding a brand-new top-level `paths` entry still needs a restart.
pub fn run_watch(
    mut config: Config,
    root: &Path,
    config_file: Option<&Path>,
    mut options: RunOptions,
    delay: Duration,
    format: &str,
    reload: impl Fn() -> Option<Config>,
) -> Result<(), String> {
    // Progress spinners fight the screen-clearing redraw; force them off.
    options.progress = false;

    let canonical_root = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());
    let config_file = config_file.and_then(|p| p.canonicalize().ok());
    let mut exclude = hard_exclude(&config);

    // Incremental by default: a persistent Session keeps per-file artifacts and
    // re-analyzes only what each change can affect — including with signature
    // inference on (the Session recomputes inference each pass, in parallel, and
    // diffs the inferred signatures into the invalidation set, so rule re-runs
    // stay selective). PHPXRAY_WATCH_FULL=1 is the escape hatch back to full
    // batch passes.
    let mut session = std::env::var_os("PHPXRAY_WATCH_FULL")
        .is_none()
        .then(|| Session::new(&config));

    // The watch set is fixed at startup (see the doc comment).
    let targets = watch_targets(&config, root, config_file.as_deref());

    // Initial render so the user sees results immediately.
    analyze_and_render(&mut session, &config, root, &options, format, None, None);

    let (tx, rx) = mpsc::channel();
    let mut debouncer =
        new_debouncer(delay, None, tx).map_err(|e| format!("failed to start file watcher: {e}"))?;
    for (path, mode) in &targets {
        // notify wants a real, existing path; canonicalize to strip `.`/`..`
        // components (e.g. a `./src` config entry → `<root>/./src`) and resolve
        // symlinks so events — which FSEvents reports as canonical paths — line
        // up. If the path doesn't exist yet, the raw path's watch error stands.
        let watch_path = path.canonicalize();
        let watch_path = watch_path.as_deref().unwrap_or(path);
        if let Err(e) = debouncer.watch(watch_path, *mode) {
            eprintln!("warning: cannot watch {}: {e}", watch_path.display());
        }
    }

    for result in rx {
        let events = match result {
            Ok(events) => events,
            Err(errors) => {
                for e in errors {
                    eprintln!("watch error: {e}");
                }
                continue;
            }
        };
        let mut changed: Vec<PathBuf> = Vec::new();
        let mut config_changed = false;
        let mut saw_creates_or_removes = false;
        for ev in &events {
            if matches!(ev.kind, EventKind::Access(_)) {
                continue;
            }
            if matches!(
                ev.kind,
                EventKind::Create(_) | EventKind::Remove(_) | EventKind::Modify(ModifyKind::Name(_))
            ) {
                saw_creates_or_removes = true;
            }
            for p in &ev.paths {
                if config_file.as_deref().is_some_and(|cf| p == cf) {
                    config_changed = true;
                } else if is_relevant(p, &canonical_root, &config, &exclude, config_file.as_deref())
                    && !changed.contains(p)
                {
                    changed.push(p.clone());
                }
            }
        }
        if config_changed {
            // Pick up edits to level/ignore/exclude/extensions on the fly.
            if let Some(fresh) = reload() {
                config = fresh;
                exclude = hard_exclude(&config);
            }
        }
        if !changed.is_empty() || config_changed {
            // Immediate feedback so a slow re-analysis doesn't look like a hang.
            let reason = changed
                .first()
                .map(|p| rel_path(p, &canonical_root))
                .unwrap_or_else(|| "config".to_string());
            // A config change may alter discovery — no hint forces a full diff.
            let hint = (!config_changed).then_some(ChangeHint {
                paths: changed,
                saw_creates_or_removes,
            });
            analyze_and_render(
                &mut session,
                &config,
                root,
                &options,
                format,
                Some(&reason),
                hint.as_ref(),
            );
        }
    }
    Ok(())
}

/// Run one analysis pass and render it. For the human `table` format the screen
/// is cleared and an animated "analyzing…" spinner shown *before* the (possibly
/// slow) analysis so a re-run never looks like a hang; the final results replace
/// it, annotated with how long the run took. `reason`, if set, names what
/// triggered the run.
#[allow(clippy::too_many_arguments)]
fn analyze_and_render(
    session: &mut Option<Session>,
    config: &Config,
    root: &Path,
    options: &RunOptions,
    format: &str,
    reason: Option<&str>,
    hint: Option<&ChangeHint>,
) {
    let is_table = format == "table";
    let mut working = None;
    if is_table {
        // Clear screen + scrollback, then show we're working *now*.
        let mut banner = String::from("\x1b[2J\x1b[3J\x1b[H");
        banner.push_str(&header(&[clock_local()]));
        write_stdout(&banner);
        let message = match reason {
            Some(r) => format!("Change in {r} — analyzing…"),
            None => "Analyzing…".to_string(),
        };
        working = Some(spinner(message));
    } else if let Some(r) = reason {
        eprintln!("Change in {r} — analyzing…");
    }

    let start = Instant::now();
    let (report, reanalyzed) = match session.as_mut() {
        Some(s) => {
            let report = s.run(config, root, hint);
            (report, Some(s.last_pass().files_reanalyzed))
        }
        None => (run_with_options(config, root, options.clone()), None),
    };
    let elapsed = start.elapsed();
    if let Some(pb) = working {
        pb.finish_and_clear();
    }

    let mut out = String::new();
    if is_table {
        let mut segments = vec![clock_local(), format!("{:.1}s", elapsed.as_secs_f64())];
        // Only change-triggered passes are selective; the initial pass analyzes
        // everything, so a re-analyzed count there would be noise.
        if let (Some(n), Some(_)) = (reanalyzed, reason) {
            let noun = if n == 1 { "file" } else { "files" };
            segments.push(format!("re-analyzed {n} {noun}"));
        }
        out.push_str("\x1b[2J\x1b[3J\x1b[H");
        out.push_str(&header(&segments));
    }
    if let Some(rendered) = report::render(&report, format) {
        out.push_str(&rendered);
    }
    write_stdout(&out);
}

const BOLD: &str = "\x1b[1m";
const DIM: &str = "\x1b[2m";
const RESET: &str = "\x1b[0m";

/// One-line status header — `── phpxray · seg · seg ──` — with the frame and
/// separators dimmed so the values carry the visual weight.
fn header(segments: &[String]) -> String {
    let mut line = format!("{DIM}──{RESET} {BOLD}phpxray{RESET}");
    for seg in segments {
        line.push_str(&format!(" {DIM}·{RESET} {seg}"));
    }
    line.push_str(&format!(" {DIM}──{RESET}\n"));
    line
}

/// An animated spinner on stdout (auto-hidden when stdout is not a terminal).
fn spinner(message: String) -> ProgressBar {
    let pb = ProgressBar::with_draw_target(None, ProgressDrawTarget::stdout());
    pb.set_style(
        ProgressStyle::with_template("{spinner:.cyan} {wide_msg}")
            .expect("static template is valid")
            .tick_chars("⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏ "),
    );
    pb.set_message(message);
    pb.enable_steady_tick(Duration::from_millis(80));
    pb
}

/// Write `s` to stdout and flush, ignoring errors (a closed pipe just ends the run).
fn write_stdout(s: &str) {
    let stdout = std::io::stdout();
    let mut lock = stdout.lock();
    let _ = lock.write_all(s.as_bytes());
    let _ = lock.flush();
}

/// `HH:MM:SS` time-of-day in the user's local timezone, without pulling in a
/// date/time crate: `localtime_r` on unix, with a UTC fallback elsewhere.
fn clock_local() -> String {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let (h, m, s) = local_hms(secs).unwrap_or_else(|| {
        let tod = secs % 86_400;
        ((tod / 3600) as u32, ((tod % 3600) / 60) as u32, (tod % 60) as u32)
    });
    format!("{h:02}:{m:02}:{s:02}")
}

#[cfg(unix)]
fn local_hms(unix_secs: u64) -> Option<(u32, u32, u32)> {
    let t = unix_secs as libc::time_t;
    let mut tm = unsafe { std::mem::zeroed::<libc::tm>() };
    // SAFETY: localtime_r only fills the caller-provided tm; thread-safe by contract.
    if unsafe { libc::localtime_r(&t, &mut tm) }.is_null() {
        return None;
    }
    Some((tm.tm_hour as u32, tm.tm_min as u32, tm.tm_sec as u32))
}

#[cfg(not(unix))]
fn local_hms(_unix_secs: u64) -> Option<(u32, u32, u32)> {
    None
}

/// The set of files dropped from analysis entirely — changes to these never
/// warrant a re-run. Mirrors the engine's hard-exclude composition (`exclude`
/// plus `excludePaths.analyseAndScan`); `excludePaths.analyse` is intentionally
/// *not* included because those files are still scanned for symbols, so editing
/// them can change reflection results.
fn hard_exclude(config: &Config) -> ExcludeMatcher {
    let mut patterns = config.exclude.clone();
    patterns.extend(config.exclude_paths.analyse_and_scan.iter().cloned());
    ExcludeMatcher::new(&patterns)
}

/// `path` relative to `root` with forward slashes; falls back to the full path.
fn rel_path(path: &Path, root: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn cfg() -> Config {
        Config {
            paths: vec!["src".to_string()],
            exclude: vec!["src/generated".to_string()],
            extensions: vec!["php".to_string()],
            ..Config::default()
        }
    }

    #[test]
    fn relevant_php_source() {
        let c = cfg();
        let ex = hard_exclude(&c);
        let root = Path::new("/proj");
        assert!(is_relevant(
            Path::new("/proj/src/Foo.php"),
            root,
            &c,
            &ex,
            None
        ));
    }

    #[test]
    fn editor_noise_is_ignored() {
        let c = cfg();
        let ex = hard_exclude(&c);
        let root = Path::new("/proj");
        assert!(!is_relevant(
            Path::new("/proj/src/Foo.php.swp"),
            root,
            &c,
            &ex,
            None
        ));
        assert!(!is_relevant(
            Path::new("/proj/src/Foo.tmp"),
            root,
            &c,
            &ex,
            None
        ));
    }

    #[test]
    fn excluded_paths_are_ignored() {
        let c = cfg();
        let ex = hard_exclude(&c);
        let root = Path::new("/proj");
        assert!(!is_relevant(
            Path::new("/proj/src/generated/Gen.php"),
            root,
            &c,
            &ex,
            None
        ));
    }

    #[test]
    fn config_file_is_relevant_despite_extension() {
        let c = cfg();
        let ex = hard_exclude(&c);
        let root = Path::new("/proj");
        let config_file = Path::new("/proj/phpxray.yaml");
        assert!(is_relevant(
            config_file,
            root,
            &c,
            &ex,
            Some(config_file)
        ));
        // A different yaml is not relevant.
        assert!(!is_relevant(
            Path::new("/proj/other.yaml"),
            root,
            &c,
            &ex,
            Some(config_file)
        ));
    }

    #[test]
    fn targets_watch_dirs_recursively_and_dedup() {
        let dir = temp_dir("watch-targets");
        let src = dir.join("src");
        fs::create_dir_all(&src).unwrap();
        let config_file = dir.join("phpxray.yaml");
        fs::write(&config_file, "level: 0\n").unwrap();

        let config = Config {
            paths: vec!["src".to_string()],
            ..Config::default()
        };
        let targets = watch_targets(&config, &dir, Some(&config_file));

        // src/ watched recursively.
        assert!(targets
            .iter()
            .any(|(p, m)| *p == src && *m == RecursiveMode::Recursive));
        // The config file's directory (== root) watched non-recursively.
        assert!(targets
            .iter()
            .any(|(p, m)| *p == dir && *m == RecursiveMode::NonRecursive));

        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn targets_prefer_recursive_on_overlap() {
        let dir = temp_dir("watch-overlap");
        fs::create_dir_all(&dir).unwrap();
        // Config lives in root and `paths` is also root: the same path is added
        // once as recursive (a dir) and once as the config parent (non-rec).
        let config_file = dir.join("phpxray.yaml");
        fs::write(&config_file, "level: 0\n").unwrap();
        let config = Config {
            paths: vec![".".to_string()],
            ..Config::default()
        };
        let targets = watch_targets(&config, &dir, Some(&config_file));
        let root_join = dir.join(".");
        let matches: Vec<_> = targets.iter().filter(|(p, _)| *p == root_join).collect();
        assert_eq!(matches.len(), 1, "overlapping path should be deduped");
        assert_eq!(matches[0].1, RecursiveMode::Recursive);

        let _ = fs::remove_dir_all(dir);
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
