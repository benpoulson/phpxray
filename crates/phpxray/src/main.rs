//! The `phpxray` command-line entry point.

use clap::Parser;
use php_config::Config;
use phpxray::{baseline, report, run_with_options, RunOptions};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

/// A fast PHP static analyzer.
#[derive(Parser)]
#[command(name = "phpxray", about = "A fast PHP static analyzer", version)]
#[command(args_conflicts_with_subcommands = true)]
struct Cli {
    #[command(subcommand)]
    command: Option<Cmd>,
    /// Files or directories to analyze (overrides `paths` in the config).
    paths: Vec<String>,
    /// Config file to use (default: autodiscover `phpxray.yaml` in the CWD).
    #[arg(short = 'c', long = "config", value_name = "FILE")]
    config: Option<PathBuf>,
    /// Rule level: 0–9 or `max` (overrides `level` in the config).
    #[arg(short = 'l', long = "level", value_name = "LEVEL")]
    level: Option<String>,
    /// Output format.
    #[arg(long = "error-format", value_name = "FORMAT", default_value = "table")]
    error_format: String,
    /// Write current findings to a baseline file (default: phpxray-baseline.yaml;
    /// a `.neon` extension writes phpstan's baseline format).
    #[arg(short = 'b', long = "generate-baseline", value_name = "FILE", num_args = 0..=1, default_missing_value = "phpxray-baseline.yaml")]
    generate_baseline: Option<String>,
    /// Allow `--generate-baseline` to write a baseline with zero entries
    /// (by default that is refused so a broken run can't wipe a baseline).
    #[arg(long = "allow-empty-baseline")]
    allow_empty_baseline: bool,
    /// Debug mode: print each analyzed file to stderr and bypass the result
    /// cache.
    #[arg(long = "debug")]
    debug: bool,
    /// Exit with code 2 when the result cache could not be used (fresh
    /// analysis was required). A CI guard for jobs that expect a warm cache.
    #[arg(long = "fail-without-result-cache")]
    fail_without_result_cache: bool,
    /// Suppress progress output (accepted for compatibility; currently a no-op).
    #[arg(long = "no-progress")]
    no_progress: bool,
    /// Watch the analyzed paths and re-run on every change (Ctrl-C to stop).
    /// Designed for the `table` format; debounced to coalesce bursts of saves.
    #[arg(short = 'w', long = "watch")]
    watch: bool,
    /// Debounce window for `--watch`, in milliseconds (default: 250).
    #[arg(long = "watch-delay", value_name = "MS", default_value = "250")]
    watch_delay: u64,
    /// Disable inferring signatures for untyped functions from bodies/call sites
    /// (overrides `inferUntypedSignatures` in the config). Analyzes declarations
    /// only, like PHPStan.
    #[arg(long = "no-infer-untyped")]
    no_infer_untyped: bool,
    /// Repair fixable findings in place (insert inferred @var/@param/@return
    /// PHPDoc for the missingType.* family), then re-analyze and report what
    /// remains. Only confidently-inferred types are written.
    #[arg(long = "fix")]
    fix: bool,
    /// Watch the analyzed paths and send a desktop notification when there
    /// are errors.
    ///
    /// Designed for the `table` format; debounced to coalesce bursts of saves.
    /// When there are no errors, the notification is silent.
    #[arg(long = "notify")]
    notify: bool,
}

/// Auxiliary maintenance commands (plain `phpxray [paths…]` analyzes).
#[derive(clap::Subcommand)]
enum Cmd {
    /// Delete the stored result cache for this project.
    #[command(name = "clear-result-cache")]
    ClearResultCache {
        /// Config file to use (default: autodiscover `phpxray.yaml` in the CWD).
        #[arg(short = 'c', long = "config", value_name = "FILE")]
        config: Option<PathBuf>,
    },
}

fn clear_result_cache(config_path: Option<&PathBuf>) -> ExitCode {
    let (config, root) = if let Some(path) = config_path {
        match Config::load(path) {
            Ok(c) => {
                let root = path
                    .parent()
                    .filter(|p| !p.as_os_str().is_empty())
                    .map(PathBuf::from)
                    .unwrap_or_else(|| PathBuf::from("."));
                (c, root)
            }
            Err(e) => {
                eprintln!("error: loading config {}: {e}", path.display());
                return ExitCode::from(2);
            }
        }
    } else {
        let cwd = PathBuf::from(".");
        match Config::discover(&cwd) {
            Some(found) => match Config::load(&found) {
                Ok(c) => (c, cwd),
                Err(e) => {
                    eprintln!("error: loading config {}: {e}", found.display());
                    return ExitCode::from(2);
                }
            },
            None => (Config::default(), cwd),
        }
    };
    let dir = phpxray::result_cache_dir(&config, &root, None);
    match std::fs::remove_dir_all(&dir) {
        Ok(()) => {
            eprintln!("Result cache cleared from {}", dir.display());
            ExitCode::SUCCESS
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            eprintln!("Result cache already empty ({})", dir.display());
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("error: clearing result cache {}: {e}", dir.display());
            ExitCode::from(2)
        }
    }
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    if let Some(Cmd::ClearResultCache { config }) = &cli.command {
        return clear_result_cache(config.as_ref());
    }

    if cli.watch && cli.generate_baseline.is_some() {
        eprintln!("error: --watch cannot be combined with --generate-baseline");
        return ExitCode::from(2);
    }
    if cli.fix && cli.watch {
        eprintln!("error: --watch cannot be combined with --fix");
        return ExitCode::from(2);
    }
    if cli.fix && cli.generate_baseline.is_some() {
        eprintln!("error: --fix cannot be combined with --generate-baseline");
        return ExitCode::from(2);
    }
    if cli.notify && cli.fix {
        eprintln!("error: --watch cannot be combined with --fix");
        return ExitCode::from(2);
    }
    if cli.notify && cli.generate_baseline.is_some() {
        eprintln!("error: --watch cannot be combined with --generate-baseline");
        return ExitCode::from(2);
    }

    // Generate-baseline mode: apply CLI overrides but do NOT merge the configured
    // baseline, so the snapshot captures the full current state.
    if let Some(out) = &cli.generate_baseline {
        let RunConfig {
            config,
            root,
            run_options,
            ..
        } = match resolve_and_override(&cli) {
            Ok(rc) => rc,
            Err(code) => return code,
        };
        let report = run_with_options(&config, &root, run_options);
        let entries = baseline::entries(&report);
        if entries.is_empty() && !cli.allow_empty_baseline {
            eprintln!(
                "error: no errors found, refusing to write an empty baseline (pass --allow-empty-baseline to allow)"
            );
            return ExitCode::from(2);
        }
        // The extension picks the format: `.neon` writes a phpstan-compatible
        // baseline, anything else our YAML `ignore:` form.
        let rendered = if out.ends_with(".neon") {
            baseline::to_neon(&entries)
        } else {
            baseline::to_yaml(&entries)
        };
        let path = root.join(out);
        if let Err(e) = std::fs::write(&path, rendered) {
            eprintln!("error: writing baseline {}: {e}", path.display());
            return ExitCode::from(2);
        }
        eprintln!(
            "Wrote baseline with {} entries to {}",
            entries.len(),
            path.display()
        );
        return ExitCode::SUCCESS;
    }

    let RunConfig {
        config,
        root,
        config_path,
        run_options,
    } = match effective_config(&cli) {
        Ok(rc) => rc,
        Err(code) => return code,
    };

    // Watch mode: loop forever, re-running on debounced changes. Runs until the
    // process is interrupted, so it never falls through to the single-shot path.
    if cli.watch {
        let delay = std::time::Duration::from_millis(cli.watch_delay);
        // Rebuild the effective config from disk on each config-file change.
        let reload = || effective_config(&cli).ok().map(|rc| rc.config);
        match phpxray::watch::run_watch(
            config,
            &root,
            config_path.as_deref(),
            run_options,
            delay,
            &cli.error_format,
            reload,
        ) {
            Ok(()) => return ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("error: {e}");
                return ExitCode::from(2);
            }
        }
    }

    let (report, fix_summary) = if cli.fix {
        let fixed = phpxray::run_fix(&config, &root, run_options);
        (fixed.report, Some(fixed.summary))
    } else {
        (run_with_options(&config, &root, run_options), None)
    };
    let render_opts = report::RenderOptions {
        editor_url: config.editor_url.clone(),
        editor_url_title: config.editor_url_title.clone(),
    };
    let rendered = match report::render_with(&report, &cli.error_format, &render_opts) {
        Some(s) => s,
        None => {
            eprintln!(
                "error: unknown error format {:?} (supported: table, json, prettyJson, raw, github, checkstyle, gitlab, junit)",
                cli.error_format
            );
            return ExitCode::from(2);
        }
    };
    print!("{rendered}");
    if let Some(summary) = fix_summary {
        eprintln!(
            "Fixed {} finding(s) in {} file(s).",
            summary.findings_fixed, summary.files_changed
        );
        for (path, reason) in &summary.files_skipped {
            eprintln!("Skipped {path}: {reason}.");
        }
    }

    if cli.fail_without_result_cache && !report.timings.as_ref().is_some_and(|t| t.cache_hit) {
        eprintln!("error: result cache was not used (fresh analysis was required)");
        return ExitCode::from(2);
    }

    if report.has_errors() {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}

/// The effective configuration for a run: the merged config, the project root,
/// the backing config file (if any), and the runtime options.
struct RunConfig {
    config: Config,
    root: PathBuf,
    config_path: Option<PathBuf>,
    run_options: RunOptions,
}

/// Resolve the config and apply CLI overrides (`paths`, `level`). Does *not*
/// merge a configured baseline — callers that want it call [`merge_baseline`].
fn resolve_and_override(cli: &Cli) -> Result<RunConfig, ExitCode> {
    let ConfigResolution {
        mut config,
        root,
        config_path,
        use_cli_paths,
    } = resolve_config(cli)?;

    let run_options = RunOptions {
        progress: !cli.no_progress,
        notify: cli.notify,
        debug: cli.debug,
        // `--fail-without-result-cache` needs the cache-hit flag, which ships
        // in the timings.
        collect_timings: cli.fail_without_result_cache,
        ..RunOptions::default()
    };

    // Command-line overrides win over the config file.
    if use_cli_paths && !cli.paths.is_empty() {
        config.paths = cli.paths.clone();
    }
    if let Some(l) = &cli.level {
        match l.parse() {
            Ok(lv) => config.level = lv,
            Err(_) => {
                eprintln!("error: invalid level {l:?} (expected 0–9 or \"max\")");
                return Err(ExitCode::from(2));
            }
        }
    }
    if cli.no_infer_untyped {
        config.infer_untyped_signatures = false;
    }
    if config.paths.is_empty() {
        eprintln!("error: no paths to analyze (set `paths` in the config or pass paths on the command line)");
        return Err(ExitCode::from(2));
    }
    // A malformed `ignore:` entry is a configuration error, not something to
    // silently degrade — phpstan refuses to start on one too. Degrading an
    // invalid regex to a literal match made it look like the finding was fixed.
    let ignore_problems = phpxray::suppress::validate_ignores(&config.ignore);
    if !ignore_problems.is_empty() {
        let plural = if ignore_problems.len() == 1 {
            "entry"
        } else {
            "entries"
        };
        eprintln!("error: invalid {plural} in `ignore`:");
        for p in &ignore_problems {
            eprintln!("  {p}");
        }
        return Err(ExitCode::from(2));
    }
    Ok(RunConfig {
        config,
        root,
        config_path,
        run_options,
    })
}

/// Merge a configured baseline file's ignore entries into `config`.
fn merge_baseline(config: &mut Config, root: &Path) -> Result<(), ExitCode> {
    if let Some(b) = &config.baseline {
        // `.neon` baselines are phpstan's format (`parameters: → ignoreErrors:`);
        // anything else is our YAML `ignore:` form.
        let loaded = if b.ends_with(".neon") {
            std::fs::read_to_string(root.join(b))
                .map_err(|e| e.to_string())
                .and_then(|text| php_config::neon::parse_baseline(&text))
        } else {
            Config::load(root.join(b))
                .map(|bc| bc.ignore)
                .map_err(|e| e.to_string())
        };
        match loaded {
            Ok(ignore) => {
                config.ignore.extend(ignore.into_iter().map(|mut e| {
                    // A baseline is a snapshot of past debt: an entry going
                    // stale means the finding was FIXED, so don't nag about it
                    // (unlike hand-written `ignore:` entries, which follow
                    // `reportUnmatchedIgnored`). Explicit per-entry settings
                    // in the baseline file still win.
                    e.report_unmatched.get_or_insert(false);
                    e
                }));
            }
            Err(e) => {
                eprintln!("error: loading baseline {b}: {e}");
                return Err(ExitCode::from(2));
            }
        }
    }
    Ok(())
}

/// The full effective config for a normal or watch run: CLI overrides plus the
/// configured baseline merged in.
fn effective_config(cli: &Cli) -> Result<RunConfig, ExitCode> {
    let mut rc = resolve_and_override(cli)?;
    merge_baseline(&mut rc.config, &rc.root)?;
    Ok(rc)
}

/// Load the config (from `--config` or autodiscovery) and determine the project
/// root. On error, returns the process exit code to use.
fn resolve_config(cli: &Cli) -> Result<ConfigResolution, ExitCode> {
    if let Some(path) = &cli.config {
        let config = load_config(path)?;
        let root = path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("."));
        return Ok(ConfigResolution {
            config,
            root,
            config_path: Some(path.clone()),
            use_cli_paths: true,
        });
    }
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    if let Some(root) = target_config_root(cli, &cwd) {
        if let Some(path) = Config::discover(&root) {
            return Ok(ConfigResolution {
                config: load_config(&path)?,
                root,
                config_path: Some(path),
                use_cli_paths: false,
            });
        }
    }
    match Config::discover(&cwd) {
        Some(path) => {
            let config = load_config(&path)?;
            Ok(ConfigResolution {
                config,
                root: cwd,
                config_path: Some(path),
                use_cli_paths: true,
            })
        }
        None => Ok(ConfigResolution {
            config: Config::default(),
            root: cwd,
            config_path: None,
            use_cli_paths: true,
        }),
    }
}

struct ConfigResolution {
    config: Config,
    root: PathBuf,
    /// The config file backing this run, if one was found (used by `--watch`).
    config_path: Option<PathBuf>,
    /// Whether positional CLI paths should replace config `paths`.
    use_cli_paths: bool,
}

fn load_config(path: impl AsRef<Path>) -> Result<Config, ExitCode> {
    let path = path.as_ref();
    let config = Config::load(path).map_err(|e| {
        eprintln!("error: {e}");
        ExitCode::from(2)
    })?;
    // Unknown keys stay non-fatal (forward compatibility), but a silent no-op
    // for a typo is a bad experience — warn, with a did-you-mean.
    if let Ok(text) = std::fs::read_to_string(path) {
        for (key, suggestion) in php_config::unknown_keys(&text) {
            match suggestion {
                Some(known) => eprintln!(
                    "warning: unknown config key `{key}` in {} — did you mean `{known}`?",
                    path.display()
                ),
                None => eprintln!("warning: unknown config key `{key}` in {}", path.display()),
            }
        }
    }
    Ok(config)
}

fn target_config_root(cli: &Cli, cwd: &Path) -> Option<PathBuf> {
    if cli.paths.len() != 1 {
        return None;
    }
    let path = PathBuf::from(&cli.paths[0]);
    let path = if path.is_absolute() {
        path
    } else {
        cwd.join(path)
    };
    path.is_dir().then_some(path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn target_directory_config_is_used_as_project_root() {
        let dir = temp_dir("target-config");
        let project = dir.join("project");
        fs::create_dir_all(&project).unwrap();
        fs::write(project.join("phpxray.yaml"), "level: 6\npaths:\n  - app\n").unwrap();

        let cli = Cli::parse_from(["phpxray", project.to_str().unwrap()]);
        let resolved = resolve_config(&cli).unwrap();

        assert_eq!(resolved.root, project);
        assert_eq!(resolved.config.level.to_string(), "6");
        assert_eq!(resolved.config.paths, ["app"]);
        assert!(!resolved.use_cli_paths);

        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn explicit_config_still_allows_positional_path_override() {
        let dir = temp_dir("explicit-config");
        let config = dir.join("phpxray.yaml");
        fs::write(&config, "level: 4\npaths:\n  - app\n").unwrap();

        let cli = Cli::parse_from(["phpxray", "-c", config.to_str().unwrap(), "tests"]);
        let resolved = resolve_config(&cli).unwrap();

        assert_eq!(resolved.root, dir);
        assert!(resolved.use_cli_paths);

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
