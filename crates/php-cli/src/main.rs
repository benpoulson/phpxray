//! The `php-analyzer` command-line entry point.

use clap::Parser;
use php_cli::{baseline, report, run_with_options, RunOptions};
use php_config::Config;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

/// A fast PHP static analyzer.
#[derive(Parser)]
#[command(name = "php-analyzer", about = "A fast PHP static analyzer", version)]
struct Cli {
    /// Files or directories to analyze (overrides `paths` in the config).
    paths: Vec<String>,
    /// Config file to use (default: autodiscover `phpanalyzer.yaml` in the CWD).
    #[arg(short = 'c', long = "config", value_name = "FILE")]
    config: Option<PathBuf>,
    /// Rule level: 0–9 or `max` (overrides `level` in the config).
    #[arg(short = 'l', long = "level", value_name = "LEVEL")]
    level: Option<String>,
    /// Output format.
    #[arg(long = "error-format", value_name = "FORMAT", default_value = "table")]
    error_format: String,
    /// Write current findings to a baseline file (default: phpanalyzer-baseline.yaml).
    #[arg(long = "generate-baseline", value_name = "FILE", num_args = 0..=1, default_missing_value = "phpanalyzer-baseline.yaml")]
    generate_baseline: Option<String>,
    /// Suppress progress output (accepted for compatibility; currently a no-op).
    #[arg(long = "no-progress")]
    no_progress: bool,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let run_options = RunOptions {
        progress: !cli.no_progress,
        ..RunOptions::default()
    };

    let ConfigResolution {
        mut config,
        root,
        use_cli_paths,
    } = match resolve_config(&cli) {
        Ok(cr) => cr,
        Err(code) => return code,
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
                return ExitCode::from(2);
            }
        }
    }
    if config.paths.is_empty() {
        eprintln!("error: no paths to analyze (set `paths` in the config or pass paths on the command line)");
        return ExitCode::from(2);
    }

    // Generate-baseline mode: run without applying any baseline, write the
    // findings out, and exit. (The configured baseline is intentionally not
    // loaded so the snapshot captures the full current state.)
    if let Some(out) = &cli.generate_baseline {
        let report = run_with_options(&config, &root, run_options);
        let entries = baseline::entries(&report);
        let yaml = baseline::to_yaml(&entries);
        let path = root.join(out);
        if let Err(e) = std::fs::write(&path, yaml) {
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

    // Normal run: merge a configured baseline into the ignore set.
    if let Some(b) = &config.baseline {
        match Config::load(root.join(b)) {
            Ok(bc) => config.ignore.extend(bc.ignore),
            Err(e) => {
                eprintln!("error: loading baseline {b}: {e}");
                return ExitCode::from(2);
            }
        }
    }

    let report = run_with_options(&config, &root, run_options);
    let rendered = match report::render(&report, &cli.error_format) {
        Some(s) => s,
        None => {
            eprintln!(
                "error: unknown error format {:?} (supported: table, json, github, checkstyle)",
                cli.error_format
            );
            return ExitCode::from(2);
        }
    };
    print!("{rendered}");

    if report.has_errors() {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
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
            use_cli_paths: true,
        });
    }
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    if let Some(root) = target_config_root(cli, &cwd) {
        if let Some(path) = Config::discover(&root) {
            return Ok(ConfigResolution {
                config: load_config(path)?,
                root,
                use_cli_paths: false,
            });
        }
    }
    match Config::discover(&cwd) {
        Some(path) => {
            let config = load_config(path)?;
            Ok(ConfigResolution {
                config,
                root: cwd,
                use_cli_paths: true,
            })
        }
        None => Ok(ConfigResolution {
            config: Config::default(),
            root: cwd,
            use_cli_paths: true,
        }),
    }
}

struct ConfigResolution {
    config: Config,
    root: PathBuf,
    /// Whether positional CLI paths should replace config `paths`.
    use_cli_paths: bool,
}

fn load_config(path: impl AsRef<Path>) -> Result<Config, ExitCode> {
    Config::load(path).map_err(|e| {
        eprintln!("error: {e}");
        ExitCode::from(2)
    })
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
        fs::write(
            project.join("phpanalyzer.yaml"),
            "level: 6\npaths:\n  - app\n",
        )
        .unwrap();

        let cli = Cli::parse_from(["php-analyzer", project.to_str().unwrap()]);
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
        let config = dir.join("phpanalyzer.yaml");
        fs::write(&config, "level: 4\npaths:\n  - app\n").unwrap();

        let cli = Cli::parse_from(["php-analyzer", "-c", config.to_str().unwrap(), "tests"]);
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
            std::env::temp_dir().join(format!("php-analyzer-{label}-{}-{now}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        dir
    }
}
