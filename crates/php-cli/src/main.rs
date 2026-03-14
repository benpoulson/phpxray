//! The `php-analyzer` command-line entry point.

use clap::Parser;
use php_cli::{report, run};
use php_config::{Config, Level};
use std::path::PathBuf;
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
    /// Suppress progress output (accepted for compatibility; currently a no-op).
    #[arg(long = "no-progress")]
    no_progress: bool,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let _ = cli.no_progress; // accepted; no progress output yet

    let (mut config, root) = match resolve_config(&cli) {
        Ok(cr) => cr,
        Err(code) => return code,
    };

    // Command-line overrides win over the config file.
    if !cli.paths.is_empty() {
        config.paths = cli.paths.clone();
    }
    if let Some(l) = &cli.level {
        match parse_level(l) {
            Some(lv) => config.level = lv,
            None => {
                eprintln!("error: invalid level {l:?} (expected 0–9 or \"max\")");
                return ExitCode::from(2);
            }
        }
    }
    if config.paths.is_empty() {
        eprintln!("error: no paths to analyze (set `paths` in the config or pass paths on the command line)");
        return ExitCode::from(2);
    }

    let report = run(&config, &root);
    let rendered = match cli.error_format.as_str() {
        "table" => report::render_table(&report),
        other => {
            eprintln!("error: unknown error format {other:?} (supported: table)");
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
fn resolve_config(cli: &Cli) -> Result<(Config, PathBuf), ExitCode> {
    if let Some(path) = &cli.config {
        let cfg = Config::load(path).map_err(|e| {
            eprintln!("error: {e}");
            ExitCode::from(2)
        })?;
        let root = path.parent().filter(|p| !p.as_os_str().is_empty()).map(PathBuf::from).unwrap_or_else(|| PathBuf::from("."));
        return Ok((cfg, root));
    }
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    match Config::discover(&cwd) {
        Some(path) => {
            let cfg = Config::load(&path).map_err(|e| {
                eprintln!("error: {e}");
                ExitCode::from(2)
            })?;
            Ok((cfg, cwd))
        }
        None => Ok((Config::default(), cwd)),
    }
}

fn parse_level(s: &str) -> Option<Level> {
    if s.eq_ignore_ascii_case("max") {
        return Some(Level::MAX);
    }
    s.parse::<u8>().ok().filter(|n| *n <= 10).map(Level)
}
