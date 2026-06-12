//! Probe the costs that matter for incremental analysis: builtins-base
//! construction, per-file index adds, and suppression.
//! Dev tool: `cargo run --release -p phpxray --example incr_probe -- <root>`

use phpxray::{parse_files_with_mode, suppress, Report};
use php_config::Config;
use std::path::PathBuf;
use std::time::Instant;

fn main() {
    let root = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .expect("usage: incr_probe <project-root>");
    let config_path = Config::discover(&root).expect("no phpxray.yaml found");
    let mut config = Config::load(&config_path).expect("config load");
    if let Some(b) = &config.baseline {
        let bc = Config::load(root.join(b)).expect("baseline load");
        config.ignore.extend(bc.ignore);
    }

    // Discover + read + parse (mirrors the engine's input pipeline).
    let files = phpxray::discover_files(&config, &root);
    println!("files          : {}", files.len());
    let inputs: Vec<(String, String, bool)> = files
        .iter()
        .map(|(rel, abs, analyze)| {
            let _ = abs;
            (
                rel.clone(),
                std::fs::read_to_string(root.join(rel)).unwrap_or_default(),
                *analyze,
            )
        })
        .collect();
    let t = Instant::now();
    let (parsed, interner) = parse_files_with_mode(inputs);
    println!("parse          : {:>8.1?}", t.elapsed());

    let php_version = php_rules::PhpVersion::default();
    let t = Instant::now();
    let project_base = php_index::ProjectIndex::with_builtins_for(php_version);
    println!("project base   : {:>8.1?}", t.elapsed());
    let t = Instant::now();
    let reflect_base = php_reflect::ReflectionIndex::with_builtins_for(php_version);
    println!("reflect base   : {:>8.1?}", t.elapsed());

    let t = Instant::now();
    let mut project = project_base;
    for f in &parsed {
        project.add_file_as(
            &f.path,
            &php_resolve::index_file(&f.program, &interner),
            php_index::SourceKind::Analyzed,
        );
    }
    println!("project adds   : {:>8.1?}", t.elapsed());
    let t = Instant::now();
    let mut reflection = reflect_base;
    for f in &parsed {
        reflection.add_file_labeled_as(
            Some(&f.path),
            &f.program,
            &interner,
            php_reflect::SourceKind::Analyzed,
        );
    }
    println!("reflect adds   : {:>8.1?}", t.elapsed());

    // Suppression cost with the configured ignore set (incl. merged baseline).
    let report = Report {
        findings: Vec::new(),
        files_analyzed: parsed.len(),
        files_scanned: 0,
        timings: None,
    };
    let sources: std::collections::HashMap<&str, &str> = parsed
        .iter()
        .map(|f| (f.path.as_str(), f.source.as_str()))
        .collect();
    let t = Instant::now();
    let _ = suppress::apply(report, &config.ignore, config.report_unmatched_ignored, &sources);
    println!("suppress (0 findings, {} ignores): {:>8.1?}", config.ignore.len(), t.elapsed());
}
