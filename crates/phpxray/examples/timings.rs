//! Print the wall-clock breakdown of one analysis run over a project root.
//! Dev tool: `cargo run --release -p phpxray --example timings -- <root>`

use phpxray::{run_with_options, RunOptions};
use php_config::Config;
use std::path::PathBuf;

fn main() {
    let root = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .expect("usage: timings <project-root>");
    let config_path = Config::discover(&root).expect("no phpxray.yaml found");
    let mut config = Config::load(&config_path).expect("config load");
    if let Some(b) = &config.baseline {
        let bc = Config::load(root.join(b)).expect("baseline load");
        config.ignore.extend(bc.ignore);
    }
    let options = RunOptions {
        progress: false,
        collect_timings: true,
        use_result_cache: false,
        ..RunOptions::default()
    };
    let report = run_with_options(&config, &root, options);
    let t = report.timings.as_ref().expect("timings");
    println!("files analyzed : {}", report.files_analyzed);
    println!("findings       : {}", report.findings.len());
    println!("discovery      : {:>8.1?}", t.discovery);
    println!("read           : {:>8.1?}", t.read);
    println!("parse          : {:>8.1?}", t.parse);
    println!("index          : {:>8.1?}", t.index);
    println!("analyze (wall) : {:>8.1?}", t.analyze);
    println!("  resolve  (cpu): {:>8.1?}", t.resolve);
    println!("  facts    (cpu): {:>8.1?}", t.facts);
    println!("  type_map (cpu): {:>8.1?}", t.type_map);
    println!("  rules    (cpu): {:>8.1?}", t.rules);
}
