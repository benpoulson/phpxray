use std::fs;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn rule_timings_command_prints_all_buckets() {
    let dir = temp_dir("rule-timings");
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("sample.php"), "<?php function ok(): void {}\n").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_xtask"))
        .arg("rule-timings")
        .arg("--path")
        .arg(&dir)
        .output()
        .unwrap();

    let _ = fs::remove_dir_all(&dir);

    assert!(
        output.status.success(),
        "stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    for bucket in [
        "files_analyzed",
        "findings",
        "cache_hit",
        "discovery_ms",
        "read_ms",
        "parse_ms",
        "index_ms",
        "analyze_ms",
        "resolve_ms",
        "facts_ms",
        "type_map_ms",
        "rules_ms",
    ] {
        assert!(stdout.contains(bucket), "missing {bucket} in:\n{stdout}");
    }
}

fn temp_dir(prefix: &str) -> std::path::PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("phpxray-{prefix}-{nanos}"))
}
