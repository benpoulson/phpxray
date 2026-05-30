use std::ffi::OsStr;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

struct TempProject {
    root: PathBuf,
}

impl TempProject {
    fn new(name: &str) -> Self {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "php-analyzer-{name}-{}-{unique}",
            std::process::id()
        ));
        fs::create_dir_all(&root).unwrap();
        Self { root }
    }

    fn write(&self, path: &str, contents: &str) {
        let path = self.root.join(path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(path, contents).unwrap();
    }

    fn run<I, S>(&self, args: I) -> Output
    where
        I: IntoIterator<Item = S>,
        S: AsRef<OsStr>,
    {
        Command::new(env!("CARGO_BIN_EXE_php-analyzer"))
            .current_dir(&self.root)
            .args(args)
            .output()
            .unwrap()
    }
}

impl Drop for TempProject {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn write_config(root: &TempProject, yaml: &str) {
    root.write("phpanalyzer.yaml", yaml);
}

#[test]
fn discovers_config_and_cli_paths_override_config_paths() {
    let p = TempProject::new("config-override");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    p.write("src/bad.php", "<?php new MissingFromConfig();");
    p.write("override/bad.php", "<?php new MissingFromOverride();");

    let discovered = p.run([] as [&str; 0]);
    assert!(!discovered.status.success(), "{}", stdout(&discovered));
    let out = stdout(&discovered);
    assert!(out.contains("src/bad.php"), "{out}");
    assert!(!out.contains("override/bad.php"), "{out}");

    let overridden = p.run(["-c", "phpanalyzer.yaml", "override"]);
    assert!(!overridden.status.success(), "{}", stdout(&overridden));
    let out = stdout(&overridden);
    assert!(out.contains("override/bad.php"), "{out}");
    assert!(!out.contains("src/bad.php"), "{out}");
}

#[test]
fn json_output_uses_phpstan_like_shape() {
    let p = TempProject::new("json");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    p.write("src/bad.php", "<?php new MissingJsonClass();");

    let output = p.run(["--error-format", "json"]);
    assert!(!output.status.success(), "{}", stdout(&output));
    let json: serde_json::Value = serde_json::from_str(&stdout(&output)).unwrap();
    assert_eq!(json["totals"]["file_errors"], 1);
    assert_eq!(json["files"]["src/bad.php"]["errors"], 1);
    assert_eq!(
        json["files"]["src/bad.php"]["messages"][0]["identifier"],
        "class.notFound"
    );
}

#[test]
fn configured_baseline_suppresses_findings() {
    let p = TempProject::new("baseline");
    write_config(&p, "level: 0\npaths:\n  - src\nbaseline: baseline.yaml\n");
    p.write(
        "baseline.yaml",
        "ignore:\n  - identifier: class.notFound\n    path: src/bad.php\n",
    );
    p.write("src/bad.php", "<?php new MissingBaselinedClass();");

    let output = p.run([] as [&str; 0]);
    assert!(output.status.success(), "{}", stdout(&output));
    assert!(stdout(&output).contains("[OK]"), "{}", stdout(&output));
}

#[test]
fn inline_suppression_suppresses_line_finding() {
    let p = TempProject::new("inline");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    p.write(
        "src/bad.php",
        "<?php new MissingInlineClass(); // @phpstan-ignore-line class.notFound\n",
    );

    let output = p.run([] as [&str; 0]);
    assert!(output.status.success(), "{}", stdout(&output));
    assert!(stdout(&output).contains("[OK]"), "{}", stdout(&output));
}

#[test]
fn scan_only_files_are_indexed_but_not_reported() {
    let p = TempProject::new("scan-only");
    write_config(&p, "level: 0\npaths:\n  - src\nscanPaths:\n  - vendor\n");
    p.write("src/use.php", "<?php new Vendor\\Thing();");
    p.write("vendor/Thing.php", "<?php namespace Vendor; class Thing {}");
    p.write("vendor/bad.php", "<?php function broken( {}");

    let output = p.run([] as [&str; 0]);
    assert!(output.status.success(), "{}", stdout(&output));
    let out = stdout(&output);
    assert!(out.contains("[OK]"), "{out}");
    assert!(!out.contains("vendor/bad.php"), "{out}");
}

#[test]
fn cross_file_callback_diagnostics_point_at_target_file() {
    let p = TempProject::new("cross-file-callback");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    p.write("src/User.php", "<?php class User {}\n");
    p.write(
        "src/Use.php",
        "<?php\n/** @param list<User> $users */\nfunction run(array $users): void { array_map('cb', $users); }\n",
    );
    p.write(
        "src/Callback.php",
        "<?php\nfunction cb($u): void { $u->missing(); }\n",
    );

    let output = p.run([] as [&str; 0]);
    assert!(!output.status.success(), "{}", stdout(&output));
    let out = stdout(&output);
    assert!(out.contains("src/Callback.php"), "{out}");
    assert!(out.contains("method.notFound"), "{out}");
    assert!(!out.contains("src/Use.php\n"), "{out}");
}
