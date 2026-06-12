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
            "phpxray-{name}-{}-{unique}",
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
        Command::new(env!("CARGO_BIN_EXE_phpxray"))
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

fn cache_file_count(project: &TempProject) -> usize {
    let cache = project.root.join(".phpxray/cache/results-v1");
    fs::read_dir(cache)
        .map(|entries| entries.filter_map(Result::ok).count())
        .unwrap_or(0)
}

fn write_config(root: &TempProject, yaml: &str) {
    root.write("phpxray.yaml", yaml);
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

    let overridden = p.run(["-c", "phpxray.yaml", "override"]);
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
fn stale_baseline_entries_do_not_nag() {
    // A baseline entry whose finding has since been FIXED must not produce an
    // ignore.unmatched error — going stale is the goal of a baseline. Explicit
    // `ignore:` entries in the config keep following reportUnmatchedIgnored.
    let p = TempProject::new("stale-baseline");
    write_config(&p, "level: 0\npaths:\n  - src\nbaseline: baseline.yaml\n");
    p.write(
        "baseline.yaml",
        "ignore:\n  - message: '#^unknown class `LongGoneClass`$#'\n    count: 1\n    path: src/ok.php\n",
    );
    p.write("src/ok.php", "<?php class Fine {}\n");

    let output = p.run([] as [&str; 0]);
    assert!(output.status.success(), "{}", stdout(&output));
    assert!(
        !stdout(&output).contains("ignore.unmatched"),
        "stale baseline entry must not nag: {}",
        stdout(&output)
    );
}

#[test]
fn rules_check_inside_closure_and_arrow_bodies() {
    // Closure/arrow-fn bodies are recorded in the file type map, so rules using
    // `type_of` (here method.notFound) fire on a typed param inside them.
    let p = TempProject::new("closure-bodies");
    write_config(&p, "level: 6\npaths:\n  - src\n");
    p.write("src/User.php", "<?php class User { public function name(): string { return \"\"; } }\n");
    p.write(
        "src/run.php",
        "<?php\nfunction run(): void {\n  $f = function (User $u) { return $u->bogus(); };\n  $g = fn (User $u) => $u->alsoBogus();\n}\n",
    );

    let output = p.run([] as [&str; 0]);
    let out = stdout(&output);
    assert!(out.contains("User::bogus"), "closure body not checked: {out}");
    assert!(out.contains("User::alsoBogus"), "arrow body not checked: {out}");
}

#[test]
fn non_utf8_source_is_still_analyzed() {
    // A PHP file with non-UTF-8 bytes (legal in PHP) must be analyzed, not
    // silently treated as empty. We lossily decode invalid bytes.
    let p = TempProject::new("non-utf8");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    fs::create_dir_all(p.root.join("src")).unwrap();
    // A real error, with a raw 0xFF/0xFE (invalid UTF-8) in a comment.
    let bytes = b"<?php // \xFF\xFE latin1\nnew MissingNonUtf8Class();\n";
    fs::write(p.root.join("src/bad.php"), bytes).unwrap();

    let output = p.run([] as [&str; 0]);
    assert!(!output.status.success(), "{}", stdout(&output));
    assert!(
        stdout(&output).contains("class.notFound"),
        "non-UTF-8 file should still be analyzed: {}",
        stdout(&output)
    );
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

#[test]
fn result_cache_creates_entry_and_cached_json_is_identical() {
    let p = TempProject::new("result-cache-json");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    p.write("src/bad.php", "<?php new MissingCachedJsonClass();\n");

    let first = p.run(["--error-format", "json"]);
    assert!(!first.status.success(), "{}", stdout(&first));
    assert!(cache_file_count(&p) > 0);
    let second = p.run(["--error-format", "json"]);
    assert!(!second.status.success(), "{}", stdout(&second));
    assert_eq!(stdout(&first), stdout(&second));
}

#[test]
fn result_cache_source_change_updates_output() {
    let p = TempProject::new("result-cache-change");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    p.write("src/bad.php", "<?php new MissingBeforeCacheChange();\n");

    let first = p.run(["--error-format", "json"]);
    assert!(!first.status.success(), "{}", stdout(&first));
    assert!(stdout(&first).contains("MissingBeforeCacheChange"));

    p.write("src/bad.php", "<?php class MissingBeforeCacheChange {}\n");
    let second = p.run(["--error-format", "json"]);
    assert!(second.status.success(), "{}", stdout(&second));
    assert!(!stdout(&second).contains("MissingBeforeCacheChange"));
}

#[test]
fn result_cache_deleted_files_disappear() {
    let p = TempProject::new("result-cache-delete");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    p.write("src/one.php", "<?php new MissingOneForCache();\n");
    p.write("src/two.php", "<?php new MissingTwoForCache();\n");

    let first = p.run(["--error-format", "json"]);
    assert!(!first.status.success(), "{}", stdout(&first));
    assert!(stdout(&first).contains("src/one.php"));
    assert!(stdout(&first).contains("src/two.php"));

    fs::remove_file(p.root.join("src/two.php")).unwrap();
    let second = p.run(["--error-format", "json"]);
    assert!(!second.status.success(), "{}", stdout(&second));
    let out = stdout(&second);
    assert!(out.contains("src/one.php"), "{out}");
    assert!(!out.contains("src/two.php"), "{out}");
}

#[test]
fn result_cache_write_failure_is_nonfatal() {
    let p = TempProject::new("result-cache-write-failure");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    p.write("src/bad.php", "<?php new MissingCacheWriteClass();\n");
    p.write(".phpxray", "not a directory");

    let output = p.run([] as [&str; 0]);
    assert!(!output.status.success(), "{}", stdout(&output));
    assert!(stdout(&output).contains("class.notFound"));
}

/// Whole-project signature inference: an untyped factory function in one file is
/// inferred to return `User` from its body, so a bad method call on its result in
/// another file is caught as `method.notFound` rather than swallowed as `mixed`.
#[test]
fn infers_untyped_return_across_files() {
    let p = TempProject::new("infer-untyped-return");
    write_config(&p, "level: 6\npaths:\n  - src\n");
    p.write(
        "src/user.php",
        "<?php\nclass User { public function name(): string { return \"x\"; } }\nfunction getUser() { return new User(); }\n",
    );
    p.write(
        "src/caller.php",
        "<?php\nfunction run() { return getUser()->bogus(); }\n",
    );

    // On by default: the inferred return type makes the bad call concrete.
    let on = p.run([] as [&str; 0]);
    let out = stdout(&on);
    assert!(out.contains("method.notFound"), "{out}");
    assert!(out.contains("User::bogus"), "{out}");

    // Disabled: getUser() stays `mixed`, so there is no method.notFound on User.
    let off = p.run(["--no-infer-untyped"]);
    let out = stdout(&off);
    assert!(!out.contains("method.notFound"), "{out}");
    assert!(!out.contains("User::bogus"), "{out}");
}

/// Call-site parameter inference: an untyped parameter is inferred from the
/// argument types callers pass, flowing into the body so a member call on it
/// resolves against the inferred class.
#[test]
fn infers_untyped_parameter_from_call_sites() {
    let p = TempProject::new("infer-untyped-param");
    write_config(&p, "level: 6\npaths:\n  - src\n");
    p.write(
        "src/code.php",
        "<?php\nclass Widget { public function render(): string { return \"x\"; } }\n\
         function show($w) { return $w->paint(); }\n\
         function main() { return show(new Widget()); }\n",
    );

    let on = p.run([] as [&str; 0]);
    let out = stdout(&on);
    // $w inferred as Widget from the call site; Widget has no paint().
    assert!(out.contains("method.notFound"), "{out}");
    assert!(out.contains("Widget::paint"), "{out}");

    let off = p.run(["--no-infer-untyped"]);
    let out = stdout(&off);
    assert!(!out.contains("Widget::paint"), "{out}");
}
