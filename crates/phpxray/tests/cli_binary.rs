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
fn stub_files_override_source_signatures() {
    // A stub file supplies a typed signature that wins over the untyped source
    // declaration, so a call with the wrong argument type is now reported.
    let p = TempProject::new("stubfiles");
    write_config(
        &p,
        "level: 5\npaths:\n  - src\nstubFiles:\n  - stubs/repo.stub\n",
    );
    p.write(
        "src/app.php",
        "<?php\nclass Repository {\n    public function find($id) { return null; }\n}\nfunction go(Repository $r): void {\n    $r->find([]);\n}\n",
    );
    p.write(
        "stubs/repo.stub",
        "<?php\nclass Repository {\n    public function find(int $id) {}\n}\n",
    );

    let output = p.run(["--error-format", "json"]);
    assert!(!output.status.success(), "{}", stdout(&output));
    let json: serde_json::Value = serde_json::from_str(&stdout(&output)).unwrap();
    assert_eq!(json["totals"]["file_errors"], 1, "{}", stdout(&output));
    assert_eq!(
        json["files"]["src/app.php"]["messages"][0]["identifier"],
        "argument.type"
    );

    // Without the stub, the untyped source signature yields no finding.
    write_config(&p, "level: 5\npaths:\n  - src\n");
    let clean = p.run(["--error-format", "json"]);
    assert!(clean.status.success(), "{}", stdout(&clean));
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

// --- `--fix` ----------------------------------------------------------------

fn read(p: &TempProject, path: &str) -> String {
    fs::read_to_string(p.root.join(path)).unwrap()
}

#[test]
fn fix_inserts_phpdoc_and_is_idempotent() {
    let p = TempProject::new("fix-basic");
    write_config(&p, "level: 6\npaths:\n  - src\n");
    p.write(
        "src/app.php",
        "<?php\nclass Repo {\n    private $rows = [];\n    public function set(): void { $this->rows = ['a']; }\n    public function find($id) {\n        return $id;\n    }\n}\n$r = new Repo();\n$r->find(7);\n",
    );

    let first = p.run(["--fix", "--no-progress"]);
    let err = String::from_utf8_lossy(&first.stderr).into_owned();
    assert!(err.contains("Fixed 3 finding(s) in 1 file(s)."), "{err}");

    let fixed = read(&p, "src/app.php");
    assert_eq!(
        fixed,
        "<?php\nclass Repo {\n    /** @var list<string> */\n    private $rows = [];\n    public function set(): void { $this->rows = ['a']; }\n    /**\n     * @param int $id\n     * @return int\n     */\n    public function find($id) {\n        return $id;\n    }\n}\n$r = new Repo();\n$r->find(7);\n"
    );

    // Second run: the repaired declarations no longer report, nothing changes.
    let second = p.run(["--fix", "--no-progress"]);
    let err2 = String::from_utf8_lossy(&second.stderr).into_owned();
    assert!(err2.contains("Fixed 0 finding(s) in 0 file(s)."), "{err2}");
    assert_eq!(read(&p, "src/app.php"), fixed);
    let out2 = stdout(&second);
    assert!(!out2.contains("missingType.property"), "{out2}");
    assert!(!out2.contains("find() has parameter"), "{out2}");
}

#[test]
fn fix_respects_baseline() {
    let p = TempProject::new("fix-baseline");
    write_config(&p, "level: 6\npaths:\n  - src\n");
    p.write(
        "src/app.php",
        "<?php\nclass C {\n    private $v = 1;\n}\n",
    );
    let baseline = p.run(["--generate-baseline", "--no-progress"]);
    assert!(baseline.status.success());
    write_config(
        &p,
        "level: 6\npaths:\n  - src\nbaseline: phpxray-baseline.yaml\n",
    );

    let original = read(&p, "src/app.php");
    let fixed = p.run(["--fix", "--no-progress"]);
    let err = String::from_utf8_lossy(&fixed.stderr).into_owned();
    assert!(err.contains("Fixed 0 finding(s) in 0 file(s)."), "{err}");
    assert_eq!(read(&p, "src/app.php"), original, "baselined finding must not be fixed");
}

#[test]
fn early_terminating_calls_end_branches() {
    let p = TempProject::new("early-terminating");
    // Without config: the dd() branch falls through, so $y is maybe-undefined
    // at level 1 (and the $this->fail() variant likewise).
    let src = r#"<?php
function myDd(string $m): string { return $m; }
function f(bool $c): void {
    if ($c) { myDd('x'); } else { $y = 1; }
    echo $y;
}
class T {
    public function fail(string $m): string { return $m; }
    public function g(bool $c): void {
        if ($c) { $this->fail('x'); } else { $z = 1; }
        echo $z;
    }
}
"#;
    p.write("src/app.php", src);
    write_config(&p, "level: 1\npaths:\n  - src\n");
    let out = stdout(&p.run(["--no-progress"]));
    assert!(out.contains("$y might not be defined"), "{out}");
    assert!(out.contains("$z might not be defined"), "{out}");

    // With the calls configured as terminating, the branches end like `throw`
    // and both variables are definitely assigned on every fall-through path.
    write_config(
        &p,
        "level: 1\npaths:\n  - src\nearlyTerminatingFunctionCalls:\n  - myDd\nearlyTerminatingMethodCalls:\n  T:\n    - fail\n",
    );
    let out = stdout(&p.run(["--no-progress"]));
    assert!(!out.contains("might not be defined"), "{out}");
}

#[test]
fn clear_result_cache_subcommand() {
    let p = TempProject::new("clear-cache");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    p.write("src/ok.php", "<?php\nclass C {}\n");

    // Prime the cache, then clear it.
    let run = p.run(["--no-progress"]);
    assert!(run.status.success());
    assert!(cache_file_count(&p) > 0, "cache should be primed");
    let clear = p.run(["clear-result-cache"]);
    assert!(clear.status.success(), "{clear:?}");
    assert_eq!(cache_file_count(&p), 0);

    // Clearing an already-empty cache still succeeds.
    let again = p.run(["clear-result-cache"]);
    assert!(again.status.success());
}

#[test]
fn debug_prints_files_and_bypasses_cache() {
    let p = TempProject::new("debug-flag");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    p.write("src/ok.php", "<?php\nclass C {}\n");

    let out = p.run(["--debug", "--no-progress"]);
    assert!(out.status.success());
    let err = String::from_utf8_lossy(&out.stderr).into_owned();
    assert!(err.contains("src/ok.php"), "{err}");
    assert_eq!(cache_file_count(&p), 0, "--debug must not write the cache");
}

#[test]
fn fail_without_result_cache_guard() {
    let p = TempProject::new("fail-without-cache");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    p.write("src/ok.php", "<?php\nclass C {}\n");

    // Cold: fresh analysis was required -> exit 2.
    let cold = p.run(["--fail-without-result-cache", "--no-progress"]);
    assert_eq!(cold.status.code(), Some(2), "{cold:?}");
    // Warm: the cache primed by the failed-guard run now hits -> exit 0.
    let warm = p.run(["--fail-without-result-cache", "--no-progress"]);
    assert_eq!(warm.status.code(), Some(0), "{warm:?}");
}

#[test]
fn empty_baseline_refused_unless_allowed() {
    let p = TempProject::new("empty-baseline");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    p.write("src/ok.php", "<?php\nclass C {}\n");

    let refused = p.run(["--generate-baseline", "--no-progress"]);
    assert_eq!(refused.status.code(), Some(2), "{refused:?}");
    assert!(!p.root.join("phpxray-baseline.yaml").exists());

    let allowed = p.run([
        "--generate-baseline",
        "--allow-empty-baseline",
        "--no-progress",
    ]);
    assert!(allowed.status.success(), "{allowed:?}");
    assert!(p.root.join("phpxray-baseline.yaml").exists());
}

#[test]
fn result_cache_path_config_is_honored() {
    let p = TempProject::new("cache-path");
    write_config(
        &p,
        "level: 0\npaths:\n  - src\nresultCachePath: var/cache\n",
    );
    p.write("src/ok.php", "<?php\nclass C {}\n");

    let run = p.run(["--no-progress"]);
    assert!(run.status.success());
    let custom = fs::read_dir(p.root.join("var/cache"))
        .map(|entries| entries.filter_map(Result::ok).count())
        .unwrap_or(0);
    assert!(custom > 0, "custom cache dir should be used");
    assert_eq!(cache_file_count(&p), 0, "default cache dir should be empty");

    // clear-result-cache honors the configured path too.
    let clear = p.run(["clear-result-cache"]);
    assert!(clear.status.success());
    assert!(!p.root.join("var/cache").exists());
}

#[test]
fn neon_baseline_generate_and_consume_round_trip() {
    let p = TempProject::new("neon-baseline");
    write_config(&p, "level: 0\npaths:\n  - src\n");
    p.write("src/app.php", "<?php\nunknown_fn_xyz();\n");

    // Findings exist without a baseline.
    let bare = p.run(["--no-progress"]);
    assert_eq!(bare.status.code(), Some(1));

    // Generate a phpstan-compatible NEON baseline.
    let gen = p.run(["--generate-baseline", "phpstan-baseline.neon", "--no-progress"]);
    assert!(gen.status.success());
    let neon = read(&p, "phpstan-baseline.neon");
    assert!(neon.starts_with("parameters:\n\tignoreErrors:\n"), "{neon}");
    assert!(neon.contains("identifier: function.notFound"), "{neon}");
    assert!(neon.contains("path: src/app.php"), "{neon}");

    // Consuming it suppresses everything (clean exit 0).
    write_config(
        &p,
        "level: 0\npaths:\n  - src\nbaseline: phpstan-baseline.neon\n",
    );
    let with_baseline = p.run(["--no-progress"]);
    assert_eq!(
        with_baseline.status.code(),
        Some(0),
        "{}",
        stdout(&with_baseline)
    );
}

#[test]
fn phpstan_written_neon_baseline_loads() {
    // The exact shape phpstan writes (tabs, quoted message, identifier).
    let p = TempProject::new("phpstan-neon-baseline");
    p.write("src/app.php", "<?php\nunknown_fn_xyz();\n");
    p.write(
        "phpstan-baseline.neon",
        "parameters:\n\tignoreErrors:\n\t\t-\n\t\t\tmessage: '#^Function unknown_fn_xyz not found\\.$#'\n\t\t\tidentifier: function.notFound\n\t\t\tcount: 1\n\t\t\tpath: src/app.php\n",
    );
    write_config(
        &p,
        "level: 0\npaths:\n  - src\nbaseline: phpstan-baseline.neon\n",
    );
    let out = p.run(["--no-progress"]);
    assert_eq!(out.status.code(), Some(0), "{}", stdout(&out));
}

#[test]
fn fix_skips_non_utf8_file() {
    let p = TempProject::new("fix-non-utf8");
    write_config(&p, "level: 6\npaths:\n  - src\n");
    let bytes: &[u8] = b"<?php // \xFF\xFE\nclass C {\n    private $v = 1;\n}\n";
    fs::create_dir_all(p.root.join("src")).unwrap();
    fs::write(p.root.join("src/bad.php"), bytes).unwrap();

    let fixed = p.run(["--fix", "--no-progress"]);
    let err = String::from_utf8_lossy(&fixed.stderr).into_owned();
    assert!(
        err.contains("Fixed 0 finding(s) in 0 file(s).") && err.contains("Skipped"),
        "{err}"
    );
    assert_eq!(fs::read(p.root.join("src/bad.php")).unwrap(), bytes);
}

#[test]
fn fix_conflicts_with_watch_and_baseline_generation() {
    let p = TempProject::new("fix-exclusive");
    write_config(&p, "level: 6\npaths:\n  - src\n");
    p.write("src/app.php", "<?php\n");
    let watch = p.run(["--fix", "--watch"]);
    assert_eq!(watch.status.code(), Some(2), "{}", stdout(&watch));
    let gen = p.run(["--fix", "--generate-baseline"]);
    assert_eq!(gen.status.code(), Some(2), "{}", stdout(&gen));
}

#[test]
fn fix_inserts_into_existing_docblock_and_array_param() {
    let p = TempProject::new("fix-existing-doc");
    write_config(&p, "level: 6\npaths:\n  - src\n");
    p.write(
        "src/app.php",
        "<?php\n/**\n * Maps ids.\n */\nfunction mapIds(array $ids): array {\n    return array_values($ids);\n}\nmapIds([1, 2]);\n",
    );

    let fixed = p.run(["--fix", "--no-progress"]);
    let err = String::from_utf8_lossy(&fixed.stderr).into_owned();
    assert!(err.contains("in 1 file(s)."), "{err}");
    let content = read(&p, "src/app.php");
    // Round 1 fixes the param from call sites; with `$ids` typed, round 2 can
    // refine the bare `array` return from the body too (the fix loop iterates).
    assert!(
        content.contains(" * Maps ids.\n * @param list<int> $ids\n * @return list<int>\n */"),
        "{content}"
    );
}
