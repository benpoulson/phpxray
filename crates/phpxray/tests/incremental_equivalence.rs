//! The incremental session's contract: after ANY edit, its report must be
//! byte-identical to a fresh batch run over the same tree. Each scenario
//! mutates a temp project, runs both engines, and diffs the full finding list
//! (path, line, column, message, identifier, severity) including order.
//!
//! Scenarios are chosen to stress the invalidation machinery specifically:
//! body-only edits (must NOT invalidate surface dependents — and must still be
//! correct), signature edits (must invalidate callers), type-flow chains where
//! the dependent never names the changed class, file adds/removes, cross-file
//! located findings whose lines shift, and config changes.

use phpxray::incremental::{ChangeHint, Session};
use phpxray::{run_with_options, Report, RunOptions};
use php_config::Config;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

struct Project {
    root: PathBuf,
    config: Config,
    session: Session,
}

impl Project {
    fn new(level: &str, files: &[(&str, &str)]) -> Project {
        let root = temp_dir("incr-equiv");
        for (rel, src) in files {
            write_file(&root, rel, src);
        }
        let config = Config::from_yaml(&format!("level: {level}\npaths:\n  - src\n")).unwrap();
        let session = Session::new(&config);
        Project {
            root,
            config,
            session,
        }
    }

    /// Like [`Project::new`] but with a full config YAML (e.g. to set
    /// `stubFiles`). Files are written before the session is constructed.
    fn new_with_config(config_yaml: &str, files: &[(&str, &str)]) -> Project {
        let root = temp_dir("incr-equiv");
        for (rel, src) in files {
            write_file(&root, rel, src);
        }
        let config = Config::from_yaml(config_yaml).unwrap();
        let session = Session::new(&config);
        Project {
            root,
            config,
            session,
        }
    }

    fn write(&self, rel: &str, src: &str) {
        write_file(&self.root, rel, src);
    }

    fn delete(&self, rel: &str) {
        fs::remove_file(self.root.join(rel)).unwrap();
    }

    /// Run the incremental session (with `hint`) and a fresh batch run; assert
    /// they produce identical reports, and return the (shared) findings as
    /// comparable strings.
    fn check(&mut self, label: &str, hint: Option<&ChangeHint>) -> Vec<String> {
        let incremental = self.session.run(&self.config, &self.root, hint);
        let batch = run_with_options(
            &self.config,
            &self.root,
            RunOptions {
                progress: false,
                use_result_cache: false,
                ..RunOptions::default()
            },
        );
        let inc = render(&incremental);
        let full = render(&batch);
        assert_eq!(
            inc, full,
            "{label}: incremental report diverged from batch report"
        );
        assert_eq!(
            incremental.files_analyzed, batch.files_analyzed,
            "{label}: files_analyzed diverged"
        );
        assert_eq!(
            incremental.files_scanned, batch.files_scanned,
            "{label}: files_scanned diverged"
        );
        inc
    }

    /// A hint naming the given project-relative files as modified in place.
    fn hint(&self, rels: &[&str]) -> ChangeHint {
        ChangeHint {
            paths: rels.iter().map(|r| self.root.join(r)).collect(),
            saw_creates_or_removes: false,
        }
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn render(report: &Report) -> Vec<String> {
    report
        .findings
        .iter()
        .map(|f| {
            format!(
                "{}:{}:{} [{}] {} ({:?})",
                f.path,
                f.line,
                f.column,
                f.identifier.unwrap_or("-"),
                f.message,
                f.severity
            )
        })
        .collect()
}

fn write_file(root: &Path, rel: &str, src: &str) {
    let path = root.join(rel);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, src).unwrap();
}

fn temp_dir(label: &str) -> PathBuf {
    // A timestamp alone collides across parallel tests (macOS clock resolution
    // is coarser than a nanosecond) — disambiguate with a process-wide counter.
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "phpxray-{label}-{}-{id}-{now}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    dir
}

#[test]
fn stub_file_edit_stays_equivalent() {
    // A stub supplies a typed signature that wins over untyped source; editing
    // the stub between passes must re-analyze dependents and stay batch-identical.
    let mut p = Project::new_with_config(
        "level: 5\npaths:\n  - src\nstubFiles:\n  - stubs/lib.stub\n",
        &[
            (
                "src/app.php",
                "<?php\nfunction take(Lib $l): void { $l->work([]); }\n",
            ),
            (
                "src/lib.php",
                "<?php\nclass Lib { public function work($x) {} }\n",
            ),
            (
                "stubs/lib.stub",
                "<?php\nclass Lib { public function work(int $x) {} }\n",
            ),
        ],
    );
    // Initial: stub types `work(int)`, so `work([])` is an argument.type error.
    let before = p.check("initial", None);
    assert!(!before.is_empty(), "stub-typed param should flag array arg");

    // Edit the stub so the param accepts arrays: the finding must disappear, and
    // the session (which doesn't watch the stub file) must still match batch.
    p.write(
        "stubs/lib.stub",
        "<?php\nclass Lib { public function work(array $x) {} }\n",
    );
    let hint = p.hint(&["src/app.php"]);
    let after = p.check("stub edit", Some(&hint));
    assert!(after.is_empty(), "widened stub param should clear the finding");
}

#[test]
fn body_only_edit_stays_equivalent() {
    let mut p = Project::new(
        "max",
        &[
            (
                "src/helper.php",
                "<?php function helper(): int { return 1; }\n",
            ),
            (
                "src/caller.php",
                "<?php function caller(): int { return helper(); }\n",
            ),
        ],
    );
    let before = p.check("initial", None);

    // Body-only edit: same signature, new (wrong) return value.
    p.write(
        "src/helper.php",
        "<?php function helper(): int { return \"oops\"; }\n",
    );
    let hint = p.hint(&["src/helper.php"]);
    let after = p.check("body edit", Some(&hint));
    assert_ne!(before, after, "the edit should introduce a finding");
}

#[test]
fn signature_change_invalidates_callers() {
    let mut p = Project::new(
        "max",
        &[
            (
                "src/api.php",
                "<?php function api(int $x): int { return $x; }\n",
            ),
            (
                "src/caller.php",
                "<?php function go(): int { return api(5); }\n",
            ),
        ],
    );
    let before = p.check("initial", None);
    assert!(
        before.is_empty(),
        "expected a clean start, got: {before:#?}"
    );

    // Param type flips: the call site in the OTHER file must light up.
    p.write(
        "src/api.php",
        "<?php function api(string $x): int { return 1; }\n",
    );
    let hint = p.hint(&["src/api.php"]);
    let after = p.check("signature edit", Some(&hint));
    assert!(
        after.iter().any(|f| f.contains("caller.php")),
        "caller should report a finding after the signature change, got: {after:#?}"
    );
}

#[test]
fn type_flow_chain_invalidates_unnamed_dependency() {
    // caller.php never names User — it reaches it via Repo::find()'s return
    // type. Editing User must still re-check caller.php.
    let mut p = Project::new(
        "max",
        &[
            (
                "src/user.php",
                "<?php class User { public function getName(): string { return \"n\"; } }\n",
            ),
            (
                "src/repo.php",
                "<?php class Repo { public function find(): User { return new User(); } }\n",
            ),
            (
                "src/caller.php",
                "<?php function takes(string $s): void {}\nfunction go(Repo $r): void { takes($r->find()->getName()); }\n",
            ),
        ],
    );
    let before = p.check("initial", None);
    assert!(before.is_empty(), "expected clean start, got: {before:#?}");

    // User::getName now returns int — caller.php's takes() argument breaks.
    p.write(
        "src/user.php",
        "<?php class User { public function getName(): int { return 1; } }\n",
    );
    let hint = p.hint(&["src/user.php"]);
    let after = p.check("type-flow edit", Some(&hint));
    assert!(
        after.iter().any(|f| f.contains("caller.php")),
        "caller should report after the chained type change, got: {after:#?}"
    );
}

#[test]
fn inheritance_chain_invalidates_descendant_users() {
    // caller uses B; the edited method lives on grandparent C.
    let mut p = Project::new(
        "max",
        &[
            (
                "src/c.php",
                "<?php class C { public function m(): string { return \"s\"; } }\n",
            ),
            ("src/b.php", "<?php class B extends C {}\n"),
            (
                "src/caller.php",
                "<?php function takes(string $s): void {}\nfunction go(B $b): void { takes($b->m()); }\n",
            ),
        ],
    );
    let before = p.check("initial", None);
    assert!(before.is_empty(), "expected clean start, got: {before:#?}");

    p.write(
        "src/c.php",
        "<?php class C { public function m(): int { return 1; } }\n",
    );
    let hint = p.hint(&["src/c.php"]);
    let after = p.check("ancestor edit", Some(&hint));
    assert!(
        after.iter().any(|f| f.contains("caller.php")),
        "caller should report after the grandparent method change, got: {after:#?}"
    );
}

#[test]
fn added_file_resolves_previously_unknown_symbol() {
    let mut p = Project::new(
        "0",
        &[(
            "src/caller.php",
            "<?php function go(): void { new Widget(); }\n",
        )],
    );
    let before = p.check("initial", None);
    assert!(
        before.iter().any(|f| f.contains("Widget")),
        "Widget should be unknown initially, got: {before:#?}"
    );

    p.write("src/widget.php", "<?php class Widget {}\n");
    let hint = ChangeHint {
        paths: vec![p.root.join("src/widget.php")],
        saw_creates_or_removes: true,
    };
    let after = p.check("file added", Some(&hint));
    assert!(
        !after.iter().any(|f| f.contains("Widget")),
        "Widget should now resolve, got: {after:#?}"
    );
}

#[test]
fn removed_file_unresolves_its_symbols() {
    let mut p = Project::new(
        "0",
        &[
            ("src/widget.php", "<?php class Widget {}\n"),
            (
                "src/caller.php",
                "<?php function go(): void { new Widget(); }\n",
            ),
        ],
    );
    let before = p.check("initial", None);
    assert!(before.is_empty(), "expected clean start, got: {before:#?}");

    p.delete("src/widget.php");
    let hint = ChangeHint {
        paths: vec![p.root.join("src/widget.php")],
        saw_creates_or_removes: true,
    };
    let after = p.check("file removed", Some(&hint));
    assert!(
        after.iter().any(|f| f.contains("Widget")),
        "Widget should be unknown after removal, got: {after:#?}"
    );
}

#[test]
fn cross_file_located_findings_track_line_shifts() {
    // The callback body lives in lib.php; analyzing caller.php emits a context
    // diagnostic AT lib.php's location. Shifting lib.php's lines must relocate
    // that finding even though caller.php itself did not change.
    let mut p = Project::new(
        "max",
        &[
            (
                "src/lib.php",
                "<?php function pick($row) { return $row['name']; }\n",
            ),
            (
                "src/caller.php",
                "<?php function go(): void { array_map('pick', [['name' => 1]]); }\n",
            ),
        ],
    );
    let before = p.check("initial", None);

    // Prepend a comment line: every finding located in lib.php shifts by one.
    p.write(
        "src/lib.php",
        "<?php\n// shifted\nfunction pick($row) { return $row['name']; }\n",
    );
    let hint = p.hint(&["src/lib.php"]);
    let after = p.check("line shift", Some(&hint));
    // Equivalence is the real assertion; sanity-check the shift if any finding
    // targets lib.php.
    let _ = (before, after);
}

#[test]
fn removing_the_target_of_cross_file_findings_stays_equivalent() {
    // caller.php's analysis emits a context diagnostic INTO lib.php (callback
    // body). Removing lib.php must re-analyze the producer so no findings
    // remain located at the dead path.
    let mut p = Project::new(
        "max",
        &[
            (
                "src/lib.php",
                "<?php function pick($row) { return $row['name']; }\n",
            ),
            (
                "src/caller.php",
                "<?php function go(): void { array_map('pick', [['name' => 1]]); }\n",
            ),
        ],
    );
    p.check("initial", None);

    p.delete("src/lib.php");
    let hint = ChangeHint {
        paths: vec![p.root.join("src/lib.php")],
        saw_creates_or_removes: true,
    };
    let after = p.check("target removed", Some(&hint));
    assert!(
        !after.iter().any(|f| f.starts_with("src/lib.php")),
        "no findings may remain at the removed path, got: {after:#?}"
    );
}

#[test]
fn interprocedural_body_edit_updates_callers() {
    // helper has NO declared return type: callers infer it from the body.
    // Editing only the body (surface unchanged) must still re-check callers.
    let mut p = Project::new(
        "max",
        &[
            ("src/helper.php", "<?php function helper() { return 1; }\n"),
            (
                "src/caller.php",
                "<?php function takes(int $x): void {}\nfunction go(): void { takes(helper()); }\n",
            ),
        ],
    );
    let before = p.check("initial", None);

    p.write(
        "src/helper.php",
        "<?php function helper() { return \"str\"; }\n",
    );
    let hint = p.hint(&["src/helper.php"]);
    let after = p.check("interprocedural body edit", Some(&hint));
    // If the engine infers through bodies here, the caller must light up in
    // BOTH engines (equivalence already asserted in check()).
    let _ = (before, after);
}

#[test]
fn inferred_signature_change_invalidates_dependents() {
    // The cross-file *inferred-signature* chain: base() and mid() have no
    // declared returns; mid's stored (inferred) return comes from base's body,
    // and dependent.php consumes mid() through the stored index. Editing ONLY
    // base's body changes mid's inferred signature while every file's *declared*
    // artifact is unchanged — dependent.php must still re-analyze (its
    // `takes(int)` call flips from clean to argument.type). This exercises the
    // inferred-signature diff feeding the invalidation set; declared-artifact
    // diffing alone would leave dependent.php stale.
    let mut p = Project::new(
        "max",
        &[
            ("src/base.php", "<?php function base() { return 1; }\n"),
            ("src/mid.php", "<?php function mid() { return base(); }\n"),
            (
                "src/dependent.php",
                "<?php function takes(int $x): void {}\nfunction go(): void { takes(mid()); }\n",
            ),
        ],
    );
    let before = p.check("initial", None);

    p.write("src/base.php", "<?php function base() { return \"str\"; }\n");
    let hint = p.hint(&["src/base.php"]);
    let after = p.check("inferred signature chain edit", Some(&hint));
    assert_ne!(
        before, after,
        "the edit must change dependent.php's findings (argument.type appears)"
    );
}

#[test]
fn level_change_reanalyzes_everything() {
    let mut p = Project::new(
        "0",
        &[(
            "src/a.php",
            "<?php function f(): int { return \"wrong\"; }\n",
        )],
    );
    let at0 = p.check("level 0", None);

    p.config = Config::from_yaml("level: max\npaths:\n  - src\n").unwrap();
    let atmax = p.check("level max", Some(&ChangeHint::default()));
    assert_ne!(at0, atmax, "raising the level should surface return.type");
}

#[test]
fn ignore_change_resuppresses_without_breaking_equivalence() {
    let mut p = Project::new(
        "max",
        &[(
            "src/a.php",
            "<?php function f(): int { return \"wrong\"; }\n",
        )],
    );
    let before = p.check("initial", None);
    assert!(!before.is_empty());

    let mut config = Config::from_yaml("level: max\npaths:\n  - src\n").unwrap();
    config.ignore = Config::from_yaml(
        "level: max\npaths: [src]\nignore:\n  - identifier: return.type\n",
    )
    .unwrap()
    .ignore;
    config.report_unmatched_ignored = false;
    p.config = config;
    let after = p.check("with ignore", Some(&ChangeHint::default()));
    assert!(
        !after.iter().any(|f| f.contains("return.type")),
        "return.type should be suppressed, got: {after:#?}"
    );
}

#[test]
fn noop_save_keeps_report_stable() {
    let mut p = Project::new(
        "max",
        &[(
            "src/a.php",
            "<?php function f(): int { return \"wrong\"; }\n",
        )],
    );
    let before = p.check("initial", None);

    // Re-write identical content (an editor save without changes).
    p.write(
        "src/a.php",
        "<?php function f(): int { return \"wrong\"; }\n",
    );
    let hint = p.hint(&["src/a.php"]);
    let after = p.check("no-op save", Some(&hint));
    assert_eq!(before, after);
}

#[test]
fn invalidation_is_selective() {
    // Five files: helper + caller (depends on helper), and three bystanders
    // with no relation to helper. A body-only edit to helper must re-analyze
    // ONLY helper (its surface is unchanged, no body deps exist on it at the
    // declared-signature level); the bystanders must be untouched.
    let mut p = Project::new(
        "max",
        &[
            (
                "src/helper.php",
                "<?php function helper(): int { return 1; }\n",
            ),
            (
                "src/caller.php",
                "<?php function go(): int { return helper(); }\n",
            ),
            ("src/by1.php", "<?php function by1(): int { return 1; }\n"),
            ("src/by2.php", "<?php function by2(): int { return 2; }\n"),
            ("src/by3.php", "<?php function by3(): int { return 3; }\n"),
        ],
    );
    p.check("initial", None);
    assert_eq!(p.session.last_pass().files_reanalyzed, 5, "first pass = all");

    // Body-only edit (signature identical): selective.
    p.write(
        "src/helper.php",
        "<?php function helper(): int { return 2; }\n",
    );
    let hint = p.hint(&["src/helper.php"]);
    p.check("body edit", Some(&hint));
    let stats = p.session.last_pass();
    assert_eq!(stats.files_changed, 1);
    assert!(
        stats.files_reanalyzed <= 2,
        "body-only edit should re-analyze at most helper + body-dependents, \
         re-analyzed {} of {}",
        stats.files_reanalyzed,
        stats.files_total
    );

    // Signature edit: helper + caller, but never the bystanders.
    p.write(
        "src/helper.php",
        "<?php function helper(): string { return \"s\"; }\n",
    );
    let hint = p.hint(&["src/helper.php"]);
    p.check("signature edit", Some(&hint));
    let stats = p.session.last_pass();
    assert!(
        stats.files_reanalyzed >= 2,
        "signature edit must reach the caller"
    );
    assert!(
        stats.files_reanalyzed < 5,
        "signature edit must NOT re-analyze unrelated bystanders, \
         re-analyzed {} of {}",
        stats.files_reanalyzed,
        stats.files_total
    );
}

#[test]
fn unhinted_passes_match_hinted_passes() {
    let mut p = Project::new(
        "max",
        &[
            (
                "src/api.php",
                "<?php function api(int $x): int { return $x; }\n",
            ),
            (
                "src/caller.php",
                "<?php function go(): int { return api(5); }\n",
            ),
        ],
    );
    p.check("initial", None);
    p.write(
        "src/api.php",
        "<?php function api(string $x): int { return 1; }\n",
    );
    // No hint at all: the session must rediscover and still match the batch.
    p.check("unhinted edit", None);
}
