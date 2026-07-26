//! TDD Tier C, in-repo: the parser is **total**.
//!
//! `xtask corpus` runs this invariant over the 5,300-file Zend suite, but that
//! needs a `php-src` checkout that CI does not have — so the totality guarantee
//! everything else rests on had no automated coverage at all. These fixtures are
//! the committed canary: adversarial inputs (depth-guard, unterminated
//! constructs, lexer state edges, non-UTF-8 bytes) chosen because they are what
//! actually breaks a hand-written recursive-descent parser. Normal PHP is
//! already covered by the golden tokens and the AST snapshots.
//!
//! The contract, for **every** input, valid or not:
//!   * lexing and parsing never panic,
//!   * they terminate (a non-advancing recovery loop hangs this test),
//!   * a fixture named `valid_*` additionally parses with zero diagnostics.

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::PathBuf;

fn fixtures_dir() -> PathBuf {
    // crates/php-parser -> crates -> <root>
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .unwrap()
        .join("test-fixtures/totality")
}

/// Read as bytes, not `String`: PHP sources are byte arrays and may hold
/// invalid UTF-8, which the parser must survive.
fn read_source(path: &PathBuf) -> String {
    let bytes = std::fs::read(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    String::from_utf8_lossy(&bytes).into_owned()
}

#[test]
fn parser_is_total_over_adversarial_fixtures() {
    let dir = fixtures_dir();
    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("php"))
        .collect();
    entries.sort();

    let mut checked = 0;
    for path in entries {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let src = read_source(&path);

        // Lexing must not panic (checked separately from parsing so a lexer
        // fault is not misattributed to the parser).
        let lexed = catch_unwind(AssertUnwindSafe(|| php_lexer::tokenize(&src).0.len()));
        assert!(lexed.is_ok(), "lexer panicked on {name}");

        // Parsing must not panic, and must produce a program either way.
        let parsed = catch_unwind(AssertUnwindSafe(|| {
            let r = php_parser::parse(&src);
            (r.program.stmts.len(), r.diagnostics.len(), r.has_errors())
        }));
        let Ok((_stmts, diags, has_errors)) = parsed else {
            panic!("parser panicked on {name}");
        };

        if name.starts_with("valid_") {
            assert!(
                !has_errors,
                "{name} is valid PHP but produced {diags} diagnostic(s)"
            );
        }
        checked += 1;
    }

    // The fixtures are the test. An empty directory reporting success is the
    // exact failure mode this file exists to prevent.
    assert!(
        checked >= 20,
        "expected the totality fixtures to be present, found {checked}"
    );
}

/// Spans must stay inside the source. A span that lies is silently wrong
/// everywhere downstream — diagnostics point at the wrong bytes, and
/// `Span::text` would panic on a slice out of bounds.
#[test]
fn spans_stay_within_the_source() {
    let dir = fixtures_dir();
    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("php"))
        .collect();
    entries.sort();

    for path in entries {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let src = read_source(&path);
        let len = src.len() as u32;
        let r = php_parser::parse(&src);

        php_ast::walk::for_each_expr(&r.program, &mut |e| {
            assert!(
                e.span.start <= e.span.end && e.span.end <= len,
                "{name}: expression span {:?} escapes a {len}-byte source",
                e.span
            );
        });
        php_ast::walk::for_each_stmt(&r.program, &mut |s| {
            assert!(
                s.span.start <= s.span.end && s.span.end <= len,
                "{name}: statement span {:?} escapes a {len}-byte source",
                s.span
            );
        });
        for d in &r.diagnostics {
            assert!(
                d.primary.start <= d.primary.end && d.primary.end <= len,
                "{name}: diagnostic span {:?} escapes a {len}-byte source",
                d.primary
            );
        }
    }
}
