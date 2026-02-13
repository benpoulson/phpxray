//! TDD Tier A: assert the lexer reproduces PHP's `token_get_all()` output for
//! every committed fixture under `test-fixtures/tokens/`.
//!
//! For each `NAME.php` with a paired `NAME.tokens`, we lex the source, render our
//! tokens in golden form, drop the trivia PHP emits but we don't (whitespace and
//! ordinary comments), and compare against the oracle.

use std::path::PathBuf;

use php_lexer::golden::{self, DEFAULT_IGNORED};

fn fixtures_dir() -> PathBuf {
    // crates/php-lexer -> crates -> <root>
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .unwrap()
        .join("test-fixtures/tokens")
}

#[test]
fn lexer_matches_php_token_oracle() {
    let dir = fixtures_dir();
    let mut checked = 0;
    let mut failures = Vec::new();

    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("php"))
        .collect();
    entries.sort();

    for php in entries {
        let tokens_path = php.with_extension("tokens");
        let Ok(golden_text) = std::fs::read_to_string(&tokens_path) else {
            panic!("missing golden {} (run `cargo run -p xtask -- gen-tokens`)", tokens_path.display());
        };
        let source = std::fs::read_to_string(&php).unwrap();

        let (tokens, _diags) = php_lexer::tokenize(&source);
        let ours = golden::from_tokens(&tokens, &source);

        let oracle = golden::parse(&golden_text)
            .unwrap_or_else(|e| panic!("parse {}: {e:?}", tokens_path.display()));
        let oracle = golden::filter_ignored(&oracle, DEFAULT_IGNORED);

        match golden::compare(&ours, &oracle) {
            Ok(()) => checked += 1,
            Err(diff) => {
                failures.push(format!("{}:\n{diff}", php.file_name().unwrap().to_string_lossy()));
            }
        }
    }

    assert!(
        failures.is_empty(),
        "{} fixture(s) matched, {} failed:\n\n{}",
        checked,
        failures.len(),
        failures.join("\n\n")
    );
    assert!(checked > 0, "no fixtures found in {}", dir.display());
}
