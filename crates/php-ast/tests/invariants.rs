//! Workspace invariants that the compiler cannot express, checked mechanically
//! so they stop being prose.

use std::path::{Path, PathBuf};

fn crates_dir() -> PathBuf {
    // crates/php-ast -> crates
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .to_path_buf()
}

fn rust_sources(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.filter_map(Result::ok) {
        let p = e.path();
        if p.is_dir() {
            rust_sources(&p, out);
        } else if p.extension().and_then(|x| x.to_str()) == Some("rs") {
            out.push(p);
        }
    }
}

/// No enum in this workspace may be `#[non_exhaustive]`.
///
/// The attribute only suppresses exhaustiveness checking *within* the defining
/// crate's workspace — so a newly added variant would silently route into some
/// `_ =>` fallback instead of failing to compile. That is the exact opposite of
/// this project's pillar (CLAUDE.md §5): the typed AST exists so the compiler
/// tells you every place a new node kind must be handled.
///
/// Held by convention until now, which meant one careless attribute could
/// disable the guarantee everything else rests on.
#[test]
fn no_enum_is_non_exhaustive() {
    let mut files = Vec::new();
    for crate_dir in std::fs::read_dir(crates_dir())
        .expect("read crates dir")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.is_dir())
    {
        rust_sources(&crate_dir.join("src"), &mut files);
    }
    assert!(
        files.len() > 50,
        "expected to scan the whole workspace, found {} files",
        files.len()
    );

    let mut offenders = Vec::new();
    for f in &files {
        let Ok(text) = std::fs::read_to_string(f) else {
            continue;
        };
        for (i, line) in text.lines().enumerate() {
            // Match the attribute, not the word in prose: a doc comment
            // explaining the rule (this crate has several) must not trip it.
            let t = line.trim_start();
            if t.starts_with("#[non_exhaustive]")
                || t.starts_with("#[cfg_attr") && t.contains("non_exhaustive")
            {
                offenders.push(format!("{}:{}", f.display(), i + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "`#[non_exhaustive]` defeats the exhaustiveness pillar (CLAUDE.md §5) — \
         a new variant would compile into an existing `_` arm instead of \
         breaking the build:\n  {}",
        offenders.join("\n  ")
    );
}
