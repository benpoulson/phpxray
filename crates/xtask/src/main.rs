//! `xtask` — project automation. Run as `cargo run -p xtask -- <command>`.
//!
//! Commands:
//!   corpus [DIR]        Parse every `.phpt` under DIR (default: php-src/Zend/tests)
//!                       and report counts. The TDD Tier-C smoke check.
//!   phpt-extract FILE   Print the `--FILE--` body of a single `.phpt`.
//!   gen-tokens          (M1) Generate golden token fixtures via PHP. Requires PHP.

use std::collections::BTreeMap;
use std::io::Write;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};

use php_lexer::golden::{self, DEFAULT_IGNORED};
use walkdir::WalkDir;
use xtask::phpt;

mod astdump;

fn workspace_root() -> PathBuf {
    // crates/xtask -> crates -> <root>
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("workspace root")
        .to_path_buf()
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("corpus") => cmd_corpus(args.get(1).map(PathBuf::from)),
        Some("resolve") => cmd_resolve(args.get(1).map(PathBuf::from)),
        Some("index") => cmd_index(args.get(1).map(PathBuf::from)),
        Some("triage") => cmd_triage(args.get(1).map(PathBuf::from)),
        Some("diag") => cmd_diag(args.get(1).map(PathBuf::from)),
        Some("difftokens") => cmd_difftokens(&args[1..]),
        Some("astdiff") => cmd_astdiff(&args[1..]),
        Some("astone") => {
            // Print OUR canonical dump for a .phpt's --FILE-- (for eyeball diffs).
            let path = PathBuf::from(args.get(1).cloned().unwrap_or_default());
            let text = std::fs::read_to_string(&path).unwrap_or_default();
            let source = phpt::extract_file_section(&text).unwrap_or_default();
            let r = php_parser::parse(&source);
            use std::io::Write;
            let _ = std::io::stdout().write_all(&astdump::dump(&r.program, &source, &r.interner));
            ExitCode::SUCCESS
        }
        Some("phpt-extract") => cmd_phpt_extract(args.get(1).map(PathBuf::from)),
        Some("gen-tokens") => cmd_gen_tokens(),
        Some("gen-stubs") => cmd_gen_stubs(),
        Some(other) => {
            eprintln!("unknown command: {other}");
            usage();
            ExitCode::FAILURE
        }
        None => {
            usage();
            ExitCode::FAILURE
        }
    }
}

fn usage() {
    eprintln!(
        "usage: cargo run -p xtask -- <command>\n\
         \n\
         commands:\n\
         \x20 corpus [DIR]        parse every .phpt under DIR (default php-src/Zend/tests)\n\
         \x20 difftokens [DIR] [--limit N]\n\
         \x20                     diff our tokens vs PHP token_get_all over the corpus (requires PHP)\n\
         \x20 phpt-extract FILE   print the --FILE-- body of a .phpt\n\
         \x20 gen-tokens          generate golden token fixtures (requires PHP; M1)"
    );
}

/// Differential token check: lex every corpus `--FILE--` with both our lexer and
/// PHP's `token_get_all()` and report the first divergence per file, tallied by
/// the oracle token name that we got wrong. A dev oracle (needs PHP); surfaces
/// the remaining lexer worklist. Trivia PHP emits but we drop is filtered out.
fn cmd_difftokens(args: &[String]) -> ExitCode {
    let mut dir: Option<PathBuf> = None;
    let mut limit = usize::MAX;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--limit" => limit = it.next().and_then(|s| s.parse().ok()).unwrap_or(usize::MAX),
            _ => dir = Some(PathBuf::from(a)),
        }
    }
    let root = workspace_root();
    let dir = dir.unwrap_or_else(|| root.join("php-src/Zend/tests"));
    let helper = root.join("crates/xtask/php/gen_golden.php");
    if Command::new("php").arg("--version").output().is_err() {
        eprintln!("`php` not found on PATH (brew install php)");
        return ExitCode::FAILURE;
    }

    let mut files: Vec<PathBuf> = WalkDir::new(&dir)
        .into_iter()
        .filter_map(Result::ok)
        .map(|e| e.into_path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("phpt"))
        .collect();
    files.sort();

    let (mut checked, mut matched) = (0usize, 0usize);
    let mut by_oracle: BTreeMap<String, usize> = BTreeMap::new();
    let mut examples: Vec<String> = Vec::new();

    for path in files.into_iter().take(limit) {
        let Ok(text) = std::fs::read_to_string(&path) else { continue };
        let Some(source) = phpt::extract_file_section(&text) else { continue };
        let Some(golden_text) = run_php_tokens(&helper, &source) else { continue };
        let Ok(oracle) = golden::parse(&golden_text) else { continue };
        let oracle = golden::filter_ignored(&oracle, DEFAULT_IGNORED);

        let ours = match catch_unwind(AssertUnwindSafe(|| {
            let (toks, _) = php_lexer::tokenize(&source);
            golden::from_tokens(&toks, &source)
        })) {
            Ok(v) => v,
            Err(_) => continue,
        };

        checked += 1;
        match first_divergence(&ours, &oracle) {
            None => matched += 1,
            Some((o, u)) => {
                *by_oracle.entry(format!("{o} (we said {u})")).or_default() += 1;
                // Skip the known-deferred categories so examples surface real bugs.
                let deferred = o.starts_with("T_AMPERSAND")
                    || o.ends_with("_CAST")
                    || o.ends_with("_SET")
                    || o == "T_YIELD_FROM"
                    || (o == "T_STRING" && u == "T_ENUM");
                if !deferred && examples.len() < 20 {
                    examples.push(format!("  {}: oracle={o} ours={u}", path.file_name().unwrap().to_string_lossy()));
                }
            }
        }
    }

    println!("\ndifftokens: {matched}/{checked} files match exactly");
    if matched != checked {
        println!("\nmismatches by oracle token (first divergence per file):");
        let mut rows: Vec<_> = by_oracle.into_iter().collect();
        rows.sort_by_key(|r| std::cmp::Reverse(r.1));
        for (name, count) in rows.iter().take(25) {
            println!("  {count:>5}  {name}");
        }
        println!("\nexamples:");
        for e in &examples {
            println!("{e}");
        }
    }
    ExitCode::SUCCESS
}

/// Return (oracle_name, our_name) at the first differing token, or `None` if the
/// streams are identical.
fn first_divergence(
    ours: &[golden::GoldenToken],
    oracle: &[golden::GoldenToken],
) -> Option<(String, String)> {
    let n = ours.len().min(oracle.len());
    for i in 0..n {
        if ours[i] != oracle[i] {
            return Some((oracle[i].name.clone(), ours[i].name.clone()));
        }
    }
    if ours.len() != oracle.len() {
        let o = oracle.get(n).map(|t| t.name.clone()).unwrap_or_else(|| "<eof>".into());
        let u = ours.get(n).map(|t| t.name.clone()).unwrap_or_else(|| "<eof>".into());
        return Some((o, u));
    }
    None
}

/// Structural AST differential: compare our AST against PHP's Zend AST
/// (`php-ast`) over the corpus, in canonical s-expression form. The measured
/// path to 100% parser correctness.
fn cmd_astdiff(args: &[String]) -> ExitCode {
    // Run on a large stack: left-associative operator chains (`1+1+…+1`) build
    // very deep ASTs that the recursive dumper would otherwise overflow on.
    let args: Vec<String> = args.to_vec();
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || astdiff_run(&args))
        .unwrap()
        .join()
        .unwrap()
}

fn astdiff_run(args: &[String]) -> ExitCode {
    let mut dir: Option<PathBuf> = None;
    let mut limit = usize::MAX;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--limit" => limit = it.next().and_then(|s| s.parse().ok()).unwrap_or(usize::MAX),
            _ => dir = Some(PathBuf::from(a)),
        }
    }
    let root = workspace_root();
    let dir = dir.unwrap_or_else(|| root.join("php-src/Zend/tests"));
    let helper = root.join("crates/xtask/php/dump_ast.php");
    if Command::new("php").arg("--version").output().is_err() {
        eprintln!("`php` not found on PATH");
        return ExitCode::FAILURE;
    }

    let mut files: Vec<PathBuf> = WalkDir::new(&dir)
        .into_iter()
        .filter_map(Result::ok)
        .map(|e| e.into_path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("phpt"))
        .collect();
    files.sort();

    let (mut checked, mut matched, mut we_errored) = (0usize, 0usize, 0usize);
    let mut buckets: BTreeMap<String, (usize, String)> = BTreeMap::new();

    for path in files.into_iter().take(limit) {
        let Ok(text) = std::fs::read_to_string(&path) else { continue };
        let Some(source) = phpt::extract_file_section(&text) else { continue };
        let Some(oracle) = run_php(&helper, &source) else { continue };
        let oracle = oracle.trim_ascii_end();
        if oracle == b"<<PARSE_ERROR>>" {
            continue; // PHP rejects this source; not an AST-match candidate.
        }
        let parsed = match catch_unwind(AssertUnwindSafe(|| php_parser::parse(&source))) {
            Ok(p) => p,
            Err(_) => continue,
        };
        checked += 1;
        if parsed.has_errors() {
            we_errored += 1;
            continue;
        }
        let ours = astdump::dump(&parsed.program, &source, &parsed.interner);
        let ours = ours.trim_ascii_end();
        if ours == oracle {
            matched += 1;
            continue;
        }
        // First differing line → bucket (lossy text view; values may be binary).
        let oracle = String::from_utf8_lossy(oracle);
        let ours = String::from_utf8_lossy(ours);
        let (o, u) = first_diff_line(&oracle, &ours);
        let key = o.trim().to_string();
        let entry = buckets.entry(key).or_insert((0, String::new()));
        entry.0 += 1;
        if entry.1.is_empty() {
            entry.1 = format!(
                "{}  [oracle: {} | ours: {}]",
                path.strip_prefix(&root).unwrap_or(&path).display(),
                o.trim(),
                u.trim()
            );
        }
    }

    let denom = checked.max(1);
    println!(
        "\nAST differential: {matched}/{checked} match ({:.2}%); {we_errored} we-error-but-PHP-ok",
        100.0 * matched as f64 / denom as f64
    );
    let mut rows: Vec<_> = buckets.into_iter().collect();
    rows.sort_by_key(|(_, (n, _))| std::cmp::Reverse(*n));
    println!("\ntop divergences (by first differing oracle line):");
    for (key, (n, ex)) in rows.into_iter().take(25) {
        println!("  {n:>5}  {key}");
        println!("         {ex}");
    }
    ExitCode::SUCCESS
}

fn first_diff_line<'a>(oracle: &'a str, ours: &'a str) -> (&'a str, &'a str) {
    let mut o = oracle.lines();
    let mut u = ours.lines();
    loop {
        match (o.next(), u.next()) {
            (Some(a), Some(b)) if a == b => continue,
            (a, b) => return (a.unwrap_or("<eof>"), b.unwrap_or("<eof>")),
        }
    }
}

fn run_php(helper: &Path, source: &str) -> Option<Vec<u8>> {
    let mut child = Command::new("php")
        .arg(helper)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    child.stdin.take()?.write_all(source.as_bytes()).ok()?;
    let out = child.wait_with_output().ok()?;
    // Raw bytes: PHP string literals can contain non-UTF-8 bytes that must
    // compare exactly against our dump.
    out.status.success().then_some(out.stdout)
}

fn run_php_tokens(helper: &Path, source: &str) -> Option<String> {
    let mut child = Command::new("php")
        .arg(helper)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    child.stdin.take()?.write_all(source.as_bytes()).ok()?;
    let out = child.wait_with_output().ok()?;
    out.status.success().then(|| String::from_utf8_lossy(&out.stdout).into_owned())
}

#[derive(Default)]
struct CorpusStats {
    total: usize,
    no_file: usize,
    parsed_clean: usize,
    parsed_with_errors: usize,
    panicked: usize,
    lex_panicked: usize,
    expects_error: usize,
}

/// Robustness check for the resolution layer: run index_file + resolve_references
/// + diagnostics over every corpus file under `catch_unwind`. Invariant: 0 panics.
fn cmd_resolve(dir: Option<PathBuf>) -> ExitCode {
    let dir = dir.unwrap_or_else(|| workspace_root().join("php-src/Zend/tests"));
    if !dir.is_dir() {
        eprintln!("corpus dir not found: {}", dir.display());
        return ExitCode::FAILURE;
    }
    let (mut files, mut panics, mut classes, mut refs, mut diags) = (0u64, 0u64, 0u64, 0u64, 0u64);
    for entry in WalkDir::new(&dir).into_iter().filter_map(Result::ok) {
        if entry.path().extension().and_then(|e| e.to_str()) != Some("phpt") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(entry.path()) else { continue };
        let Some(source) = phpt::extract_file_section(&text) else { continue };
        files += 1;
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            let r = php_parser::parse(&source);
            let idx = php_resolve::index_file(&r.program, &r.interner);
            let refs = php_resolve::resolve_references(&r.program, &r.interner);
            let diags = php_resolve::diagnostics(&r.program, &r.interner);
            (idx.classes.len(), refs.len(), diags.len())
        }));
        match outcome {
            Ok((c, r, d)) => {
                classes += c as u64;
                refs += r as u64;
                diags += d as u64;
            }
            Err(_) => {
                panics += 1;
                eprintln!("RESOLVE PANIC on {}", entry.path().display());
            }
        }
    }
    println!(
        "resolve over {files} files: {panics} panics; {classes} classes, {refs} references, {diags} diagnostics"
    );
    if panics == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// Build one project-wide symbol index over the whole corpus and report scale
/// stats. (The corpus is many independent tests, so duplicate class names are
/// expected — this exercises aggregation + the index at scale, 0 panics.)
fn cmd_index(dir: Option<PathBuf>) -> ExitCode {
    let dir = dir.unwrap_or_else(|| workspace_root().join("php-src/Zend/tests"));
    if !dir.is_dir() {
        eprintln!("corpus dir not found: {}", dir.display());
        return ExitCode::FAILURE;
    }
    let mut index = php_index::ProjectIndex::new();
    let mut files = 0u64;
    for entry in WalkDir::new(&dir).into_iter().filter_map(Result::ok) {
        if entry.path().extension().and_then(|e| e.to_str()) != Some("phpt") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(entry.path()) else { continue };
        let Some(source) = phpt::extract_file_section(&text) else { continue };
        files += 1;
        let label = entry.path().strip_prefix(&dir).unwrap_or(entry.path()).display().to_string();
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            let r = php_parser::parse(&source);
            php_resolve::index_file(&r.program, &r.interner)
        }));
        match outcome {
            Ok(file_index) => index.add_file(&label, &file_index),
            Err(_) => eprintln!("INDEX PANIC on {}", entry.path().display()),
        }
    }
    let dup = index.duplicate_classes().count();
    println!(
        "indexed {files} files: {} unique classes ({dup} redeclared across files), {} functions, {} constants",
        index.class_count(),
        index.function_count(),
        index.constant_count(),
    );
    ExitCode::SUCCESS
}

fn cmd_corpus(dir: Option<PathBuf>) -> ExitCode {
    let dir = dir.unwrap_or_else(|| workspace_root().join("php-src/Zend/tests"));
    if !dir.is_dir() {
        eprintln!("corpus dir not found: {}", dir.display());
        return ExitCode::FAILURE;
    }
    println!("scanning {}", dir.display());

    let mut s = CorpusStats::default();
    for entry in WalkDir::new(&dir).into_iter().filter_map(Result::ok) {
        if entry.file_type().is_dir() {
            continue;
        }
        if entry.path().extension().and_then(|e| e.to_str()) != Some("phpt") {
            continue;
        }
        s.total += 1;
        let Ok(text) = std::fs::read_to_string(entry.path()) else {
            continue;
        };
        let Some(source) = phpt::extract_file_section(&text) else {
            s.no_file += 1;
            continue;
        };
        if phpt::expects_parse_error(&text) {
            s.expects_error += 1;
        }
        // Lexer stress: M1 lexing may produce wrong tokens for not-yet-supported
        // constructs (heredoc, interpolation), but it must never panic.
        match catch_unwind(AssertUnwindSafe(|| php_lexer::tokenize(&source))) {
            Ok(_) => {}
            Err(_) => {
                s.lex_panicked += 1;
                eprintln!("LEX PANIC on {}", entry.path().display());
            }
        }
        match catch_unwind(AssertUnwindSafe(|| php_parser::parse(&source))) {
            Ok(result) => {
                if result.has_errors() {
                    s.parsed_with_errors += 1;
                } else {
                    s.parsed_clean += 1;
                }
            }
            Err(_) => {
                s.panicked += 1;
                eprintln!("PANIC parsing {}", entry.path().display());
            }
        }
    }

    println!("\ncorpus results:");
    println!("  .phpt files scanned : {}", s.total);
    println!("  with --FILE--       : {}", s.total - s.no_file);
    println!("  lexed ok            : {}", (s.total - s.no_file) - s.lex_panicked);
    println!("  LEX PANICKED        : {}", s.lex_panicked);
    println!("  parsed (no errors)  : {}", s.parsed_clean);
    println!("  parsed (w/ errors)  : {}", s.parsed_with_errors);
    println!("  PARSE PANICKED      : {}", s.panicked);
    println!("  assert parse error  : {} (error-recovery subset)", s.expects_error);

    // The hard invariant: neither lexer nor parser may ever panic.
    if s.panicked == 0 && s.lex_panicked == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// Triage: list corpus files that parse *with errors* but are NOT intentional
/// parse-error tests — the M8 worklist. Tally by first diagnostic message.
fn cmd_triage(dir: Option<PathBuf>) -> ExitCode {
    let dir = dir.unwrap_or_else(|| workspace_root().join("php-src/Zend/tests"));
    let mut by_msg: BTreeMap<String, (usize, Vec<String>)> = BTreeMap::new();
    let mut total = 0usize;

    for entry in WalkDir::new(&dir).into_iter().filter_map(Result::ok) {
        if entry.path().extension().and_then(|e| e.to_str()) != Some("phpt") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(entry.path()) else { continue };
        if phpt::expects_parse_error(&text) {
            continue; // intentional error — not our worklist
        }
        let Some(source) = phpt::extract_file_section(&text) else { continue };
        let Ok(result) = catch_unwind(AssertUnwindSafe(|| php_parser::parse(&source))) else {
            continue;
        };
        let Some(first) = result.diagnostics.iter().find(|d| d.is_error()) else {
            continue;
        };
        total += 1;
        let name = entry.path().file_name().unwrap().to_string_lossy().into_owned();
        let bucket = by_msg.entry(first.message.clone()).or_default();
        bucket.0 += 1;
        if bucket.1.len() < 3 {
            bucket.1.push(name);
        }
    }

    println!("{total} non-intentional files parse with errors. By first diagnostic:\n");
    let mut rows: Vec<_> = by_msg.into_iter().collect();
    rows.sort_by_key(|(_, (n, _))| std::cmp::Reverse(*n));
    for (msg, (n, examples)) in rows {
        println!("{n:>5}  {msg}");
        println!("       e.g. {}", examples.join(", "));
    }
    ExitCode::SUCCESS
}

/// Parse one `.phpt`'s `--FILE--` and print each diagnostic with its source
/// slice and 1-based line — pinpoints where the parser trips.
fn cmd_diag(path: Option<PathBuf>) -> ExitCode {
    let Some(path) = path else {
        eprintln!("usage: xtask diag FILE.phpt");
        return ExitCode::FAILURE;
    };
    let Ok(text) = std::fs::read_to_string(&path) else {
        eprintln!("cannot read {}", path.display());
        return ExitCode::FAILURE;
    };
    let Some(source) = phpt::extract_file_section(&text) else {
        eprintln!("no --FILE-- section");
        return ExitCode::FAILURE;
    };
    let r = php_parser::parse(&source);
    println!("{} diagnostic(s):", r.diagnostics.len());
    for d in &r.diagnostics {
        let s = d.primary.start as usize;
        let e = (d.primary.end as usize).min(source.len());
        let line = source[..s.min(source.len())].bytes().filter(|&b| b == b'\n').count() + 1;
        let slice = source.get(s..e).unwrap_or("");
        println!("  line {line}: {} — {:?}", d.message, slice);
    }
    ExitCode::SUCCESS
}

fn cmd_phpt_extract(path: Option<PathBuf>) -> ExitCode {
    let Some(path) = path else {
        eprintln!("usage: xtask phpt-extract FILE");
        return ExitCode::FAILURE;
    };
    let Ok(text) = std::fs::read_to_string(&path) else {
        eprintln!("cannot read {}", path.display());
        return ExitCode::FAILURE;
    };
    match phpt::extract_file_section(&text) {
        Some(body) => {
            print!("{body}");
            ExitCode::SUCCESS
        }
        None => {
            eprintln!("no --FILE-- section in {}", path.display());
            ExitCode::FAILURE
        }
    }
}

/// Generate golden token fixtures: for every `test-fixtures/tokens/*.php`, run
/// the PHP oracle and (over)write the paired `*.tokens`. Requires `php` on PATH.
/// Regenerate the committed built-in-names manifest (`crates/php-index/stubs/
/// builtins.txt`) by parsing the **phpstorm-stubs** submodule with our own
/// parser + resolver and collecting declared FQNs. No PHP needed; the manifest
/// is committed and CI never runs this. Names only — version-aware *types* come
/// from the same stubs at the type-system stage. Covers all bundled + PECL
/// extensions (sqlsrv, oci8, redis, …), not just what a local PHP build loads.
fn cmd_gen_stubs() -> ExitCode {
    use std::collections::BTreeSet;
    let root = workspace_root();
    let stubs = root.join("vendor/phpstorm-stubs");
    let dest = root.join("crates/php-index/stubs/builtins.txt");
    if !stubs.is_dir() {
        eprintln!("phpstorm-stubs not present: {} (run `git submodule update --init`)", stubs.display());
        return ExitCode::FAILURE;
    }
    let (mut functions, mut classes, mut interfaces, mut traits, mut enums, mut constants) = (
        BTreeSet::new(),
        BTreeSet::new(),
        BTreeSet::new(),
        BTreeSet::new(),
        BTreeSet::new(),
        BTreeSet::new(),
    );
    let (mut files, mut parse_errors) = (0u64, 0u64);
    for entry in WalkDir::new(&stubs).into_iter().filter_map(Result::ok) {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("php") {
            continue;
        }
        // Skip the test suite and the generated stubs-map meta file.
        let s = path.to_string_lossy();
        if s.contains("/tests/") || path.file_name().and_then(|f| f.to_str()) == Some("PhpStormStubsMap.php") {
            continue;
        }
        let Ok(source) = std::fs::read_to_string(path) else { continue };
        files += 1;
        let parsed = match catch_unwind(AssertUnwindSafe(|| php_parser::parse(&source))) {
            Ok(p) => p,
            Err(_) => {
                eprintln!("PARSE PANIC on {}", path.display());
                continue;
            }
        };
        if parsed.has_errors() {
            parse_errors += 1;
        }
        let idx = php_resolve::index_file(&parsed.program, &parsed.interner);
        for c in idx.classes {
            let set = match c.kind {
                php_ast::ClassKind::Class => &mut classes,
                php_ast::ClassKind::Interface => &mut interfaces,
                php_ast::ClassKind::Trait => &mut traits,
                php_ast::ClassKind::Enum => &mut enums,
            };
            set.insert(c.fqn);
        }
        functions.extend(idx.functions.into_iter().map(|f| f.fqn));
        constants.extend(idx.constants.into_iter().map(|k| k.fqn));
    }

    let mut out = String::new();
    out.push_str("# Built-in symbol names from JetBrains/phpstorm-stubs (submodule) — existence only.\n");
    out.push_str("# Generated by `xtask gen-stubs`; do not edit. Names are version-stable;\n");
    out.push_str("# signatures/types are version-dependent and come from the stubs later.\n");
    let section = |out: &mut String, name: &str, items: &BTreeSet<String>| {
        out.push_str(&format!("[{name}]\n"));
        for i in items {
            out.push_str(i);
            out.push('\n');
        }
    };
    section(&mut out, "functions", &functions);
    section(&mut out, "classes", &classes);
    section(&mut out, "interfaces", &interfaces);
    section(&mut out, "traits", &traits);
    section(&mut out, "enums", &enums);
    section(&mut out, "constants", &constants);

    if let Some(parent) = dest.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    if let Err(e) = std::fs::write(&dest, &out) {
        eprintln!("write failed {}: {e}", dest.display());
        return ExitCode::FAILURE;
    }
    println!(
        "parsed {files} stub files ({parse_errors} with parse errors) -> {}: {} functions, {} classes, {} interfaces, {} traits, {} enums, {} constants",
        dest.strip_prefix(&root).unwrap_or(&dest).display(),
        functions.len(),
        classes.len(),
        interfaces.len(),
        traits.len(),
        enums.len(),
        constants.len(),
    );
    ExitCode::SUCCESS
}

fn cmd_gen_tokens() -> ExitCode {
    let root = workspace_root();
    let tokens_dir = root.join("test-fixtures/tokens");
    let helper = root.join("crates/xtask/php/gen_golden.php");
    if !helper.is_file() {
        eprintln!("missing PHP helper: {}", helper.display());
        return ExitCode::FAILURE;
    }
    match Command::new("php").arg("--version").output() {
        Ok(out) if out.status.success() => {
            let v = String::from_utf8_lossy(&out.stdout);
            println!("oracle: {}", v.lines().next().unwrap_or("php"));
        }
        _ => {
            eprintln!("`php` not found on PATH (brew install php)");
            return ExitCode::FAILURE;
        }
    }

    let mut sources: Vec<PathBuf> = WalkDir::new(&tokens_dir)
        .into_iter()
        .filter_map(Result::ok)
        .map(|e| e.into_path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("php"))
        .collect();
    sources.sort();

    if sources.is_empty() {
        eprintln!("no *.php fixtures under {}", tokens_dir.display());
        return ExitCode::FAILURE;
    }

    let mut failures = 0;
    for php in &sources {
        let out = match Command::new("php").arg(&helper).arg(php).output() {
            Ok(o) => o,
            Err(e) => {
                eprintln!("php invocation failed for {}: {e}", php.display());
                failures += 1;
                continue;
            }
        };
        if !out.status.success() {
            eprintln!(
                "php errored on {}:\n{}",
                php.display(),
                String::from_utf8_lossy(&out.stderr)
            );
            failures += 1;
            continue;
        }
        let dest = php.with_extension("tokens");
        if let Err(e) = std::fs::write(&dest, &out.stdout) {
            eprintln!("write failed {}: {e}", dest.display());
            failures += 1;
            continue;
        }
        println!("  {}", dest.strip_prefix(&root).unwrap_or(&dest).display());
    }

    println!("generated {} fixture(s), {failures} failure(s)", sources.len() - failures);
    if failures == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
