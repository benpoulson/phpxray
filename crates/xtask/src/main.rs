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
        Some("reflect") => cmd_reflect(args.get(1).map(PathBuf::from)),
        Some("infer") => cmd_infer(args.get(1).map(PathBuf::from)),
        Some("check") => cmd_check(args.get(1).map(PathBuf::from)),
        Some("phpdoc") => cmd_phpdoc(args.get(1).map(PathBuf::from)),
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

/// M-T3: build the project **reflection index** over a corpus — reflect every
/// class/function (native + PHPDoc types resolved & merged) into one queryable
/// map. Asserts 0 panics and reports counts plus a sanity sweep of inherited-
/// member lookup (every class resolves its own first declared method).
fn cmd_reflect(dir: Option<PathBuf>) -> ExitCode {
    let dir = dir.unwrap_or_else(|| workspace_root().join("php-src/Zend/tests"));
    if !dir.is_dir() {
        eprintln!("corpus dir not found: {}", dir.display());
        return ExitCode::FAILURE;
    }
    let mut index = php_reflect::ReflectionIndex::new();
    let (mut files, mut panics) = (0u64, 0u64);
    for entry in WalkDir::new(&dir).into_iter().filter_map(Result::ok) {
        if entry.path().extension().and_then(|e| e.to_str()) != Some("phpt") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(entry.path()) else { continue };
        let Some(source) = phpt::extract_file_section(&text) else { continue };
        files += 1;
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            let r = php_parser::parse(&source);
            index.add_file(&r.program, &r.interner);
        }));
        if outcome.is_err() {
            panics += 1;
            eprintln!("REFLECT PANIC on {}", entry.path().display());
        }
    }
    println!("reflected {files} files: {} classes, {panics} panics", index.class_count());
    if panics == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// M-T4/M-T5: run **type inference** over a corpus. Pass 1 builds the project
/// reflection index; pass 2 runs flow analysis over every function and method
/// body (which infers every contained expression). Asserts 0 panics — the
/// inference layer must be total, like the parser.
fn cmd_infer(dir: Option<PathBuf>) -> ExitCode {
    use php_ast::{Member, Stmt, StmtKind};
    use php_infer::TypeCtx;
    use php_reflect::{resolve_ast_type, ReflectionIndex};
    use php_resolve::{for_each_region, Scope};
    use php_types::Type;

    let dir = dir.unwrap_or_else(|| workspace_root().join("php-src/Zend/tests"));
    if !dir.is_dir() {
        eprintln!("corpus dir not found: {}", dir.display());
        return ExitCode::FAILURE;
    }

    // Pass 1: build the project-wide reflection index (and keep the sources to
    // re-parse in pass 2).
    let mut index = ReflectionIndex::new();
    let mut sources: Vec<(String, String)> = Vec::new();
    for entry in WalkDir::new(&dir).into_iter().filter_map(Result::ok) {
        if entry.path().extension().and_then(|e| e.to_str()) != Some("phpt") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(entry.path()) else { continue };
        let Some(source) = phpt::extract_file_section(&text) else { continue };
        let label = entry.path().display().to_string();
        let r = php_parser::parse(&source);
        index.add_file(&r.program, &r.interner);
        sources.push((label, source));
    }

    // Recursive descent: analyse each function/method body, descending into
    // nested/conditional declarations.
    fn infer_stmt(idx: &ReflectionIndex, scope: &Scope, i: &php_intern::Interner, st: &Stmt, bodies: &mut u64) {
        match &st.kind {
            StmtKind::Function(f) => {
                let mut ctx = TypeCtx::new(idx, scope, i);
                ctx.analyze_function_body(f);
                *bodies += 1;
                infer_all(idx, scope, i, &f.body, bodies);
            }
            StmtKind::Class(c) => {
                let fqn = c.name.map(|n| scope.qualify(i.resolve(n)));
                for m in &c.members {
                    let Member::Method(md) = m else { continue };
                    let Some(body) = &md.body else { continue };
                    let mut ctx = TypeCtx::new(idx, scope, i);
                    ctx.class = fqn.clone();
                    for p in &md.params {
                        let ty = p.ty.as_ref().map(|t| resolve_ast_type(scope, t)).unwrap_or(Type::Mixed);
                        ctx.vars.insert(i.resolve(p.name).to_string(), ty);
                    }
                    ctx.exec_block(body);
                    *bodies += 1;
                    infer_all(idx, scope, i, body, bodies);
                }
            }
            StmtKind::Block(b) => infer_all(idx, scope, i, b, bodies),
            StmtKind::If { then, elseifs, els, .. } => {
                infer_stmt(idx, scope, i, then, bodies);
                for e in elseifs {
                    infer_stmt(idx, scope, i, &e.body, bodies);
                }
                if let Some(e) = els {
                    infer_stmt(idx, scope, i, e, bodies);
                }
            }
            StmtKind::While { body, .. }
            | StmtKind::DoWhile { body, .. }
            | StmtKind::For { body, .. }
            | StmtKind::Foreach { body, .. } => infer_stmt(idx, scope, i, body, bodies),
            StmtKind::Try { body, catches, finally } => {
                infer_all(idx, scope, i, body, bodies);
                for c in catches {
                    infer_all(idx, scope, i, &c.body, bodies);
                }
                if let Some(f) = finally {
                    infer_all(idx, scope, i, f, bodies);
                }
            }
            StmtKind::Switch { cases, .. } => {
                for case in cases {
                    infer_all(idx, scope, i, &case.body, bodies);
                }
            }
            StmtKind::Declare { body: Some(b), .. } => infer_stmt(idx, scope, i, b, bodies),
            _ => {}
        }
    }
    fn infer_all(idx: &ReflectionIndex, scope: &Scope, i: &php_intern::Interner, stmts: &[Stmt], bodies: &mut u64) {
        for st in stmts {
            infer_stmt(idx, scope, i, st, bodies);
        }
    }

    // Pass 2: run inference, isolating panics per file.
    let (mut files, mut bodies, mut panics) = (0u64, 0u64, 0u64);
    for (label, source) in &sources {
        files += 1;
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            let r = php_parser::parse(source);
            let mut count = 0u64;
            for_each_region(&r.program.stmts, &r.interner, |scope, region| {
                infer_all(&index, scope, &r.interner, region, &mut count);
            });
            count
        }));
        match outcome {
            Ok(n) => bodies += n,
            Err(_) => {
                panics += 1;
                eprintln!("INFER PANIC on {label}");
            }
        }
    }
    println!("inferred over {files} files: {bodies} function/method bodies analysed, {panics} panics");
    if panics == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// M-T7: the **multi-file driver** — index a whole project (reflection), then
/// run the type rules (currently the return-type rule) over each file. Reports
/// the total diagnostics and a sample, and asserts 0 panics. Over the Zend
/// corpus (intentionally weird code) this is mostly a false-positive gauge.
fn cmd_check(dir: Option<PathBuf>) -> ExitCode {
    // Left-associative chains in the corpus produce very deep ASTs; the recursive
    // visitors (infer/flow/walk) need a large stack (same as `astdiff`).
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || cmd_check_run(dir))
        .expect("spawn check thread")
        .join()
        .expect("check thread panicked")
}

fn cmd_check_run(dir: Option<PathBuf>) -> ExitCode {
    use php_index::ProjectIndex;
    use php_reflect::ReflectionIndex;
    use php_resolve::{index_file, resolve_references};
    use php_rules::{analyze_file, FileAnalysis};
    use std::collections::BTreeMap;

    let dir = dir.unwrap_or_else(|| workspace_root().join("php-src/Zend/tests"));
    if !dir.is_dir() {
        eprintln!("corpus dir not found: {}", dir.display());
        return ExitCode::FAILURE;
    }

    // Pass 1: parse every file into ONE shared interner (so cross-file symbols
    // resolve) and build the project symbol + reflection indexes over it.
    let mut interner = php_intern::Interner::new();
    let mut project = ProjectIndex::with_builtins();
    let mut reflection = ReflectionIndex::with_builtins();
    let mut files_data: Vec<(String, String, php_ast::Program)> = Vec::new();
    for entry in WalkDir::new(&dir).into_iter().filter_map(Result::ok) {
        if entry.path().extension().and_then(|e| e.to_str()) != Some("phpt") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(entry.path()) else { continue };
        let Some(source) = phpt::extract_file_section(&text) else { continue };
        let label = entry.path().display().to_string();
        let (program, _diags) = php_parser::parse_into(&source, &mut interner);
        project.add_file(&label, &index_file(&program, &interner));
        reflection.add_file(&program, &interner);
        files_data.push((label, source, program));
    }

    // Pass 2: run ALL rules at level max, isolating panics per file.
    let (mut files, mut diags, mut panics) = (0u64, 0u64, 0u64);
    let mut by_code: BTreeMap<String, u64> = BTreeMap::new();
    for (label, source, program) in &files_data {
        files += 1;
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            let refs = resolve_references(program, &interner);
            let types = php_rules::type_map(&reflection, program, &interner);
            let native_types = php_rules::native_type_map(&reflection, program, &interner);
            let fa = FileAnalysis {
                path: label,
                source,
                program,
                interner: &interner,
                project: &project,
                reflection: &reflection,
                resolved_refs: &refs,
                types: &types,
                native_types: &native_types,
                php_version: php_rules::PhpVersion::default(),
                treat_phpdoc_types_as_certain: true,
                check_nullables: true, // xtask check runs at level 10
            };
            analyze_file(&fa, 10)
                .into_iter()
                .map(|d| d.code.unwrap_or("?").to_string())
                .collect::<Vec<_>>()
        }));
        match outcome {
            Ok(codes) => {
                diags += codes.len() as u64;
                for c in codes {
                    *by_code.entry(c).or_default() += 1;
                }
            }
            Err(_) => {
                panics += 1;
                eprintln!("CHECK PANIC on {label}");
            }
        }
    }
    println!("checked {files} files at level max: {diags} diagnostics, {panics} panics");
    let mut rows: Vec<(&String, &u64)> = by_code.iter().collect();
    rows.sort_by(|a, b| b.1.cmp(a.1));
    for (code, n) in rows {
        println!("  {n:>7}  {code}");
    }
    if panics == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// M-D3: sweep every docblock in a corpus (default: the phpstorm-stubs
/// submodule) through the PHPDoc parser. Asserts 0 panics and reports type-
/// expression *coverage* — what fraction of `@param`/`@return`/`@var`/`@throws`
/// type operands parse — plus the most common unparsed forms, to drive grammar
/// completeness. No external oracle; our parser vs. real-world docblocks.
fn cmd_phpdoc(dir: Option<PathBuf>) -> ExitCode {
    use std::collections::HashMap;
    let dir = dir.unwrap_or_else(|| workspace_root().join("vendor/phpstorm-stubs"));
    if !dir.is_dir() {
        eprintln!("corpus dir not found: {} (try `git submodule update --init`)", dir.display());
        return ExitCode::FAILURE;
    }
    let type_tags = ["param", "return", "var", "throws"];
    let (mut blocks, mut total, mut parsed, mut panics) = (0u64, 0u64, 0u64, 0u64);
    let (mut methods, mut properties) = (0u64, 0u64);
    let mut fails: HashMap<String, u32> = HashMap::new();

    for entry in WalkDir::new(&dir).into_iter().filter_map(Result::ok) {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("php") {
            continue;
        }
        if path.to_string_lossy().contains("/tests/") {
            continue;
        }
        let Ok(source) = std::fs::read_to_string(path) else { continue };
        let (tokens, _) = php_lexer::tokenize(&source);
        for t in tokens.iter().filter(|t| t.kind == php_lexer::TokenKind::DocComment) {
            let raw = t.span.text(&source);
            let outcome = catch_unwind(AssertUnwindSafe(|| {
                // Exercise the full typed parse (incl. @method/@property/@mixin/
                // generic-extends) for no-panics across the corpus.
                let doc = php_phpdoc::parse(raw);
                let mut local = Vec::new();
                for tag in php_phpdoc::parse_block(raw).tags {
                    let base = tag
                        .name
                        .strip_prefix("phpstan-")
                        .or_else(|| tag.name.strip_prefix("psalm-"))
                        .unwrap_or(&tag.name);
                    if !type_tags.contains(&base) {
                        continue;
                    }
                    let v = tag.value.trim_start();
                    // No type operand (just `$var`/`&$var`/`...$var`/description).
                    if v.is_empty() || v.starts_with(['$', '&']) || v.starts_with("...") {
                        continue;
                    }
                    local.push((php_phpdoc::parse_type_prefix(v).is_some(), v.to_string()));
                }
                (local, doc.methods.len(), doc.properties.len())
            }));
            match outcome {
                Ok((results, m, p)) => {
                    blocks += 1;
                    methods += m as u64;
                    properties += p as u64;
                    for (ok, v) in results {
                        total += 1;
                        if ok {
                            parsed += 1;
                        } else {
                            let key: String = v.chars().take(50).collect();
                            *fails.entry(key).or_insert(0) += 1;
                        }
                    }
                }
                Err(_) => {
                    panics += 1;
                    eprintln!("PHPDOC PANIC on {}", path.display());
                }
            }
        }
    }

    let pct = if total == 0 { 100.0 } else { 100.0 * parsed as f64 / total as f64 };
    println!(
        "\nPHPDoc sweep: {blocks} docblocks, {total} type operands, {parsed} parsed ({pct:.2}%); {panics} panics"
    );
    println!("  also parsed: {methods} @method, {properties} @property declarations");
    if !fails.is_empty() {
        let mut rows: Vec<_> = fails.into_iter().collect();
        rows.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
        println!("\ntop unparsed type forms (by leading token):");
        for (key, n) in rows.into_iter().take(25) {
            println!("  {n:>5}  {key}");
        }
    }
    if panics == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
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
    // Cap #4: typed function signatures, fqn (lowercased key) -> serialized line.
    let mut typed_fns: BTreeMap<String, String> = BTreeMap::new();
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

        // Cap #4: reflect each function to capture its (native + PHPDoc) signature.
        php_resolve::for_each_region(&parsed.program.stmts, &parsed.interner, |scope, region| {
            for st in region {
                if let php_ast::StmtKind::Function(f) = &st.kind {
                    let fr = php_reflect::reflect_function(scope, &parsed.interner, f);
                    typed_fns.insert(fr.fqn.to_ascii_lowercase(), serialize_fn(f, &fr, &parsed.interner));
                }
            }
        });
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

    // Cap #4: write the typed-function manifest consumed by `ReflectionIndex::with_builtins`.
    let fn_dest = root.join("crates/php-reflect/stubs/builtin-functions.txt");
    let mut fn_out = String::new();
    fn_out.push_str("# Typed built-in function signatures from JetBrains/phpstorm-stubs.\n");
    fn_out.push_str("# Generated by `xtask gen-stubs`; do not edit. Keyed to our target PHP\n");
    fn_out.push_str("# version (8.x). Format: fqn<TAB>return<TAB>p1;p2;...  where each param is\n");
    fn_out.push_str("# name|type|flags (flags subset of r=by-ref v=variadic o=optional; empty\n");
    fn_out.push_str("# type = mixed). Types are php_types::Type Display, re-parsed on load.\n");
    for line in typed_fns.values() {
        fn_out.push_str(line);
        fn_out.push('\n');
    }
    if let Some(parent) = fn_dest.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    if let Err(e) = std::fs::write(&fn_dest, &fn_out) {
        eprintln!("write failed {}: {e}", fn_dest.display());
        return ExitCode::FAILURE;
    }

    println!(
        "parsed {files} stub files ({parse_errors} with parse errors) -> {}: {} functions, {} classes, {} interfaces, {} traits, {} enums, {} constants; {} typed fn signatures -> {}",
        dest.strip_prefix(&root).unwrap_or(&dest).display(),
        functions.len(),
        classes.len(),
        interfaces.len(),
        traits.len(),
        enums.len(),
        constants.len(),
        typed_fns.len(),
        fn_dest.strip_prefix(&root).unwrap_or(&fn_dest).display(),
    );
    ExitCode::SUCCESS
}

/// Serialize a reflected function to one manifest line (see the file header).
/// phpstorm-stubs encodes per-version types with
/// `#[LanguageLevelTypeAware(["8.0" => "T"], default: "U")]`; we honour it for
/// our target PHP version so e.g. PHP-8 `substr` is `string`, not `string|false`.
fn serialize_fn(
    f: &php_ast::FunctionDecl,
    fr: &php_reflect::FunctionReflection,
    interner: &php_intern::Interner,
) -> String {
    let ret = level_aware_type(&f.attrs, interner)
        .unwrap_or_else(|| ty_str(&fr.return_type));

    let params: Vec<String> = fr
        .params
        .iter()
        .enumerate()
        .map(|(i, p)| {
            let mut flags = String::new();
            if p.by_ref {
                flags.push('r');
            }
            if p.variadic {
                flags.push('v');
            }
            if p.optional {
                flags.push('o');
            }
            let ty = f
                .params
                .get(i)
                .and_then(|ap| level_aware_type(&ap.attrs, interner))
                .unwrap_or_else(|| ty_str(&p.ty));
            // Field sep `#` and param sep `;` never appear in a Type Display
            // (unions use `|`, generics `<,>`), so types are written verbatim.
            format!("{}#{}#{}", p.name, ty, flags)
        })
        .collect();
    format!("{}\t{}\t{}", fr.fqn, ret, params.join(";"))
}

fn ty_str(t: &php_types::Type) -> String {
    if *t == php_types::Type::Mixed { String::new() } else { t.to_string() }
}

/// Our target PHP version for resolving `#[LanguageLevelTypeAware]` entries.
const TARGET_PHP: (u32, u32) = (8, 6);

/// If `attrs` contains a `#[LanguageLevelTypeAware(["V" => "T", …], default: "U")]`,
/// return the type string for [`TARGET_PHP`]: the value of the highest version
/// key `≤ target`, else the `default:`.
fn level_aware_type(attrs: &[php_ast::AttributeGroup], interner: &php_intern::Interner) -> Option<String> {
    use php_ast::ExprKind;
    for g in attrs {
        for a in &g.attrs {
            let last = a.name.text.rsplit('\\').next().unwrap_or(&a.name.text);
            if !last.eq_ignore_ascii_case("LanguageLevelTypeAware") {
                continue;
            }
            let args = a.args.as_ref()?;
            // First positional arg: the `["V" => "T"]` map. `default:` named arg.
            let mut best: Option<((u32, u32), String)> = None;
            let mut default: Option<String> = None;
            for arg in args {
                if arg.name.map(|s| interner.resolve(s)) == Some("default") {
                    if let ExprKind::Str(b) = &arg.value.kind {
                        default = Some(String::from_utf8_lossy(b).into_owned());
                    }
                    continue;
                }
                if let ExprKind::Array { items, .. } = &arg.value.kind {
                    for it in items {
                        let (Some(k), Some(v)) = (&it.key, &it.value) else { continue };
                        let (ExprKind::Str(kb), ExprKind::Str(vb)) = (&k.kind, &v.kind) else { continue };
                        let ver = parse_ver(&String::from_utf8_lossy(kb));
                        let Some(ver) = ver else { continue };
                        if ver <= TARGET_PHP && best.as_ref().is_none_or(|(bv, _)| ver >= *bv) {
                            best = Some((ver, String::from_utf8_lossy(vb).into_owned()));
                        }
                    }
                }
            }
            let chosen = best.map(|(_, t)| t).or(default)?;
            let chosen = chosen.trim();
            return Some(if chosen.eq_ignore_ascii_case("mixed") { String::new() } else { chosen.to_string() });
        }
    }
    None
}

fn parse_ver(s: &str) -> Option<(u32, u32)> {
    let mut it = s.trim().split('.');
    let major = it.next()?.parse().ok()?;
    let minor = it.next().unwrap_or("0").parse().ok()?;
    Some((major, minor))
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
