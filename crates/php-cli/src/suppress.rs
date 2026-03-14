//! M-C4: **suppression** — drop findings the user has chosen to ignore, via
//! config `ignore` entries or inline `@phpstan-ignore` comments.
//!
//! Config entries match on a message regex, an exact identifier, and/or path
//! globs (all present conditions must hold). Inline ignores are found by a
//! line-oriented prescan of the raw source — independent of the lexer (which
//! discards comments), so token parity is untouched. With `reportUnmatched`,
//! config entries that matched nothing are themselves reported (so stale
//! suppressions get cleaned up).

use crate::{Finding, Report};
use php_config::{ExcludeMatcher, IgnoreEntry};
use php_diagnostics::Severity;
use regex::Regex;
use std::collections::HashMap;

/// Apply config + inline suppressions to a report. `sources` maps each file's
/// display path to its source (for inline-ignore scanning).
pub fn apply(
    report: Report,
    ignore: &[IgnoreEntry],
    report_unmatched: bool,
    sources: &HashMap<&str, &str>,
) -> Report {
    let mut matchers: Vec<Matcher> = ignore.iter().filter_map(Matcher::compile).collect();
    // Precompute inline-ignore maps per file (keys borrow `sources`, which
    // outlives this loop — so findings can be moved into `kept`).
    let inline: HashMap<&str, HashMap<u32, Spec>> =
        sources.iter().map(|(path, src)| (*path, inline_ignores(src))).collect();

    let mut kept = Vec::new();
    for f in report.findings {
        // Inline ignore?
        if let Some(map) = inline.get(f.path.as_str()) {
            if suppressed_inline(map, &f) {
                continue;
            }
        }
        // Config ignore?
        if let Some(m) = matchers.iter_mut().find(|m| m.matches(&f)) {
            m.matched += 1;
            continue;
        }
        kept.push(f);
    }

    if report_unmatched {
        for m in &matchers {
            if m.matched == 0 {
                kept.push(Finding {
                    path: "(ignore)".to_string(),
                    line: 0,
                    column: 0,
                    message: format!("Ignored pattern {} was not matched in reported errors", m.describe()),
                    identifier: Some("ignore.unmatched"),
                    severity: Severity::Error,
                });
            }
        }
    }

    Report { findings: kept, files_analyzed: report.files_analyzed }
}

/// A compiled config ignore entry.
struct Matcher {
    message: Option<Regex>,
    identifier: Option<String>,
    /// Path constraint (subtree-aware, like excludes); `None` = any path.
    paths: Option<ExcludeMatcher>,
    matched: usize,
    desc: String,
}

impl Matcher {
    /// Compile an entry; `None` for a degenerate entry (no message and no
    /// identifier — too broad to honor safely).
    fn compile(e: &IgnoreEntry) -> Option<Matcher> {
        if e.message.is_none() && e.identifier.is_none() {
            return None;
        }
        let message = e.message.as_ref().map(|m| {
            let body = strip_delims(m);
            Regex::new(body).unwrap_or_else(|_| Regex::new(&regex::escape(body)).unwrap())
        });
        let path_patterns: Vec<String> = e.path.iter().chain(e.paths.iter()).cloned().collect();
        let paths = (!path_patterns.is_empty()).then(|| ExcludeMatcher::new(&path_patterns));
        let desc = e.message.clone().or_else(|| e.identifier.clone()).unwrap_or_default();
        Some(Matcher { message, identifier: e.identifier.clone(), paths, matched: 0, desc })
    }

    fn matches(&self, f: &Finding) -> bool {
        if let Some(re) = &self.message {
            if !re.is_match(&f.message) {
                return false;
            }
        }
        if let Some(id) = &self.identifier {
            if f.identifier != Some(id.as_str()) {
                return false;
            }
        }
        if let Some(pm) = &self.paths {
            if !pm.is_excluded(&f.path) {
                return false;
            }
        }
        true
    }

    fn describe(&self) -> &str {
        &self.desc
    }
}

/// Strip matched `/.../`, `#...#`, or `~...~` regex delimiters.
fn strip_delims(s: &str) -> &str {
    let b = s.as_bytes();
    if b.len() >= 2 {
        let first = b[0];
        if matches!(first, b'/' | b'#' | b'~') && b[b.len() - 1] == first {
            return &s[1..s.len() - 1];
        }
    }
    s
}

/// What an inline ignore on a line suppresses.
#[derive(Clone)]
enum Spec {
    /// Ignore every finding on the line.
    All,
    /// Ignore only findings with one of these identifiers.
    Ids(Vec<String>),
}

fn suppressed_inline(map: &HashMap<u32, Spec>, f: &Finding) -> bool {
    match map.get(&f.line) {
        Some(Spec::All) => true,
        Some(Spec::Ids(ids)) => f.identifier.map(|id| ids.iter().any(|x| x == id)).unwrap_or(false),
        None => false,
    }
}

/// Scan source for inline ignore comments, mapping target line → what to ignore.
fn inline_ignores(source: &str) -> HashMap<u32, Spec> {
    let mut map: HashMap<u32, Spec> = HashMap::new();
    for (i, line) in source.lines().enumerate() {
        let lineno = (i + 1) as u32;
        if let Some((target, spec)) = marker(line, lineno) {
            merge(&mut map, target, spec);
        }
    }
    map
}

fn merge(map: &mut HashMap<u32, Spec>, line: u32, spec: Spec) {
    match map.get_mut(&line) {
        Some(Spec::All) => {}
        Some(existing @ Spec::Ids(_)) => match spec {
            Spec::All => *existing = Spec::All,
            Spec::Ids(mut more) => {
                if let Spec::Ids(ids) = existing {
                    ids.append(&mut more);
                }
            }
        },
        None => {
            map.insert(line, spec);
        }
    }
}

/// Parse an ignore marker on `line` (at 1-based `lineno`), returning the target
/// line it applies to and what it ignores.
///
/// `-line`/`-next-line` are explicit. A bare `@phpstan-ignore` applies to the
/// **same** line when it's a trailing comment (code precedes it) and the **next**
/// line when it stands alone — matching how people actually annotate.
fn marker(line: &str, lineno: u32) -> Option<(u32, Spec)> {
    for prefix in ["@phpstan-ignore", "@php-analyzer-ignore"] {
        if let Some(pos) = line.find(prefix) {
            let rest = &line[pos + prefix.len()..];
            if rest.starts_with("-next-line") {
                return Some((lineno + 1, Spec::All));
            }
            if rest.starts_with("-line") {
                return Some((lineno, Spec::All));
            }
            let target = if is_trailing_comment(&line[..pos]) { lineno } else { lineno + 1 };
            let ids = parse_ids(rest);
            return Some((target, if ids.is_empty() { Spec::All } else { Spec::Ids(ids) }));
        }
    }
    None
}

/// Whether the text before the marker contains code (a trailing comment) rather
/// than just the comment opener and whitespace (a standalone comment).
fn is_trailing_comment(before: &str) -> bool {
    let trimmed = before.trim_end().trim_end_matches(['/', '*', '#', ' ', '\t']);
    !trimmed.trim().is_empty()
}

/// Identifiers after a bare `@phpstan-ignore` (comma/space separated), stopping
/// at a `(reason)` or any non-identifier token.
fn parse_ids(rest: &str) -> Vec<String> {
    let mut ids = Vec::new();
    for tok in rest.split([',', ' ', '\t']) {
        let tok = tok.trim();
        if tok.is_empty() {
            continue;
        }
        if tok.starts_with('(') {
            break;
        }
        if tok.chars().all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-')) {
            ids.push(tok.to_string());
        } else {
            break;
        }
    }
    ids
}

#[cfg(test)]
mod tests {
    use super::*;

    fn finding(path: &str, line: u32, msg: &str, id: &'static str) -> Finding {
        Finding {
            path: path.into(),
            line,
            column: 1,
            message: msg.into(),
            identifier: Some(id),
            severity: Severity::Error,
        }
    }

    fn report(findings: Vec<Finding>) -> Report {
        Report { findings, files_analyzed: 1 }
    }

    fn no_sources() -> HashMap<&'static str, &'static str> {
        HashMap::new()
    }

    #[test]
    fn ignore_by_identifier_and_path() {
        let r = report(vec![
            finding("src/Gen/A.php", 3, "bad return", "return.type"),
            finding("src/App.php", 5, "bad return", "return.type"),
        ]);
        let entries = vec![IgnoreEntry {
            identifier: Some("return.type".into()),
            path: Some("src/Gen".into()),
            ..Default::default()
        }];
        let out = apply(r, &entries, false, &no_sources());
        // Only the src/Gen one is suppressed.
        assert_eq!(out.findings.len(), 1);
        assert_eq!(out.findings[0].path, "src/App.php");
    }

    #[test]
    fn ignore_by_message_regex() {
        let r = report(vec![
            finding("a.php", 1, "Cannot call method foo() on null", "method.nonObject"),
            finding("a.php", 2, "unknown class `X`", "class.notFound"),
        ]);
        let entries = vec![IgnoreEntry {
            message: Some("/Cannot call method .* on null/".into()),
            ..Default::default()
        }];
        let out = apply(r, &entries, false, &no_sources());
        assert_eq!(out.findings.len(), 1);
        assert_eq!(out.findings[0].identifier, Some("class.notFound"));
    }

    #[test]
    fn report_unmatched_ignored() {
        let r = report(vec![finding("a.php", 1, "real", "return.type")]);
        let entries = vec![IgnoreEntry { identifier: Some("never.happens".into()), ..Default::default() }];
        let out = apply(r, &entries, true, &no_sources());
        // The real finding stays; an unmatched-ignore finding is added.
        assert!(out.findings.iter().any(|f| f.identifier == Some("return.type")));
        assert!(out.findings.iter().any(|f| f.identifier == Some("ignore.unmatched")));
    }

    #[test]
    fn inline_ignore_next_line_and_same_line() {
        let src = "<?php\n// @phpstan-ignore-next-line\nbad();\nbad(); // @phpstan-ignore-line\n";
        let mut sources = HashMap::new();
        sources.insert("a.php", src);
        let r = report(vec![
            finding("a.php", 3, "x", "class.notFound"), // covered by next-line on line 2
            finding("a.php", 4, "y", "class.notFound"), // covered by same-line on line 4
        ]);
        let out = apply(r, &[], false, &sources);
        assert!(out.findings.is_empty(), "{:?}", out.findings);
    }

    #[test]
    fn inline_ignore_specific_identifier() {
        let src = "<?php\n// @phpstan-ignore return.type\nstuff();\n";
        let mut sources = HashMap::new();
        sources.insert("a.php", src);
        let r = report(vec![
            finding("a.php", 3, "bad return", "return.type"), // suppressed
            finding("a.php", 3, "unknown", "class.notFound"), // not in the id list -> kept
        ]);
        let out = apply(r, &[], false, &sources);
        assert_eq!(out.findings.len(), 1);
        assert_eq!(out.findings[0].identifier, Some("class.notFound"));
    }
}
