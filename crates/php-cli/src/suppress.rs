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
    let inline: HashMap<&str, InlineIgnores> = sources
        .iter()
        .map(|(path, src)| (*path, inline_ignores(src)))
        .collect();

    let mut kept = Vec::new();
    for f in report.findings {
        // Inline ignore?
        if let Some(inline) = inline.get(f.path.as_str()) {
            if suppressed_inline(&inline.map, &f) {
                continue;
            }
        }
        // Config ignore?
        if matchers.iter_mut().any(|m| m.try_suppress(&f)) {
            continue;
        }
        kept.push(f);
    }

    for (path, inline) in &inline {
        for (line, message) in &inline.parse_errors {
            kept.push(Finding {
                path: (*path).to_string(),
                line: *line,
                column: 0,
                message: format!("Parse error in @phpstan-ignore: {message}"),
                identifier: Some("ignore.parseError"),
                severity: Severity::Error,
            });
        }
    }

    if report_unmatched {
        for m in &matchers {
            if m.matched == 0 {
                kept.push(Finding {
                    path: "(ignore)".to_string(),
                    line: 0,
                    column: 0,
                    message: format!(
                        "Ignored pattern {} was not matched in reported errors",
                        m.describe()
                    ),
                    identifier: Some("ignore.unmatched"),
                    severity: Severity::Error,
                });
            } else if let Some(expected) = m.count {
                if m.matched < expected {
                    kept.push(Finding {
                        path: "(ignore)".to_string(),
                        line: 0,
                        column: 0,
                        message: format!(
                            "Ignored pattern {} was expected to match {expected} times, but matched {} times",
                            m.describe(),
                            m.matched
                        ),
                        identifier: Some("ignore.unmatched"),
                        severity: Severity::Error,
                    });
                }
            }
        }
    }

    Report {
        findings: kept,
        files_analyzed: report.files_analyzed,
    }
}

/// A compiled config ignore entry.
struct Matcher {
    message: Option<Regex>,
    identifier: Option<String>,
    /// Path constraint (subtree-aware, like excludes); `None` = any path.
    paths: Option<ExcludeMatcher>,
    /// Maximum number of findings this entry may suppress. `None` means unlimited.
    count: Option<usize>,
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
        let desc = e
            .message
            .clone()
            .or_else(|| e.identifier.clone())
            .unwrap_or_default();
        Some(Matcher {
            message,
            identifier: e.identifier.clone(),
            paths,
            count: e.count,
            matched: 0,
            desc,
        })
    }

    fn try_suppress(&mut self, f: &Finding) -> bool {
        if !self.matches(f) {
            return false;
        }
        if self.count.is_some_and(|count| self.matched >= count) {
            return false;
        }
        self.matched += 1;
        true
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

struct InlineIgnores {
    map: HashMap<u32, Spec>,
    parse_errors: Vec<(u32, String)>,
}

fn suppressed_inline(map: &HashMap<u32, Spec>, f: &Finding) -> bool {
    match map.get(&f.line) {
        Some(Spec::All) => true,
        Some(Spec::Ids(ids)) => f
            .identifier
            .map(|id| ids.iter().any(|x| x == id))
            .unwrap_or(false),
        None => false,
    }
}

/// Scan source for inline ignore comments, mapping target line → what to ignore.
fn inline_ignores(source: &str) -> InlineIgnores {
    let mut map: HashMap<u32, Spec> = HashMap::new();
    let mut parse_errors = Vec::new();
    for (i, line) in source.lines().enumerate() {
        let lineno = (i + 1) as u32;
        match marker(line, lineno) {
            Marker::Ignore(target, spec) => merge(&mut map, target, spec),
            Marker::ParseError(line, msg) => parse_errors.push((line, msg)),
            Marker::None => {}
        }
    }
    InlineIgnores { map, parse_errors }
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
enum Marker {
    Ignore(u32, Spec),
    ParseError(u32, String),
    None,
}

fn marker(line: &str, lineno: u32) -> Marker {
    for (prefix, strict) in [("@phpstan-ignore", true), ("@php-analyzer-ignore", false)] {
        if let Some(pos) = line.find(prefix) {
            let mut rest = &line[pos + prefix.len()..];
            if let Some(end) = rest.find("*/") {
                rest = &rest[..end];
            }
            if rest.starts_with("-next-line") {
                return Marker::Ignore(lineno + 1, Spec::All);
            }
            if rest.starts_with("-line") {
                return Marker::Ignore(lineno, Spec::All);
            }
            let target = if is_trailing_comment(&line[..pos]) {
                lineno
            } else {
                lineno + 1
            };
            if strict {
                return match parse_ids_strict(rest) {
                    Ok(ids) => Marker::Ignore(target, Spec::Ids(ids)),
                    Err(msg) => Marker::ParseError(lineno, msg),
                };
            }
            let ids = parse_ids_lenient(rest);
            return Marker::Ignore(
                target,
                if ids.is_empty() {
                    Spec::All
                } else {
                    Spec::Ids(ids)
                },
            );
        }
    }
    Marker::None
}

/// Whether the text before the marker contains code (a trailing comment) rather
/// than just the comment opener and whitespace (a standalone comment).
fn is_trailing_comment(before: &str) -> bool {
    let trimmed = before
        .trim_end()
        .trim_end_matches(['/', '*', '#', ' ', '\t']);
    !trimmed.trim().is_empty()
}

/// Identifiers after a bare `@phpstan-ignore` (comma/space separated), stopping
/// at a `(reason)` or any non-identifier token.
fn parse_ids_lenient(rest: &str) -> Vec<String> {
    let mut ids = Vec::new();
    for tok in rest.split([',', ' ', '\t']) {
        let tok = tok.trim();
        if tok.is_empty() {
            continue;
        }
        if tok.starts_with('(') {
            break;
        }
        if tok
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-'))
        {
            ids.push(tok.to_string());
        } else {
            break;
        }
    }
    ids
}

fn parse_ids_strict(rest: &str) -> Result<Vec<String>, String> {
    let mut p = IgnoreIdParser {
        s: rest,
        pos: 0,
        last: "@phpstan-ignore",
    };
    p.parse()
}

struct IgnoreIdParser<'a> {
    s: &'a str,
    pos: usize,
    last: &'static str,
}

impl<'a> IgnoreIdParser<'a> {
    fn parse(&mut self) -> Result<Vec<String>, String> {
        let mut ids = Vec::new();
        let mut expect_identifier = true;
        loop {
            self.skip_ws();
            if self.eof() {
                if ids.is_empty() {
                    return Err("Missing identifier".to_string());
                }
                if expect_identifier {
                    return Err("Unexpected end after comma (,), expected identifier".to_string());
                }
                return Ok(ids);
            }
            if expect_identifier {
                let Some(id) = self.identifier() else {
                    return Err(self.unexpected("identifier"));
                };
                ids.push(id);
                self.last = "identifier";
                expect_identifier = false;
                continue;
            }
            match self.peek() {
                Some(b',') => {
                    self.pos += 1;
                    self.last = "comma (,)";
                    expect_identifier = true;
                }
                Some(b'(') => {
                    self.comment()?;
                    self.last = "T_CLOSE_PARENTHESIS";
                }
                Some(_) => return Err(self.unexpected("comma (,) or end or T_OPEN_PARENTHESIS")),
                None => return Ok(ids),
            }
        }
    }

    fn comment(&mut self) -> Result<(), String> {
        let mut depth = 0u32;
        while let Some(b) = self.peek() {
            self.pos += 1;
            match b {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        return Ok(());
                    }
                }
                _ => {}
            }
        }
        Err("Unexpected end, unclosed opening parenthesis".to_string())
    }

    fn identifier(&mut self) -> Option<String> {
        let start = self.pos;
        while let Some(b) = self.peek() {
            let c = b as char;
            if c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-') {
                self.pos += 1;
            } else {
                break;
            }
        }
        (self.pos > start).then(|| self.s[start..self.pos].to_string())
    }

    fn unexpected(&self, expected: &str) -> String {
        match self.peek() {
            Some(b'(') => format!(
                "Unexpected T_OPEN_PARENTHESIS after {}, expected {expected}",
                self.last
            ),
            Some(b')') => format!(
                "Unexpected T_CLOSE_PARENTHESIS after {}, expected {expected}",
                self.last
            ),
            Some(b',') => format!(
                "Unexpected comma (,) after {}, expected {expected}",
                self.last
            ),
            Some(_) => {
                let content = self.other_token();
                format!(
                    "Unexpected T_OTHER '{content}' after {}, expected {expected}",
                    self.last
                )
            }
            None => format!("Unexpected end after {}, expected {expected}", self.last),
        }
    }

    fn other_token(&self) -> &str {
        let start = self.pos;
        let mut end = start;
        for (off, ch) in self.s[start..].char_indices() {
            if ch.is_whitespace() || matches!(ch, '(' | ')') {
                break;
            }
            end = start + off + ch.len_utf8();
        }
        if end == start {
            &self.s[start..start + 1]
        } else {
            &self.s[start..end]
        }
    }

    fn skip_ws(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t')) {
            self.pos += 1;
        }
    }

    fn eof(&self) -> bool {
        self.pos >= self.s.len()
    }

    fn peek(&self) -> Option<u8> {
        self.s.as_bytes().get(self.pos).copied()
    }
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
        Report {
            findings,
            files_analyzed: 1,
        }
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
            finding(
                "a.php",
                1,
                "Cannot call method foo() on null",
                "method.nonObject",
            ),
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
        let entries = vec![IgnoreEntry {
            identifier: Some("never.happens".into()),
            ..Default::default()
        }];
        let out = apply(r, &entries, true, &no_sources());
        // The real finding stays; an unmatched-ignore finding is added.
        assert!(out
            .findings
            .iter()
            .any(|f| f.identifier == Some("return.type")));
        assert!(out
            .findings
            .iter()
            .any(|f| f.identifier == Some("ignore.unmatched")));
    }

    #[test]
    fn count_limits_suppression() {
        let r = report(vec![
            finding("a.php", 1, "unknown class `Foo`", "class.notFound"),
            finding("a.php", 2, "unknown class `Foo`", "class.notFound"),
        ]);
        let entries = vec![IgnoreEntry {
            message: Some("#^unknown class `Foo`$#".into()),
            path: Some("a.php".into()),
            count: Some(1),
            ..Default::default()
        }];
        let out = apply(r, &entries, false, &no_sources());
        assert_eq!(out.findings.len(), 1);
        assert_eq!(out.findings[0].line, 2);
        assert_eq!(out.findings[0].identifier, Some("class.notFound"));
    }

    #[test]
    fn report_unmatched_ignored_reports_partial_count() {
        let r = report(vec![finding(
            "a.php",
            1,
            "unknown class `Foo`",
            "class.notFound",
        )]);
        let entries = vec![IgnoreEntry {
            message: Some("#^unknown class `Foo`$#".into()),
            path: Some("a.php".into()),
            count: Some(2),
            ..Default::default()
        }];
        let out = apply(r, &entries, true, &no_sources());
        assert_eq!(out.findings.len(), 1);
        let unmatched = &out.findings[0];
        assert_eq!(unmatched.identifier, Some("ignore.unmatched"));
        assert!(unmatched.message.contains("expected to match 2 times"));
        assert!(unmatched.message.contains("matched 1 times"));
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

    #[test]
    fn malformed_phpstan_ignore_reports_parse_error_and_does_not_suppress() {
        let src = "<?php\n// @phpstan-ignore\nstuff();\n";
        let mut sources = HashMap::new();
        sources.insert("a.php", src);
        let r = report(vec![finding("a.php", 3, "bad return", "return.type")]);
        let out = apply(r, &[], false, &sources);
        assert_eq!(out.findings.len(), 2);
        assert!(out
            .findings
            .iter()
            .any(|f| f.identifier == Some("return.type")));
        let parse = out
            .findings
            .iter()
            .find(|f| f.identifier == Some("ignore.parseError"))
            .unwrap();
        assert_eq!(parse.line, 2);
        assert_eq!(
            parse.message,
            "Parse error in @phpstan-ignore: Missing identifier"
        );
    }

    #[test]
    fn malformed_phpstan_ignore_comment_parenthesis_is_reported() {
        let src = "<?php\n// @phpstan-ignore return.type (reason\nstuff();\n";
        let mut sources = HashMap::new();
        sources.insert("a.php", src);
        let r = report(vec![finding("a.php", 3, "bad return", "return.type")]);
        let out = apply(r, &[], false, &sources);
        assert!(out
            .findings
            .iter()
            .any(|f| f.identifier == Some("return.type")));
        assert!(out.findings.iter().any(|f| {
            f.identifier == Some("ignore.parseError")
                && f.message == "Parse error in @phpstan-ignore: Unexpected end, unclosed opening parenthesis"
        }));
    }

    #[test]
    fn phpdoc_ignore_closing_marker_is_not_part_of_directive() {
        let src = "<?php\n/** @phpstan-ignore return.type */\nstuff();\n";
        let mut sources = HashMap::new();
        sources.insert("a.php", src);
        let r = report(vec![finding("a.php", 3, "bad return", "return.type")]);
        let out = apply(r, &[], false, &sources);
        assert!(out.findings.is_empty(), "{:?}", out.findings);
    }
}
