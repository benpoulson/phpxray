//! Golden-token test harness (TDD Tier A).
//!
//! PHP's own `token_get_all()` is our authoritative token oracle. The `xtask
//! gen-tokens` command (run on a machine with PHP installed) serializes the
//! oracle's output into committed `*.tokens` fixtures using the textual format
//! implemented here. Lexer tests then lex the paired `*.php` source, render their
//! tokens in the same format, and assert equality — so neither the test suite nor
//! CI ever needs PHP at runtime.
//!
//! ## Fixture format
//!
//! One token per line, three TAB-separated fields:
//!
//! ```text
//! T_VARIABLE\t6..8\t$a
//! '='\t9..10\t=
//! T_LNUMBER\t11..12\t1
//! ```
//!
//! * field 1: canonical name — a `T_*` name, or the literal spelling for
//!   single-character tokens (matching how `token_get_all()` represents them).
//! * field 2: the byte span as `start..end`.
//! * field 3: the source text, with `\`, newline, CR and TAB escaped (see
//!   [`escape_text`]) so every token stays on one line.
//!
//! Blank lines and lines beginning with `#` are ignored (comments / spacing).

use crate::Token;
use php_span::Span;

/// One token in the golden representation.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct GoldenToken {
    pub name: String,
    pub span: Span,
    pub text: String,
}

/// Token names PHP emits that our lexer intentionally drops (whitespace and
/// ordinary comments are trivia). `T_DOC_COMMENT` is deliberately *not* here — we
/// keep doc-comments to attach to declarations.
pub const DEFAULT_IGNORED: &[&str] = &["T_WHITESPACE", "T_COMMENT"];

/// Escape a token's text so it occupies a single fixture line.
pub fn escape_text(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(ch),
        }
    }
    out
}

/// Inverse of [`escape_text`].
pub fn unescape_text(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }
        match chars.next() {
            Some('\\') => out.push('\\'),
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            // Unknown escape: keep both bytes verbatim rather than lose data.
            Some(other) => {
                out.push('\\');
                out.push(other);
            }
            None => out.push('\\'),
        }
    }
    out
}

/// Render golden tokens back to the fixture text format.
pub fn render(tokens: &[GoldenToken]) -> String {
    let mut out = String::new();
    for t in tokens {
        out.push_str(&t.name);
        out.push('\t');
        out.push_str(&format!("{}..{}", t.span.start, t.span.end));
        out.push('\t');
        out.push_str(&escape_text(&t.text));
        out.push('\n');
    }
    out
}

/// An error encountered while parsing a `*.tokens` fixture.
#[derive(Debug, PartialEq, Eq)]
pub struct ParseError {
    pub line: usize,
    pub message: String,
}

/// Parse fixture text into golden tokens.
pub fn parse(text: &str) -> Result<Vec<GoldenToken>, ParseError> {
    let mut out = Vec::new();
    for (i, raw) in text.lines().enumerate() {
        let line_no = i + 1;
        let line = raw.trim_end_matches('\r');
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut fields = line.splitn(3, '\t');
        let name = fields.next().ok_or_else(|| err(line_no, "missing name"))?;
        let span_field = fields.next().ok_or_else(|| err(line_no, "missing span"))?;
        // Text field may be absent for empty-text tokens.
        let text_field = fields.next().unwrap_or("");
        let span = parse_span(span_field).ok_or_else(|| err(line_no, "bad span"))?;
        out.push(GoldenToken {
            name: name.to_string(),
            span,
            text: unescape_text(text_field),
        });
    }
    Ok(out)
}

fn err(line: usize, message: &str) -> ParseError {
    ParseError { line, message: message.to_string() }
}

fn parse_span(s: &str) -> Option<Span> {
    let (a, b) = s.split_once("..")?;
    Some(Span::new(a.trim().parse().ok()?, b.trim().parse().ok()?))
}

/// Build golden tokens from a lexed token stream and its source. Tokens whose
/// kind has no `token_get_all()` analogue (e.g. `Eof`) are skipped.
pub fn from_tokens(tokens: &[Token], source: &str) -> Vec<GoldenToken> {
    tokens
        .iter()
        .filter_map(|t| {
            let name = t.kind.php_name()?;
            Some(GoldenToken {
                name: name.to_string(),
                span: t.span,
                text: t.span.text(source).to_string(),
            })
        })
        .collect()
}

/// Remove tokens whose names appear in `ignored` (used to drop the whitespace and
/// comment tokens PHP emits but we don't).
pub fn filter_ignored(tokens: &[GoldenToken], ignored: &[&str]) -> Vec<GoldenToken> {
    tokens
        .iter()
        .filter(|t| !ignored.contains(&t.name.as_str()))
        .cloned()
        .collect()
}

/// Compare our tokens against the oracle's, returning a human-readable
/// description of the first mismatch (for test failure messages).
pub fn compare(ours: &[GoldenToken], oracle: &[GoldenToken]) -> Result<(), String> {
    let n = ours.len().min(oracle.len());
    for i in 0..n {
        if ours[i] != oracle[i] {
            return Err(format!(
                "token #{i} differs:\n  ours:   {:?}\n  oracle: {:?}",
                ours[i], oracle[i]
            ));
        }
    }
    if ours.len() != oracle.len() {
        return Err(format!(
            "token count differs: ours={}, oracle={} (first {} matched)",
            ours.len(),
            oracle.len(),
            n
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tok(name: &str, start: u32, end: u32, text: &str) -> GoldenToken {
        GoldenToken { name: name.into(), span: Span::new(start, end), text: text.into() }
    }

    #[test]
    fn escape_round_trips() {
        let cases = ["plain", "tab\there", "line\nbreak", "back\\slash", "\r\n"];
        for c in cases {
            assert_eq!(unescape_text(&escape_text(c)), c, "round-trip failed for {c:?}");
        }
    }

    #[test]
    fn render_parse_round_trip() {
        let toks = vec![
            tok("T_OPEN_TAG", 0, 6, "<?php "),
            tok("T_VARIABLE", 6, 8, "$a"),
            tok("'='", 9, 10, "="),
            tok("T_CONSTANT_ENCAPSED_STRING", 11, 18, "'hi\tx'"),
        ];
        let rendered = render(&toks);
        let parsed = parse(&rendered).expect("parse");
        assert_eq!(parsed, toks);
    }

    #[test]
    fn parse_skips_blank_and_comment_lines() {
        let text = "# a header\n\nT_VARIABLE\t0..2\t$x\n";
        let parsed = parse(text).unwrap();
        assert_eq!(parsed, vec![tok("T_VARIABLE", 0, 2, "$x")]);
    }

    #[test]
    fn filter_drops_trivia() {
        let toks = vec![
            tok("T_VARIABLE", 0, 2, "$x"),
            tok("T_WHITESPACE", 2, 3, " "),
            tok("T_COMMENT", 3, 8, "// hi"),
            tok("T_DOC_COMMENT", 8, 19, "/** keep */"),
        ];
        let kept = filter_ignored(&toks, DEFAULT_IGNORED);
        let names: Vec<_> = kept.iter().map(|t| t.name.as_str()).collect();
        assert_eq!(names, ["T_VARIABLE", "T_DOC_COMMENT"]);
    }

    #[test]
    fn compare_reports_mismatch_and_length() {
        let a = vec![tok("T_VARIABLE", 0, 2, "$x")];
        let b = vec![tok("T_VARIABLE", 0, 2, "$y")];
        assert!(compare(&a, &b).is_err());
        assert!(compare(&a, &a).is_ok());
        assert!(compare(&a, &[]).unwrap_err().contains("count differs"));
    }
}
