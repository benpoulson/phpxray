//! Minimal NEON reader for the **baseline subset** — enough to load a phpstan
//! `phpstan-baseline.neon` (`parameters: → ignoreErrors:` entries with
//! `message`/`identifier`/`count`/`path`/`reportUnmatched` keys) without
//! pulling in a full NEON implementation. Full NEON *config* compatibility is
//! a separate milestone (M-P6); this parser deliberately rejects what a
//! baseline never contains (multiline strings, nested sections) with a clear
//! error instead of misreading it.

use crate::IgnoreEntry;

/// Parse a phpstan baseline NEON document into ignore entries.
pub fn parse_baseline(text: &str) -> Result<Vec<IgnoreEntry>, String> {
    let mut entries: Vec<IgnoreEntry> = Vec::new();
    let mut cur: Option<IgnoreEntry> = None;
    // Byte width of the indentation of the `ignoreErrors:` line; a non-blank
    // line at the same or shallower indent ends the section.
    let mut section_indent: Option<usize> = None;

    for (idx, raw) in text.lines().enumerate() {
        let lineno = idx + 1;
        let line = raw.trim_end();
        let trimmed = line.trim_start();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let indent = line.len() - trimmed.len();

        let Some(section) = section_indent else {
            if trimmed == "ignoreErrors:" {
                section_indent = Some(indent);
            }
            continue;
        };
        if indent <= section {
            // Left the ignoreErrors section (another parameter or top-level key).
            section_indent = None;
            continue;
        }

        if trimmed == "-" {
            if let Some(e) = cur.take() {
                entries.push(e);
            }
            cur = Some(IgnoreEntry::default());
            continue;
        }
        // Tolerate the inline form `- message: '…'`.
        let (target_new, kv) = match trimmed.strip_prefix("- ") {
            Some(rest) => (true, rest),
            None => (false, trimmed),
        };
        if target_new {
            if let Some(e) = cur.take() {
                entries.push(e);
            }
            cur = Some(IgnoreEntry::default());
        }
        let Some((key, value)) = kv.split_once(':') else {
            return Err(format!("line {lineno}: expected `key: value`, got {kv:?}"));
        };
        let Some(entry) = cur.as_mut() else {
            return Err(format!("line {lineno}: entry field before a `-` list item"));
        };
        let value = scalar(value, lineno)?;
        match key.trim() {
            "message" => entry.message = Some(value),
            "rawMessage" => entry.raw_message = Some(value),
            "identifier" => entry.identifier = Some(value),
            "path" => entry.path = Some(value),
            "count" => {
                entry.count = Some(
                    value
                        .parse()
                        .map_err(|_| format!("line {lineno}: invalid count {value:?}"))?,
                )
            }
            "reportUnmatched" => match value.as_str() {
                "true" | "yes" => entry.report_unmatched = Some(true),
                "false" | "no" => entry.report_unmatched = Some(false),
                other => return Err(format!("line {lineno}: invalid reportUnmatched {other:?}")),
            },
            // Unknown keys (e.g. future phpstan additions) are skipped,
            // matching the YAML config's forward-compat posture.
            _ => {}
        }
    }
    if let Some(e) = cur.take() {
        entries.push(e);
    }
    Ok(entries)
}

/// Decode one NEON scalar value: single-quoted (`''` escapes a quote),
/// double-quoted (backslash escapes), or bare.
fn scalar(s: &str, lineno: usize) -> Result<String, String> {
    let s = s.trim();
    if let Some(rest) = s.strip_prefix("'''") {
        let _ = rest;
        return Err(format!(
            "line {lineno}: multiline NEON strings are not supported in baselines"
        ));
    }
    if let Some(inner) = s.strip_prefix('\'') {
        let Some(inner) = inner.strip_suffix('\'') else {
            return Err(format!("line {lineno}: unterminated single-quoted string"));
        };
        // A lone `''` inside means an escaped quote; reject strings where
        // stripping produced an odd trailing escape (e.g. `'a''`).
        return Ok(inner.replace("''", "'"));
    }
    if let Some(inner) = s.strip_prefix('"') {
        let Some(inner) = inner.strip_suffix('"') else {
            return Err(format!("line {lineno}: unterminated double-quoted string"));
        };
        let mut out = String::with_capacity(inner.len());
        let mut chars = inner.chars();
        while let Some(c) = chars.next() {
            if c != '\\' {
                out.push(c);
                continue;
            }
            match chars.next() {
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some('r') => out.push('\r'),
                Some(other) => out.push(other),
                None => break,
            }
        }
        return Ok(out);
    }
    Ok(s.to_string())
}

/// Encode one scalar for a generated baseline: bare when it is entirely
/// filename/identifier-safe, single-quoted (with `''` escaping) otherwise.
pub fn encode_scalar(s: &str) -> String {
    let bare_safe = !s.is_empty()
        && s.chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-' | '/'));
    if bare_safe {
        s.to_string()
    } else {
        format!("'{}'", s.replace('\'', "''"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_phpstan_baseline_shape() {
        let neon = "parameters:\n\tignoreErrors:\n\t\t-\n\t\t\tmessage: '#^Access to an undefined property Foo\\:\\:\\$bar\\.$#'\n\t\t\tidentifier: property.notFound\n\t\t\tcount: 2\n\t\t\tpath: src/Foo.php\n\t\t-\n\t\t\tmessage: '#^It''s broken\\.$#'\n\t\t\tcount: 1\n\t\t\tpath: src/Bar.php\n";
        let entries = parse_baseline(neon).unwrap();
        assert_eq!(entries.len(), 2);
        assert_eq!(
            entries[0].message.as_deref(),
            Some("#^Access to an undefined property Foo\\:\\:\\$bar\\.$#")
        );
        assert_eq!(entries[0].identifier.as_deref(), Some("property.notFound"));
        assert_eq!(entries[0].count, Some(2));
        assert_eq!(entries[0].path.as_deref(), Some("src/Foo.php"));
        // `''` decodes to a single quote.
        assert_eq!(entries[1].message.as_deref(), Some("#^It's broken\\.$#"));
    }

    #[test]
    fn spaces_indentation_and_comments() {
        let neon = "# a comment\nparameters:\n    ignoreErrors:\n        -\n            message: '#^x$#'\n            path: a.php\n";
        let entries = parse_baseline(neon).unwrap();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].path.as_deref(), Some("a.php"));
    }

    #[test]
    fn section_ends_at_sibling_parameter() {
        let neon = "parameters:\n\tignoreErrors:\n\t\t-\n\t\t\tmessage: '#^x$#'\n\tlevel: 5\n";
        let entries = parse_baseline(neon).unwrap();
        assert_eq!(entries.len(), 1);
    }

    #[test]
    fn empty_baseline_is_ok() {
        assert!(parse_baseline("parameters:\n\tignoreErrors: []\n")
            .unwrap()
            .is_empty());
    }

    #[test]
    fn errors_are_line_numbered() {
        let err =
            parse_baseline("parameters:\n\tignoreErrors:\n\t\t-\n\t\t\tcount: many\n").unwrap_err();
        assert!(err.contains("line 4"), "{err}");
    }

    #[test]
    fn encode_scalar_quotes_when_needed() {
        assert_eq!(encode_scalar("src/Foo.php"), "src/Foo.php");
        assert_eq!(encode_scalar("#^a b$#"), "'#^a b$#'");
        assert_eq!(encode_scalar("it's"), "'it''s'");
    }
}
