//! Parsing of PHP's `.phpt` test files.
//!
//! `.phpt` files are PHP's own test format: a sequence of `--SECTION--` headers,
//! each followed by that section's body. We reuse PHP's 5,329-file `Zend/tests`
//! suite as a parser corpus by pulling the raw source out of the `--FILE--`
//! section of each test. The `--EXPECT--`/`--EXPECTF--` section tells us whether
//! a test deliberately asserts a parse error (used by the error-recovery suite).

/// If `line` is a section header like `--FILE--`, return the section name
/// (`FILE`). A header is a line that, once trimmed, starts and ends with `--`.
fn section_name(line: &str) -> Option<&str> {
    let t = line.trim_end_matches(['\r', '\n']);
    let inner = t.strip_prefix("--")?.strip_suffix("--")?;
    // Reject empty (`----`) and obviously-non-header content.
    if inner.is_empty() {
        return None;
    }
    Some(inner)
}

/// Return the body of the named section (e.g. `"FILE"`), if present.
///
/// The body is the lines between the header and the next header, joined with
/// `\n`, with the trailing newline that precedes the next header dropped (mirrors
/// how PHP's run-tests harness treats section bodies).
pub fn extract_section(phpt: &str, name: &str) -> Option<String> {
    let mut found = false;
    let mut collecting = false;
    let mut body: Vec<&str> = Vec::new();
    for line in phpt.lines() {
        if let Some(header) = section_name(line) {
            if collecting {
                // Reached the next section; stop collecting.
                break;
            }
            collecting = header == name;
            found |= collecting;
            continue;
        }
        if collecting {
            body.push(line);
        }
    }
    found.then(|| body.join("\n"))
}

/// The raw PHP source under the `--FILE--` section.
pub fn extract_file_section(phpt: &str) -> Option<String> {
    extract_section(phpt, "FILE")
}

/// Whether the test's expectation indicates an intentional parse/compile error.
/// Used to select the error-recovery subset of the corpus.
pub fn expects_parse_error(phpt: &str) -> bool {
    for sect in ["EXPECT", "EXPECTF", "EXPECTREGEX"] {
        if let Some(body) = extract_section(phpt, sect) {
            let lower = body.to_ascii_lowercase();
            if lower.contains("parse error") || lower.contains("syntax error") {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = "\
--TEST--
Basic test
--FILE--
<?php
echo \"Hello\";
?>
--EXPECT--
Hello
";

    #[test]
    fn extracts_file_body() {
        let file = extract_file_section(SAMPLE).unwrap();
        assert_eq!(file, "<?php\necho \"Hello\";\n?>");
    }

    #[test]
    fn extracts_named_section() {
        assert_eq!(extract_section(SAMPLE, "TEST").unwrap(), "Basic test");
        assert_eq!(extract_section(SAMPLE, "EXPECT").unwrap(), "Hello");
        assert!(extract_section(SAMPLE, "SKIPIF").is_none());
    }

    #[test]
    fn detects_parse_error_expectation() {
        let err = "\
--TEST--
unterminated
--FILE--
<?php /* foo
--EXPECTF--
Parse error: Unterminated comment starting line 1 in %s on line %d
";
        assert!(expects_parse_error(err));
        assert!(!expects_parse_error(SAMPLE));
    }

    #[test]
    fn section_header_recognition() {
        assert_eq!(section_name("--FILE--"), Some("FILE"));
        assert_eq!(section_name("--EXPECTF--"), Some("EXPECTF"));
        assert_eq!(section_name("----"), None);
        assert_eq!(section_name("not a header"), None);
        assert_eq!(section_name("<?php // --FILE--"), None);
    }
}
