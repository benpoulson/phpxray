//! Output formatting for a [`Report`]: `table` (human), `json`/`prettyJson`
//! (phpstan-style schema for tooling), `raw` (grep-friendly lines), `github`
//! (Actions annotations), `checkstyle` (XML), `gitlab` (Code Quality JSON),
//! and `junit` (JUnit XML). Non-table formats mirror phpstan's ErrorFormatter
//! output shapes so existing CI integrations keep working.

use crate::Report;
use php_diagnostics::Severity;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

/// The synthetic path suppression bookkeeping findings are reported at
/// (phpstan's "not file specific" errors).
const NON_FILE_PATH: &str = "(ignore)";

/// Presentation-only options (from config, not part of analysis).
#[derive(Debug, Clone, Default)]
pub struct RenderOptions {
    /// Editor link template shown under each table finding; `%file%`,
    /// `%relFile%`, `%line%` and `%column%` placeholders are substituted
    /// (phpstan's `editorUrl`).
    pub editor_url: Option<String>,
    /// Display text for the editor link (phpstan's `editorUrlTitle`); the
    /// substituted URL itself when unset.
    pub editor_url_title: Option<String>,
}

/// Render a report in the named format. Returns `None` for an unknown format.
pub fn render(report: &Report, format: &str) -> Option<String> {
    render_with(report, format, &RenderOptions::default())
}

/// [`render`] with presentation options (editor links in the table format).
pub fn render_with(report: &Report, format: &str, opts: &RenderOptions) -> Option<String> {
    Some(match format {
        "table" => render_table_with(report, opts),
        "json" => render_json(report),
        "prettyJson" => render_json_pretty(report),
        "raw" => render_raw(report),
        "github" => render_github(report),
        "checkstyle" => render_checkstyle(report),
        "gitlab" => render_gitlab(report),
        "junit" => render_junit(report),
        _ => return None,
    })
}

/// Render a report as a human-readable, file-grouped table.
pub fn render_table(report: &Report) -> String {
    render_table_with(report, &RenderOptions::default())
}

/// The editor link line for one finding, when `editorUrl` is configured.
/// With an `editorUrlTitle` the link is emitted as an OSC-8 terminal
/// hyperlink showing the title; without one, the substituted URL itself.
fn editor_line(opts: &RenderOptions, f: &crate::Finding) -> Option<String> {
    let subst = |template: &str| {
        template
            .replace("%file%", &f.path)
            .replace("%relFile%", &f.path)
            .replace("%line%", &f.line.to_string())
            .replace("%column%", &f.column.to_string())
    };
    let url = subst(opts.editor_url.as_deref()?);
    Some(match opts.editor_url_title.as_deref() {
        Some(title) => format!("\u{1b}]8;;{url}\u{1b}\\{}\u{1b}]8;;\u{1b}\\", subst(title)),
        None => url,
    })
}

fn render_table_with(report: &Report, opts: &RenderOptions) -> String {
    let mut out = String::new();
    // Group findings by file, preserving first-seen file order.
    let mut files: Vec<&str> = Vec::new();
    for f in &report.findings {
        if !files.contains(&f.path.as_str()) {
            files.push(&f.path);
        }
    }

    for path in &files {
        out.push_str(path);
        out.push('\n');
        for f in report.findings.iter().filter(|f| &f.path == path) {
            let marker = match f.severity {
                Severity::Error => "error",
                Severity::Warning => "warning",
            };
            let id = f.identifier.map(|i| format!("  ({i})")).unwrap_or_default();
            out.push_str(&format!(
                "  {}:{} {}  {}{}\n",
                f.line, f.column, marker, f.message, id
            ));
            if let Some(link) = editor_line(opts, f) {
                out.push_str(&format!("    {link}\n"));
            }
        }
        out.push('\n');
    }

    let errors = report.error_count();
    // Scan-only files (e.g. vendor) are indexed for symbols, not rule-checked;
    // mention them only when present so small runs stay uncluttered.
    let scanned = if report.files_scanned > 0 {
        format!(", {} scanned", report.files_scanned)
    } else {
        String::new()
    };
    let file_noun = if report.files_analyzed == 1 {
        "file"
    } else {
        "files"
    };
    if errors == 0 {
        out.push_str(&format!(
            "[OK] No errors ({} {file_noun} analyzed{scanned})\n",
            report.files_analyzed
        ));
    } else {
        let noun = if errors == 1 { "error" } else { "errors" };
        out.push_str(&format!(
            "[ERROR] Found {errors} {noun} ({} {file_noun} analyzed{scanned})\n",
            report.files_analyzed
        ));
    }
    out
}

/// phpstan-style JSON, compact (phpstan's `json`). See [`render_json_pretty`]
/// for the indented variant.
pub fn render_json(report: &Report) -> String {
    render_json_impl(report, false)
}

/// phpstan-style JSON, indented (phpstan's `prettyJson`).
pub fn render_json_pretty(report: &Report) -> String {
    render_json_impl(report, true)
}

/// phpstan-style JSON: `{ totals, files: { path: { errors, messages } }, errors }`.
fn render_json_impl(report: &Report, pretty: bool) -> String {
    #[derive(Serialize)]
    struct Out {
        totals: Totals,
        files: BTreeMap<String, FileBlock>,
        errors: Vec<String>,
    }
    #[derive(Serialize)]
    struct Totals {
        errors: usize,
        file_errors: usize,
    }
    #[derive(Serialize)]
    struct FileBlock {
        errors: usize,
        messages: Vec<Message>,
    }
    #[derive(Serialize)]
    struct Message {
        message: String,
        line: u32,
        ignorable: bool,
        identifier: Option<&'static str>,
    }

    let mut files: BTreeMap<String, FileBlock> = BTreeMap::new();
    // Non-file-specific findings (suppression bookkeeping like unmatched
    // ignores, reported at the synthetic "(ignore)" path) go into phpstan's
    // top-level `errors` array and `totals.errors`, not `files`.
    let mut errors: Vec<String> = Vec::new();
    for f in &report.findings {
        if f.path == NON_FILE_PATH {
            errors.push(f.message.clone());
            continue;
        }
        let block = files.entry(f.path.clone()).or_insert(FileBlock {
            errors: 0,
            messages: Vec::new(),
        });
        block.errors += 1;
        block.messages.push(Message {
            message: f.message.clone(),
            line: f.line,
            ignorable: true,
            identifier: f.identifier,
        });
    }
    let out = Out {
        totals: Totals {
            errors: errors.len(),
            file_errors: report.error_count().saturating_sub(errors.len()),
        },
        files,
        errors,
    };
    let rendered = if pretty {
        serde_json::to_string_pretty(&out)
    } else {
        serde_json::to_string(&out)
    };
    rendered.unwrap_or_else(|_| "{}".to_string())
}

/// Grep-friendly `path:line:message` lines (phpstan's `raw`). Non-file
/// findings render as `?:?:message`, first, matching phpstan's order.
pub fn render_raw(report: &Report) -> String {
    let mut out = String::new();
    for f in report.findings.iter().filter(|f| f.path == NON_FILE_PATH) {
        out.push_str(&format!("?:?:{}\n", f.message));
    }
    for f in report.findings.iter().filter(|f| f.path != NON_FILE_PATH) {
        out.push_str(&format!("{}:{}:{}\n", f.path, f.line, f.message));
    }
    out
}

/// GitLab Code Quality report JSON (phpstan's `gitlab`): an array of
/// `{description, check_name, fingerprint, severity, location}` objects.
/// The fingerprint is `sha256(path + line + message)` like phpstan's, so
/// GitLab treats findings as the same issue across runs.
pub fn render_gitlab(report: &Report) -> String {
    let mut items: Vec<serde_json::Value> = Vec::new();
    for f in report.findings.iter().filter(|f| f.path != NON_FILE_PATH) {
        let fingerprint = sha256_hex(&format!("{}{}{}", f.path, f.line, f.message));
        // phpstan: ignorable errors are "major", non-ignorable "blocker".
        let severity = if f.identifier == Some("ignore.parseError") {
            "blocker"
        } else {
            "major"
        };
        items.push(serde_json::json!({
            "description": f.message,
            "check_name": f.identifier,
            "fingerprint": fingerprint,
            "severity": severity,
            "location": { "path": f.path, "lines": { "begin": f.line } },
        }));
    }
    for f in report.findings.iter().filter(|f| f.path == NON_FILE_PATH) {
        items.push(serde_json::json!({
            "description": f.message,
            "fingerprint": sha256_hex(&f.message),
            "severity": "major",
            "location": { "path": "", "lines": { "begin": 0 } },
        }));
    }
    serde_json::to_string_pretty(&items).unwrap_or_else(|_| "[]".to_string())
}

/// JUnit XML (phpstan's `junit`): one `<testcase>` per finding with a
/// `<failure>` child; a single passing `phpstan` case when clean.
pub fn render_junit(report: &Report) -> String {
    let failures = report.error_count();
    let tests = if failures == 0 { 1 } else { failures };
    let mut out = String::from("<?xml version=\"1.0\" encoding=\"UTF-8\"?>");
    out.push_str(&format!(
        "<testsuite failures=\"{failures}\" name=\"phpstan\" tests=\"{tests}\" \
         xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" \
         xsi:noNamespaceSchemaLocation=\"https://raw.githubusercontent.com/junit-team/junit5/r5.5.1/platform-tests/src/test/resources/jenkins-junit.xsd\">"
    ));
    for f in report.findings.iter().filter(|f| f.path != NON_FILE_PATH) {
        out.push_str(&format!(
            "<testcase name=\"{}:{}\"><failure type=\"ERROR\" message=\"{}\" /></testcase>",
            xml_escape(&f.path),
            f.line,
            xml_escape(&f.message)
        ));
    }
    for f in report.findings.iter().filter(|f| f.path == NON_FILE_PATH) {
        out.push_str(&format!(
            "<testcase name=\"General error\"><failure type=\"ERROR\" message=\"{}\" /></testcase>",
            xml_escape(&f.message)
        ));
    }
    if failures == 0 {
        out.push_str("<testcase name=\"phpstan\"></testcase>");
    }
    out.push_str("</testsuite>");
    out
}

fn sha256_hex(input: &str) -> String {
    let digest = Sha256::digest(input.as_bytes());
    digest.iter().map(|b| format!("{b:02x}")).collect()
}

/// GitHub Actions annotations: one `::error` workflow command per finding.
pub fn render_github(report: &Report) -> String {
    let mut out = String::new();
    for f in &report.findings {
        let level = match f.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        };
        let id = f.identifier.map(|i| format!(" ({i})")).unwrap_or_default();
        // Escape per GitHub's workflow-command rules.
        let msg = f
            .message
            .replace('%', "%25")
            .replace('\r', "%0D")
            .replace('\n', "%0A");
        out.push_str(&format!(
            "::{level} file={},line={},col={}::{msg}{id}\n",
            f.path, f.line, f.column
        ));
    }
    out
}

/// Checkstyle XML.
pub fn render_checkstyle(report: &Report) -> String {
    let mut files: BTreeMap<&str, Vec<&crate::Finding>> = BTreeMap::new();
    for f in &report.findings {
        files.entry(&f.path).or_default().push(f);
    }
    let mut out = String::from("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<checkstyle>\n");
    for (path, findings) in &files {
        out.push_str(&format!("  <file name=\"{}\">\n", xml_escape(path)));
        for f in findings {
            let severity = match f.severity {
                Severity::Error => "error",
                Severity::Warning => "warning",
            };
            out.push_str(&format!(
                "    <error line=\"{}\" column=\"{}\" severity=\"{severity}\" message=\"{}\" source=\"{}\"/>\n",
                f.line,
                f.column,
                xml_escape(&f.message),
                xml_escape(f.identifier.unwrap_or("")),
            ));
        }
        out.push_str("  </file>\n");
    }
    out.push_str("</checkstyle>\n");
    out
}

fn xml_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&apos;")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Finding, Report};

    fn finding(path: &str, line: u32, msg: &str, id: &'static str) -> Finding {
        Finding {
            path: path.into(),
            line,
            column: 1,
            message: msg.into(),
            identifier: Some(id),
            severity: Severity::Error,
            fix: None,
        }
    }

    #[test]
    fn table_groups_by_file_and_summarizes() {
        let report = Report {
            findings: vec![
                finding(
                    "src/A.php",
                    3,
                    "should return int but returns string",
                    "return.type",
                ),
                finding("src/A.php", 7, "unknown class `Foo`", "class.notFound"),
            ],
            files_analyzed: 2,
            files_scanned: 0,
            timings: None,
        };
        let out = render_table(&report);
        assert!(out.contains("src/A.php\n"));
        assert!(out.contains("3:1 error  should return int but returns string  (return.type)"));
        assert!(out.contains("[ERROR] Found 2 errors (2 files analyzed)"));
    }

    #[test]
    fn table_ok_when_clean() {
        let report = Report {
            findings: vec![],
            files_analyzed: 5,
            files_scanned: 0,
            timings: None,
        };
        assert!(render_table(&report).contains("[OK] No errors (5 files analyzed)"));
    }

    #[test]
    fn table_mentions_scanned_files_when_present() {
        let report = Report {
            findings: vec![],
            files_analyzed: 5,
            files_scanned: 12,
            timings: None,
        };
        assert!(render_table(&report).contains("[OK] No errors (5 files analyzed, 12 scanned)"));
    }

    #[test]
    fn json_matches_phpstan_shape() {
        let report = Report {
            findings: vec![finding("src/A.php", 4, "bad return", "return.type")],
            files_analyzed: 1,
            files_scanned: 0,
            timings: None,
        };
        let v: serde_json::Value = serde_json::from_str(&render_json(&report)).unwrap();
        assert_eq!(v["totals"]["file_errors"], 1);
        assert_eq!(v["files"]["src/A.php"]["errors"], 1);
        assert_eq!(
            v["files"]["src/A.php"]["messages"][0]["message"],
            "bad return"
        );
        assert_eq!(v["files"]["src/A.php"]["messages"][0]["line"], 4);
        assert_eq!(
            v["files"]["src/A.php"]["messages"][0]["identifier"],
            "return.type"
        );
    }

    #[test]
    fn json_routes_non_file_findings_to_top_level_errors() {
        // phpstan puts non-file-specific errors (e.g. unmatched ignores) into
        // the top-level `errors` array + `totals.errors`, not under `files`.
        let report = Report {
            findings: vec![
                finding("src/A.php", 4, "bad return", "return.type"),
                finding("(ignore)", 0, "Ignored pattern #x# was not matched in reported errors", "ignore.unmatched"),
            ],
            files_analyzed: 1,
            files_scanned: 0,
            timings: None,
        };
        let v: serde_json::Value = serde_json::from_str(&render_json(&report)).unwrap();
        assert_eq!(v["totals"]["errors"], 1);
        assert_eq!(v["totals"]["file_errors"], 1);
        assert!(v["files"].get("(ignore)").is_none());
        assert_eq!(
            v["errors"][0],
            "Ignored pattern #x# was not matched in reported errors"
        );
    }

    #[test]
    fn github_and_checkstyle_formats() {
        let report = Report {
            findings: vec![finding("src/A.php", 4, "bad return", "return.type")],
            files_analyzed: 1,
            files_scanned: 0,
            timings: None,
        };
        assert_eq!(
            render_github(&report).trim(),
            "::error file=src/A.php,line=4,col=1::bad return (return.type)"
        );
        let xml = render_checkstyle(&report);
        assert!(xml.contains("<file name=\"src/A.php\">"));
        assert!(xml.contains("severity=\"error\" message=\"bad return\" source=\"return.type\""));
    }

    #[test]
    fn render_dispatch_unknown_format() {
        let report = Report {
            findings: vec![],
            files_analyzed: 0,
            files_scanned: 0,
            timings: None,
        };
        assert!(render(&report, "table").is_some());
        assert!(render(&report, "json").is_some());
        assert!(render(&report, "prettyJson").is_some());
        assert!(render(&report, "raw").is_some());
        assert!(render(&report, "gitlab").is_some());
        assert!(render(&report, "junit").is_some());
        assert!(render(&report, "nope").is_none());
    }

    #[test]
    fn table_editor_url_line() {
        let report = Report {
            findings: vec![finding("src/A.php", 4, "bad return", "return.type")],
            files_analyzed: 1,
            files_scanned: 0,
            timings: None,
        };
        let opts = RenderOptions {
            editor_url: Some("editor://open?file=%file%&line=%line%&col=%column%".into()),
            editor_url_title: None,
        };
        let out = render_with(&report, "table", &opts).unwrap();
        assert!(
            out.contains("editor://open?file=src/A.php&line=4&col=1"),
            "{out}"
        );
        // A title wraps the URL in an OSC-8 hyperlink showing the title text.
        let titled = RenderOptions {
            editor_url_title: Some("open %relFile%".into()),
            ..opts
        };
        let out = render_with(&report, "table", &titled).unwrap();
        assert!(out.contains("open src/A.php"), "{out}");
        assert!(out.contains("\u{1b}]8;;editor://open"), "{out}");
    }

    #[test]
    fn json_is_compact_and_pretty_json_indented() {
        let report = Report {
            findings: vec![finding("src/A.php", 4, "bad return", "return.type")],
            files_analyzed: 1,
            files_scanned: 0,
            timings: None,
        };
        let compact = render_json(&report);
        let pretty = render_json_pretty(&report);
        assert!(!compact.contains('\n'));
        assert!(pretty.contains('\n'));
        // Same data either way.
        let a: serde_json::Value = serde_json::from_str(&compact).unwrap();
        let b: serde_json::Value = serde_json::from_str(&pretty).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn raw_lines_and_non_file_ordering() {
        let mut report = Report {
            findings: vec![finding("src/A.php", 4, "bad return", "return.type")],
            files_analyzed: 1,
            files_scanned: 0,
            timings: None,
        };
        report
            .findings
            .push(finding("(ignore)", 0, "stale ignore", "ignore.unmatched"));
        assert_eq!(
            render_raw(&report),
            "?:?:stale ignore\nsrc/A.php:4:bad return\n"
        );
    }

    #[test]
    fn gitlab_code_quality_shape() {
        let report = Report {
            findings: vec![finding("src/A.php", 4, "bad return", "return.type")],
            files_analyzed: 1,
            files_scanned: 0,
            timings: None,
        };
        let v: serde_json::Value = serde_json::from_str(&render_gitlab(&report)).unwrap();
        assert_eq!(v[0]["description"], "bad return");
        assert_eq!(v[0]["check_name"], "return.type");
        assert_eq!(v[0]["severity"], "major");
        assert_eq!(v[0]["location"]["path"], "src/A.php");
        assert_eq!(v[0]["location"]["lines"]["begin"], 4);
        // Deterministic sha256 of path+line+message.
        assert_eq!(
            v[0]["fingerprint"],
            sha256_hex("src/A.php4bad return").as_str()
        );
    }

    #[test]
    fn junit_failure_and_clean_shapes() {
        let report = Report {
            findings: vec![finding("src/A.php", 4, "bad \"return\"", "return.type")],
            files_analyzed: 1,
            files_scanned: 0,
            timings: None,
        };
        let xml = render_junit(&report);
        assert!(xml.contains("<testsuite failures=\"1\" name=\"phpstan\" tests=\"1\""));
        assert!(
            xml.contains("<testcase name=\"src/A.php:4\"><failure type=\"ERROR\" message=\"bad &quot;return&quot;\" /></testcase>")
        );
        let clean = Report {
            findings: vec![],
            files_analyzed: 1,
            files_scanned: 0,
            timings: None,
        };
        let xml = render_junit(&clean);
        assert!(xml.contains("failures=\"0\""));
        assert!(xml.contains("tests=\"1\""));
        assert!(xml.contains("<testcase name=\"phpstan\"></testcase>"));
    }
}
