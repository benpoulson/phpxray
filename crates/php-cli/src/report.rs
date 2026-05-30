//! Output formatting for a [`Report`]: `table` (human), `json` (phpstan-style
//! schema for tooling), `github` (Actions annotations), and `checkstyle` (XML).

use crate::Report;
use php_diagnostics::Severity;
use serde::Serialize;
use std::collections::BTreeMap;

/// Render a report in the named format. Returns `None` for an unknown format.
pub fn render(report: &Report, format: &str) -> Option<String> {
    Some(match format {
        "table" => render_table(report),
        "json" => render_json(report),
        "github" => render_github(report),
        "checkstyle" => render_checkstyle(report),
        _ => return None,
    })
}

/// Render a report as a human-readable, file-grouped table.
pub fn render_table(report: &Report) -> String {
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
        }
        out.push('\n');
    }

    let errors = report.error_count();
    if errors == 0 {
        out.push_str(&format!(
            "[OK] No errors ({} files analyzed)\n",
            report.files_analyzed
        ));
    } else {
        let noun = if errors == 1 { "error" } else { "errors" };
        out.push_str(&format!(
            "[ERROR] Found {errors} {noun} ({} files analyzed)\n",
            report.files_analyzed
        ));
    }
    out
}

/// phpstan-style JSON: `{ totals, files: { path: { errors, messages } }, errors }`.
pub fn render_json(report: &Report) -> String {
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
    for f in &report.findings {
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
            errors: 0,
            file_errors: report.error_count(),
        },
        files,
        errors: Vec::new(),
    };
    serde_json::to_string_pretty(&out).unwrap_or_else(|_| "{}".to_string())
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
            timings: None,
        };
        assert!(render_table(&report).contains("[OK] No errors (5 files analyzed)"));
    }

    #[test]
    fn json_matches_phpstan_shape() {
        let report = Report {
            findings: vec![finding("src/A.php", 4, "bad return", "return.type")],
            files_analyzed: 1,
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
    fn github_and_checkstyle_formats() {
        let report = Report {
            findings: vec![finding("src/A.php", 4, "bad return", "return.type")],
            files_analyzed: 1,
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
            timings: None,
        };
        assert!(render(&report, "table").is_some());
        assert!(render(&report, "json").is_some());
        assert!(render(&report, "nope").is_none());
    }
}
