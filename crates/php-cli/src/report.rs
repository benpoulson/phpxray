//! Output formatting for a [`Report`]. M-C2 ships the human `table` format;
//! `json`/`github`/`checkstyle` follow in M-C3.

use crate::Report;
use php_diagnostics::Severity;

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
            out.push_str(&format!("  {}:{} {}  {}{}\n", f.line, f.column, marker, f.message, id));
        }
        out.push('\n');
    }

    let errors = report.error_count();
    if errors == 0 {
        out.push_str(&format!("[OK] No errors ({} files analyzed)\n", report.files_analyzed));
    } else {
        let noun = if errors == 1 { "error" } else { "errors" };
        out.push_str(&format!("[ERROR] Found {errors} {noun} ({} files analyzed)\n", report.files_analyzed));
    }
    out
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
                finding("src/A.php", 3, "should return int but returns string", "return.type"),
                finding("src/A.php", 7, "unknown class `Foo`", "class.notFound"),
            ],
            files_analyzed: 2,
        };
        let out = render_table(&report);
        assert!(out.contains("src/A.php\n"));
        assert!(out.contains("3:1 error  should return int but returns string  (return.type)"));
        assert!(out.contains("[ERROR] Found 2 errors (2 files analyzed)"));
    }

    #[test]
    fn table_ok_when_clean() {
        let report = Report { findings: vec![], files_analyzed: 5 };
        assert!(render_table(&report).contains("[OK] No errors (5 files analyzed)"));
    }
}
