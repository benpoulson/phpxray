//! M-C5: **baseline** — snapshot current findings so a legacy codebase passes,
//! then ratchet down over time.
//!
//! Generating writes a YAML file of `ignore` entries (grouped by message + path
//! with a count). Consuming is free: the file is just `ignore:` entries, so
//! `php_config::Config::load` reads it and the engine merges them into the active
//! ignore set (see the binary). A baselined error that disappears is surfaced via
//! `reportUnmatchedIgnored`, nudging you to shrink the baseline.

use crate::Report;
use serde::Serialize;
use std::collections::BTreeMap;

/// One baseline entry: an exact message (as an anchored regex) for a file, with
/// the number of occurrences.
#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct Entry {
    pub message: String,
    pub count: usize,
    pub path: String,
}

/// Collect a report's findings into baseline entries (sorted, deduped by
/// message+path with counts). Synthetic unmatched-ignore findings are excluded.
pub fn entries(report: &Report) -> Vec<Entry> {
    let mut counts: BTreeMap<(String, String), usize> = BTreeMap::new();
    for f in &report.findings {
        if f.identifier == Some("ignore.unmatched") {
            continue;
        }
        // Anchored, regex-escaped exact message (matches the suppression layer's
        // `#…#` delimiter convention).
        let message = format!("#^{}$#", regex::escape(&f.message));
        *counts.entry((f.path.clone(), message)).or_default() += 1;
    }
    counts
        .into_iter()
        .map(|((path, message), count)| Entry {
            message,
            count,
            path,
        })
        .collect()
}

/// Serialize entries to a baseline YAML document (`ignore:` list).
pub fn to_yaml(entries: &[Entry]) -> String {
    #[derive(Serialize)]
    struct Baseline<'a> {
        ignore: &'a [Entry],
    }
    serde_yaml::to_string(&Baseline { ignore: entries }).unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{suppress, Finding, Report};
    use php_config::Config;
    use php_diagnostics::Severity;
    use std::collections::HashMap;

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
    fn groups_and_counts() {
        let report = Report {
            findings: vec![
                finding("a.php", 1, "bad return", "return.type"),
                finding("a.php", 5, "bad return", "return.type"),
                finding("b.php", 2, "unknown class `X`", "class.notFound"),
            ],
            files_analyzed: 2,
            timings: None,
        };
        let es = entries(&report);
        // (a.php, "bad return") x2 and (b.php, ...) x1.
        let a = es.iter().find(|e| e.path == "a.php").unwrap();
        assert_eq!(a.count, 2);
        assert_eq!(a.message, "#^bad return$#");
        assert!(es.iter().any(|e| e.path == "b.php" && e.count == 1));
    }

    #[test]
    fn round_trips_through_config_and_suppresses() {
        // Generate a baseline from a report, load it as config ignore, and apply
        // it back to the same report -> everything is suppressed.
        let report = Report {
            findings: vec![
                finding(
                    "src/A.php",
                    4,
                    "should return int but returns string",
                    "return.type",
                ),
                finding("src/B.php", 9, "unknown class `Foo`", "class.notFound"),
            ],
            files_analyzed: 2,
            timings: None,
        };
        let yaml = to_yaml(&entries(&report));
        let cfg = Config::from_yaml(&yaml).unwrap();
        assert_eq!(cfg.ignore.len(), 2);

        let out = suppress::apply(report, &cfg.ignore, false, &HashMap::new());
        assert!(
            out.findings.is_empty(),
            "baseline should suppress all: {:?}",
            out.findings
        );
    }
}
