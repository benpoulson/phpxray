//! phpstan category **Classes** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Classes/` — 37 rule(s) at level(s) 0,1,2,4.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to `RULES`
//! (with a phpstan-style identifier on its diagnostics).

use crate::{unknown_symbols, FileAnalysis, RuleEntry};
use php_diagnostics::Diagnostic;

// Our consolidated existence check: emits `class.notFound` + `function.notFound`
// + `constant.notFound`. phpstan spreads these across Classes/, Functions/, and
// Constants/; we may split it as those categories are fleshed out.
fn run_unknown_symbols(fa: &FileAnalysis) -> Vec<Diagnostic> {
    unknown_symbols(fa.project, fa.resolved_refs)
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "unknown-symbol", level: 0, run: run_unknown_symbols },
];
