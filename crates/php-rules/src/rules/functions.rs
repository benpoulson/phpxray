//! phpstan category **Functions** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Functions/` — 41 rule(s) at level(s) 0–6.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to `RULES`
//! (with a phpstan-style identifier on its diagnostics).

use crate::{return_type_errors, FileAnalysis, RuleEntry};
use php_diagnostics::Diagnostic;

fn run_return_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    return_type_errors(fa.reflection, fa.program, fa.interner)
}

pub(crate) static RULES: &[RuleEntry] = &[
    // Checks each `return <expr>` against the declared return type. Also covers
    // method returns (phpstan splits these across Functions/ and Methods/).
    RuleEntry { name: "return-type", level: 3, run: run_return_type },
];
