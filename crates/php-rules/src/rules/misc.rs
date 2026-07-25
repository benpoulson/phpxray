//! phpstan category **(root)** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/` — 1 rule(s) at level(s) 5.
//! Rules directly under src/Rules/ (no subdir).The rule set's coverage truth is `cargo run -p xtask -- rule-manifest`. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).

#![allow(unused_imports)]
use crate::{FileAnalysis, RuleEntry};
use php_diagnostics::Diagnostic;

pub(crate) static RULES: &[RuleEntry] = &[];
