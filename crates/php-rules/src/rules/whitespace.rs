//! phpstan category **Whitespace** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Whitespace/` — 1 rule(s) at level(s) 0.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented (`FileWhitespaceRule`, level 0):
//! - `whitespace.bom` — the file begins with a UTF-8 byte-order-mark.
//! - `whitespace.fileEnd` — the file ends with trailing whitespace, i.e. the
//!   final inline-HTML region (after the last `?>`, or a stray inline-HTML at the
//!   end of a namespace/declare body) is non-empty and consists solely of
//!   whitespace.
//!
//! phpstan derives both from the AST: it inspects the first/last `InlineHTML`
//! nodes (recursing only into `declare`/`namespace` bodies for the trailing
//! check). We mirror that exactly. The BOM is detected on the raw source, which
//! is byte-for-byte equivalent and avoids depending on how the lexer treats a
//! leading BOM.

#![allow(unused_imports)]
use crate::{FileAnalysis, RuleEntry};
use php_ast::{Stmt, StmtKind};
use php_diagnostics::Diagnostic;
use php_span::Span;

/// The UTF-8 byte-order-mark.
const BOM: &str = "\u{feff}";

const BOM_MSG: &str = "File begins with UTF-8 BOM character. This may cause problems when running the code in the web browser.";
const TRAILING_MSG: &str = "File ends with a trailing whitespace. This may cause problems when running the code in the web browser. Remove the closing ?> mark or remove the whitespace.";

/// `FileWhitespaceRule` (level 0).
fn run_file_whitespace(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();

    // --- BOM (reported at the very start of the file, i.e. line 1). ---
    if fa.source.starts_with(BOM) {
        let len = BOM.len() as u32;
        out.push(Diagnostic::error(Span::new(0, len), BOM_MSG).with_code("whitespace.bom"));
    }

    // --- Trailing whitespace. ---
    // phpstan considers the file-level last node and the last node of each
    // top-level `declare`/`namespace` body. Any that is an inline-HTML region of
    // pure (non-empty) whitespace is flagged.
    for last in trailing_candidates(&fa.program.stmts) {
        if let StmtKind::InlineHtml(text) = &last.kind {
            if is_all_whitespace(text) {
                out.push(
                    Diagnostic::error(last.span, TRAILING_MSG).with_code("whitespace.fileEnd"),
                );
            }
        }
    }

    out
}

/// The statements that phpstan checks for trailing whitespace: the last
/// statement of each top-level `declare`/`namespace` body, plus the last
/// top-level statement (mirroring `FileWhitespaceRule`'s visitor + the final
/// `array_last($nodes)`).
fn trailing_candidates(stmts: &[Stmt]) -> Vec<&Stmt> {
    let mut out: Vec<&Stmt> = Vec::new();
    for s in stmts {
        match &s.kind {
            StmtKind::Declare {
                body: Some(body), ..
            } => {
                // A `declare(...) { ... }` block body — phpstan reads the body's
                // last statement. Our body is a single `Stmt` (often a `Block`).
                if let StmtKind::Block(inner) = &body.kind {
                    if let Some(last) = inner.last() {
                        out.push(last);
                    }
                } else {
                    out.push(body);
                }
            }
            StmtKind::Namespace {
                body: Some(body), ..
            } => {
                if let Some(last) = body.last() {
                    out.push(last);
                }
            }
            _ => {}
        }
    }
    if let Some(last) = stmts.last() {
        out.push(last);
    }
    out
}

/// `true` if `s` is non-empty and every character is ASCII/Unicode whitespace
/// (phpstan's `#^(\s+)$#`).
fn is_all_whitespace(s: &str) -> bool {
    !s.is_empty() && s.chars().all(|c| c.is_whitespace())
}

pub(crate) static RULES: &[RuleEntry] = &[RuleEntry {
    name: "whitespace.file",
    level: 0,
    run: run_file_whitespace,
}];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- BOM ------------------------------------------------------------------

    #[test]
    fn bom_is_flagged() {
        // A leading UTF-8 BOM before the open tag.
        let src = "\u{feff}<?php\n\necho 'test';\n";
        assert_eq!(codes(src, run_file_whitespace), ["whitespace.bom"]);
    }

    #[test]
    fn no_bom_is_ok() {
        let src = "<?php\n\necho 'test';\n";
        assert!(codes(src, run_file_whitespace).is_empty());
    }

    // --- trailing whitespace --------------------------------------------------

    #[test]
    fn trailing_whitespace_after_close_tag_is_flagged() {
        // `?>` then a blank line: the close tag absorbs one newline, the rest is
        // pure-whitespace inline HTML.
        let src = "<?php\n\necho 'foo';\n\n?>\n\n";
        assert_eq!(codes(src, run_file_whitespace), ["whitespace.fileEnd"]);
    }

    #[test]
    fn trailing_whitespace_in_namespace_is_flagged() {
        let src = "<?php declare(strict_types = 1);\n\nnamespace Test;\n\necho 'foo';\n\n?>\n\n";
        assert_eq!(codes(src, run_file_whitespace), ["whitespace.fileEnd"]);
    }

    #[test]
    fn correct_file_is_ok() {
        let src = "<?php\n\nnamespace Test;\n\necho 'foo';\n";
        assert!(codes(src, run_file_whitespace).is_empty());
    }

    #[test]
    fn non_whitespace_html_after_close_is_ok() {
        // Real HTML after `?>` is intentional output, not trailing whitespace.
        let src = "<?php\n\necho 'test';\n\n?>\n\n<html><head>\n";
        assert!(codes(src, run_file_whitespace).is_empty());
    }

    #[test]
    fn no_close_tag_is_ok() {
        let src = "<?php\n\necho 'foo';\n";
        assert!(codes(src, run_file_whitespace).is_empty());
    }

    #[test]
    fn bom_and_trailing_both_flagged() {
        let src = "\u{feff}<?php\n\necho 'foo';\n\n?>\n\n";
        let mut got = codes(src, run_file_whitespace);
        got.sort_unstable();
        assert_eq!(got, ["whitespace.bom", "whitespace.fileEnd"]);
    }
}
