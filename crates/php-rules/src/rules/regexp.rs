//! phpstan category **Regexp** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Regexp/` — 2 rule(s) at level(s) 0,5.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented here:
//! - `regexp.pattern` (`RegularExpressionPatternRule`, level 0) — a `preg_*`
//!   call whose FIRST argument folds to a constant string that is a
//!   *syntactically broken* PCRE pattern. phpstan compiles the pattern with
//!   PCRE; we have no PCRE, so this is a deliberately CONSERVATIVE structural
//!   check that only fires for patterns that cannot possibly be valid (empty
//!   pattern, an invalid delimiter character, a missing/mismatched closing
//!   delimiter, or a non-letter trailing the closing delimiter where a modifier
//!   is expected). When in any doubt the pattern is left alone — zero false
//!   positives is the contract here.
//!
//! Deferred:
//! - `RegularExpressionQuotingRule` (`argument.invalidPregQuote`, level 5) —
//!   flags `preg_quote($x)` (no 2nd delimiter arg) interpolated into a pattern
//!   built by string concatenation. Faithfully replicating it requires
//!   `RegexExpressionHelper::getPatternDelimiters` (resolve the delimiter from a
//!   `Concat` whose leftmost constant piece is the pattern opener) plus
//!   `removeDefaultEscapedDelimiters` and argument normalization. Our AST models
//!   concatenation, but deciding "this `preg_quote` result lands inside a pattern
//!   with delimiter D" from a folded/partial concat is subtle and easy to get
//!   wrong (false positives when the concat is not actually a pattern, or when
//!   the delimiter is one preg_quote escapes by default). DEFERRED to stay
//!   FP-safe — needs the delimiter-from-concat helper before it can be done
//!   without over-reporting.

#![allow(unused_imports)]
use crate::{FileAnalysis, RuleEntry};
use php_ast::{Expr, ExprKind};
use php_diagnostics::Diagnostic;
use php_infer::{eval_const, ConstVal};
use php_resolve::{Resolution, ResolvedRef};
use std::collections::HashMap;

pub(crate) static RULES: &[RuleEntry] = &[RuleEntry {
    name: "regexp.pattern",
    level: 0,
    run: run_pattern,
}];

/// Build a span→resolution map for function references (callee names).
fn function_refs(refs: &[ResolvedRef]) -> HashMap<(u32, u32), &ResolvedRef> {
    refs.iter()
        .filter(|r| r.kind == php_resolve::RefKind::Function)
        .map(|r| ((r.span.start, r.span.end), r))
        .collect()
}

/// The resolved reference for a call's callee, if it is a plain name.
fn resolved_callee<'a>(
    callee: &Expr,
    fmap: &HashMap<(u32, u32), &'a ResolvedRef>,
) -> Option<&'a ResolvedRef> {
    if let ExprKind::Name(n) = &callee.kind {
        return fmap.get(&(n.span.start, n.span.end)).copied();
    }
    None
}

/// The unqualified, lowercased global tail of a resolved function name, used to
/// match built-ins like `preg_match`. Returns the global candidate's last
/// segment (the global fallback for an unqualified call).
fn global_tail_lower(r: &ResolvedRef) -> Option<String> {
    let candidate = match &r.resolution {
        Resolution::Fqn(fqn) => fqn.as_str(),
        Resolution::Fallback { global, .. } => global.as_str(),
        _ => return None,
    };
    let tail = candidate.rsplit('\\').next().unwrap_or(candidate);
    Some(tail.to_ascii_lowercase())
}

/// Is this resolved call the *global* `preg_*` built-in (not a namespaced user
/// function that merely happens to share the tail)? The global preg_* functions
/// live in the root namespace, so the resolution must be (or fall back to) a
/// bare `preg_*` name — AND no namespaced user function may shadow it (an
/// unqualified call inside `namespace App` would bind to `App\preg_*` if one is
/// declared). Rejecting that case keeps us false-positive-free.
fn is_global_preg(fa: &FileAnalysis, r: &ResolvedRef, tail: &str) -> bool {
    match &r.resolution {
        Resolution::Fallback { namespaced, global } => {
            // A namespaced override wins over the global fallback.
            if fa.project.has_function(namespaced) {
                return false;
            }
            global.eq_ignore_ascii_case(tail)
        }
        // A fully-qualified `\preg_match(...)` resolves straight to the bare name.
        Resolution::Fqn(fqn) => fqn.eq_ignore_ascii_case(tail),
        _ => false,
    }
}

/// `RegularExpressionPatternRule` (`regexp.pattern`). A `preg_*` call whose first
/// argument folds to a constant string that is a structurally-invalid PCRE
/// pattern.
fn run_pattern(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else { return };
        let Some(r) = resolved_callee(callee, &fmap) else { return };
        let Some(tail) = global_tail_lower(r) else { return };
        // Every preg_* function takes the pattern as the first argument. Match
        // any `preg_`-prefixed global function (phpstan does the same), but only
        // the ones whose first arg is the pattern string. `preg_quote` /
        // `preg_last_error*` do NOT take a pattern first — exclude them.
        if !tail.starts_with("preg_") {
            return;
        }
        if matches!(
            tail.as_str(),
            "preg_quote" | "preg_last_error" | "preg_last_error_msg"
        ) {
            return;
        }
        if !is_global_preg(fa, r, &tail) {
            return;
        }
        // First positional argument (skip spread/named/first-class-callable forms
        // where the pattern position is indeterminate).
        let Some(arg0) = args.first() else { return };
        if arg0.spread || arg0.placeholder || arg0.name.is_some() {
            return;
        }
        // Fold the pattern to a constant string. Only a constant string can be
        // validated; anything dynamic is left alone.
        let Some(ConstVal::Str(bytes)) = eval_const(&arg0.value) else { return };
        if let Some(msg) = invalid_pattern_reason(&bytes) {
            out.push(
                Diagnostic::error(arg0.value.span, format!("Regex pattern is invalid: {msg}"))
                    .with_code("regexp.pattern"),
            );
        }
    });
    out
}

/// Conservatively decide whether `pattern` is a structurally-broken PCRE pattern,
/// returning a short reason if so (and `None` when it is plausibly valid).
///
/// PCRE pattern syntax (what `Strings::match`/`preg_*` require):
/// `<delim> ... <delim> <modifiers>` where `<delim>` is a single non-alphanumeric,
/// non-backslash, non-whitespace byte; bracket-style delimiters `()`, `{}`, `[]`,
/// `<>` use the matching closer. After the closing delimiter only modifier
/// letters may follow. We only return `Some` for cases that **cannot** be valid;
/// when unsure we return `None`.
fn invalid_pattern_reason(pattern: &[u8]) -> Option<String> {
    // Empty pattern → PCRE: "Empty regular expression".
    if pattern.is_empty() {
        return Some("Empty regular expression".to_string());
    }
    let delim = pattern[0];
    // A valid delimiter is any non-alphanumeric, non-backslash byte that is not
    // whitespace. (PCRE additionally forbids the NUL byte.) Backslash is never a
    // valid delimiter.
    if delim.is_ascii_alphanumeric() || delim == b'\\' || delim.is_ascii_whitespace() || delim == 0
    {
        return Some("Delimiter must not be alphanumeric, backslash, or whitespace".to_string());
    }

    // The closing delimiter: bracket-style delimiters pair, all others are the
    // same character.
    let close = match delim {
        b'(' => b')',
        b'{' => b'}',
        b'[' => b']',
        b'<' => b'>',
        other => other,
    };
    let bracketed = close != delim;

    // Find the closing delimiter. A `\` escapes the next byte (so an escaped
    // delimiter does not close the pattern). For bracket delimiters PCRE tracks
    // nesting of the opener/closer; we mirror that.
    let body = &pattern[1..];
    let mut i = 0;
    let mut depth = 1usize; // we are inside one level (the opening delimiter)
    let mut found_end: Option<usize> = None;
    while i < body.len() {
        let b = body[i];
        if b == b'\\' {
            // Escapes the next byte (if any). A trailing backslash escapes
            // nothing and is left for PCRE — but it cannot be the closer.
            i += 2;
            continue;
        }
        if bracketed {
            if b == delim {
                depth += 1;
            } else if b == close {
                depth -= 1;
                if depth == 0 {
                    found_end = Some(i);
                    break;
                }
            }
        } else if b == close {
            found_end = Some(i);
            break;
        }
        i += 1;
    }

    let Some(end) = found_end else {
        // No closing delimiter at all → cannot be valid.
        return Some(format!("No ending delimiter '{}' found", close as char));
    };

    // Everything after the closing delimiter must be modifier letters. PCRE's
    // valid modifiers: i m s x e A D S U X J u n (plus a couple of edge ones).
    // We accept any ASCII letter as a modifier position (and stop at FP risk:
    // if a non-letter, non-end byte appears, it's an "unknown modifier"). To stay
    // strictly FP-safe we only flag a *clearly* invalid trailing byte: a
    // non-alphabetic, non-NUL byte after the closing delimiter.
    let modifiers = &body[end + 1..];
    for &m in modifiers {
        if !m.is_ascii_alphabetic() {
            return Some(format!("Unknown modifier '{}'", m as char));
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{codes, run};

    #[test]
    fn invalid_unmatched_group_is_not_structurally_flagged() {
        // `(` is unbalanced inside the pattern, but the pattern is structurally
        // a valid `/ ... /` form — PCRE would reject it, but we cannot prove that
        // without a real engine, so we DO NOT flag it (FP-safety).
        assert!(codes("<?php preg_match('/(/', $s);", run_pattern).is_empty());
    }

    #[test]
    fn empty_pattern_flagged() {
        let c = codes("<?php preg_match('', $s);", run_pattern);
        assert_eq!(c, vec!["regexp.pattern"]);
    }

    #[test]
    fn missing_closing_delimiter_flagged() {
        // Opens with `/` but never closes.
        let c = codes(r#"<?php preg_match('/abc', $s);"#, run_pattern);
        assert_eq!(c, vec!["regexp.pattern"]);
    }

    #[test]
    fn alphanumeric_delimiter_flagged() {
        // `a` is not a legal delimiter.
        let c = codes(r#"<?php preg_match('aabca', $s);"#, run_pattern);
        assert_eq!(c, vec!["regexp.pattern"]);
    }

    #[test]
    fn backslash_delimiter_flagged() {
        let c = codes(r#"<?php preg_match('\\abc\\', $s);"#, run_pattern);
        assert_eq!(c, vec!["regexp.pattern"]);
    }

    #[test]
    fn invalid_trailing_modifier_flagged() {
        // Closing `/` then `5` — `5` is not a modifier letter.
        let c = codes(r#"<?php preg_match('/abc/5', $s);"#, run_pattern);
        assert_eq!(c, vec!["regexp.pattern"]);
    }

    #[test]
    fn valid_pattern_not_flagged() {
        assert!(codes(r#"<?php preg_match('/\d+/', $s);"#, run_pattern).is_empty());
    }

    #[test]
    fn valid_pattern_with_modifiers_not_flagged() {
        assert!(codes(r#"<?php preg_match('/foo.*bar/is', $s);"#, run_pattern).is_empty());
    }

    #[test]
    fn valid_hash_delimiter_not_flagged() {
        assert!(codes(r##"<?php preg_match('#^https?://#i', $url);"##, run_pattern).is_empty());
    }

    #[test]
    fn valid_bracket_delimiter_not_flagged() {
        // `{ ... }` bracket delimiters with nested braces (a quantifier `{1,3}`).
        assert!(codes(r#"<?php preg_match('{a{1,3}}', $s);"#, run_pattern).is_empty());
    }

    #[test]
    fn escaped_delimiter_inside_not_a_false_close() {
        // The `\/` is escaped, so the real close is the final `/`.
        assert!(codes(r#"<?php preg_match('/a\/b/', $s);"#, run_pattern).is_empty());
    }

    #[test]
    fn non_constant_pattern_not_flagged() {
        // Dynamic pattern — nothing to validate.
        assert!(codes("<?php preg_match($pat, $s);", run_pattern).is_empty());
    }

    #[test]
    fn preg_quote_not_treated_as_pattern() {
        // preg_quote's first arg is text to quote, NOT a pattern.
        assert!(codes(r#"<?php preg_quote('abc');"#, run_pattern).is_empty());
    }

    #[test]
    fn non_preg_function_ignored() {
        assert!(codes(r#"<?php str_replace('', 'x', $s);"#, run_pattern).is_empty());
    }

    #[test]
    fn preg_replace_pattern_flagged() {
        // preg_replace also takes the pattern first.
        let c = codes(r#"<?php preg_replace('aabca', 'x', $s);"#, run_pattern);
        assert_eq!(c, vec!["regexp.pattern"]);
    }

    #[test]
    fn namespaced_user_preg_match_not_flagged() {
        // A namespaced call that does NOT fall back to the global builtin is a
        // user function — never validate it as a regex.
        let src = r#"<?php namespace App; function preg_match($p){} preg_match('aaa');"#;
        // This resolves to App\preg_match (a user fn). It must not be flagged.
        assert!(codes(src, run_pattern).is_empty());
    }
}
