//! phpstan category **Regexp** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Regexp/` — 2 rule(s) at level(s) 0,5.
//! The rule set's coverage truth is `cargo run -p xtask -- rule-manifest`; for phpstan's behaviour read `phpstan-src/src/Rules/` directly. Add each rule as a `RuleEntry` to
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
//! - `argument.invalidPregQuote` (`RegularExpressionQuotingRule`, level 5) —
//!   flags `preg_quote()` calls inside a concatenated regex pattern when the
//!   quote delimiter is missing or contradicts the pattern delimiter.

use crate::members;
use crate::{facts::CallFact, FactKind, FactRuleEntry, FactRuleHandler, FileAnalysis, RuleEntry};
use php_ast::{Arg, BinOp, Expr, ExprKind};
use php_diagnostics::Diagnostic;
use php_infer::{eval_const, ConstVal};
use php_resolve::{Resolution, ResolvedRef};
use php_types::Type;
use std::collections::HashMap;

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "regexp.pattern",
        level: 0,
        run: run_pattern,
    },
    RuleEntry {
        name: "argument.invalidPregQuote",
        level: 5,
        run: run_quoting,
    },
];

pub(crate) static FACT_RULES: &[FactRuleEntry] = &[
    FactRuleEntry::new(
        "regexp.pattern",
        0,
        FactKind::FunctionCall,
        FactRuleHandler::FunctionCall(check_pattern_call),
    ),
    FactRuleEntry::new(
        "argument.invalidPregQuote",
        5,
        FactKind::FunctionCall,
        FactRuleHandler::FunctionCall(check_quoting_call),
    ),
];

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
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    for call in fa.facts.function_calls() {
        check_pattern_call_with_refs(fa, call, &fmap, &mut out);
    }
    out
}

fn check_pattern_call(fa: &FileAnalysis, call: &CallFact, out: &mut Vec<Diagnostic>) {
    let fmap = members::function_refs(fa.resolved_refs);
    check_pattern_call_with_refs(fa, call, &fmap, out);
}

fn check_pattern_call_with_refs(
    fa: &FileAnalysis,
    call: &CallFact,
    fmap: &HashMap<(u32, u32), &ResolvedRef>,
    out: &mut Vec<Diagnostic>,
) {
    let Some(r) = members::resolved_callee(call.callee, fmap) else {
        return;
    };
    let Some(tail) = global_tail_lower(r) else {
        return;
    };
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
    let Some(arg0) = call.args.first() else {
        return;
    };
    if arg0.spread || arg0.placeholder || arg0.name.is_some() {
        return;
    }
    // Fold the pattern to a constant string. Only a constant string can be
    // validated; anything dynamic is left alone.
    let Some(ConstVal::Str(bytes)) = eval_const(&arg0.value) else {
        return;
    };
    if let Some(msg) = invalid_pattern_reason(&bytes) {
        out.push(
            Diagnostic::error(arg0.value.span, format!("Regex pattern is invalid: {msg}"))
                .with_code("regexp.pattern"),
        );
    }
}

/// `RegularExpressionQuotingRule` (`argument.invalidPregQuote`). phpstan only
/// checks patterns built by concatenation; the delimiter is read from the
/// leftmost constant piece of the concat.
fn run_quoting(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    for call in fa.facts.function_calls() {
        check_quoting_call_with_refs(fa, call, &fmap, &mut out);
    }
    out
}

fn check_quoting_call(fa: &FileAnalysis, call: &CallFact, out: &mut Vec<Diagnostic>) {
    let fmap = members::function_refs(fa.resolved_refs);
    check_quoting_call_with_refs(fa, call, &fmap, out);
}

fn check_quoting_call_with_refs(
    fa: &FileAnalysis,
    call: &CallFact,
    fmap: &HashMap<(u32, u32), &ResolvedRef>,
    out: &mut Vec<Diagnostic>,
) {
    let Some(r) = members::resolved_callee(call.callee, fmap) else {
        return;
    };
    let Some(tail) = global_tail_lower(r) else {
        return;
    };
    if !is_regex_pattern_function(&tail) || !is_global_preg(fa, r, &tail) {
        return;
    }

    let Some(pattern) = pattern_arg(call.args, fa.interner, &tail) else {
        return;
    };
    if !is_concat(pattern) {
        return;
    }

    let mut pattern_delimiters = pattern_delimiters_from_concat(fa, pattern);
    pattern_delimiters = remove_default_escaped(pattern_delimiters);
    if pattern_delimiters.is_empty() {
        return;
    }

    validate_quote_delimiters(fa, fmap, pattern, &pattern_delimiters, out);
}

fn is_regex_pattern_function(tail: &str) -> bool {
    matches!(
        tail,
        "preg_match"
            | "preg_match_all"
            | "preg_filter"
            | "preg_grep"
            | "preg_replace"
            | "preg_replace_callback"
            | "preg_split"
    )
}

fn is_concat(e: &Expr) -> bool {
    matches!(
        e.kind,
        ExprKind::Binary {
            op: BinOp::Concat,
            ..
        }
    )
}

fn pattern_arg<'a>(
    args: &'a [Arg],
    interner: &php_intern::Interner,
    _tail: &str,
) -> Option<&'a Expr> {
    // PHP 8 named-arg spelling, e.g. preg_split(subject: $s, pattern: '...').
    for arg in args {
        if arg.spread || arg.placeholder {
            continue;
        }
        if let Some(name) = arg.name {
            if interner.resolve(name) == "pattern" {
                return Some(&arg.value);
            }
        }
    }

    let arg0 = args.first()?;
    if arg0.spread || arg0.placeholder || arg0.name.is_some() {
        return None;
    }
    Some(&arg0.value)
}

fn preg_quote_delimiter_arg<'a>(
    args: &'a [Arg],
    interner: &php_intern::Interner,
) -> Option<Option<&'a Expr>> {
    for arg in args {
        if arg.spread || arg.placeholder {
            return None;
        }
        if let Some(name) = arg.name {
            if interner.resolve(name) == "delimiter" {
                return Some(Some(&arg.value));
            }
        }
    }

    let positional = args.iter().filter(|a| a.name.is_none()).collect::<Vec<_>>();
    if positional.iter().any(|a| a.spread || a.placeholder) {
        return None;
    }
    Some(positional.get(1).map(|a| &a.value))
}

fn validate_quote_delimiters(
    fa: &FileAnalysis,
    fmap: &HashMap<(u32, u32), &ResolvedRef>,
    e: &Expr,
    pattern_delimiters: &[String],
    out: &mut Vec<Diagnostic>,
) {
    let ExprKind::Binary {
        op: BinOp::Concat,
        lhs,
        rhs,
    } = &e.kind
    else {
        return;
    };

    validate_quote_expr(fa, fmap, lhs, pattern_delimiters, out);
    validate_quote_expr(fa, fmap, rhs, pattern_delimiters, out);
}

fn validate_quote_expr(
    fa: &FileAnalysis,
    fmap: &HashMap<(u32, u32), &ResolvedRef>,
    e: &Expr,
    pattern_delimiters: &[String],
    out: &mut Vec<Diagnostic>,
) {
    if is_concat(e) {
        validate_quote_delimiters(fa, fmap, e, pattern_delimiters, out);
        return;
    }

    let ExprKind::Call { callee, args } = &e.kind else {
        return;
    };
    let Some(r) = members::resolved_callee(callee, fmap) else {
        return;
    };
    let Some(tail) = global_tail_lower(r) else {
        return;
    };
    if tail != "preg_quote" || !is_global_preg(fa, r, "preg_quote") {
        return;
    }

    let Some(delimiter_arg) = preg_quote_delimiter_arg(args, fa.interner) else {
        return;
    };
    match delimiter_arg {
        None => {
            let msg = if pattern_delimiters.len() == 1 {
                format!(
                    "Call to preg_quote() is missing delimiter {} to be effective.",
                    pattern_delimiters[0]
                )
            } else {
                "Call to preg_quote() is missing delimiter parameter to be effective.".to_string()
            };
            out.push(Diagnostic::error(e.span, msg).with_code("argument.invalidPregQuote"));
        }
        Some(delimiter) => {
            for quote_delimiter in remove_default_escaped(const_string_values(fa, delimiter)) {
                if pattern_delimiters.iter().any(|d| d == &quote_delimiter) {
                    continue;
                }
                let msg = if pattern_delimiters.len() == 1 {
                    format!(
                        "Call to preg_quote() uses invalid delimiter {} while pattern uses {}.",
                        quote_delimiter, pattern_delimiters[0]
                    )
                } else {
                    format!("Call to preg_quote() uses invalid delimiter {quote_delimiter}.")
                };
                out.push(Diagnostic::error(e.span, msg).with_code("argument.invalidPregQuote"));
                return;
            }
        }
    }
}

fn pattern_delimiters_from_concat(fa: &FileAnalysis, e: &Expr) -> Vec<String> {
    let left = leftmost_concat_piece(e);
    let mut out = Vec::new();
    for value in const_string_values(fa, left) {
        if let Some(delimiter) = pattern_delimiter(&value) {
            if valid_pattern_delimiter(&delimiter) && !out.contains(&delimiter) {
                out.push(delimiter);
            }
        }
    }
    out
}

fn leftmost_concat_piece(mut e: &Expr) -> &Expr {
    while let ExprKind::Binary {
        op: BinOp::Concat,
        lhs,
        ..
    } = &e.kind
    {
        e = lhs;
    }
    e
}

fn const_string_values(fa: &FileAnalysis, e: &Expr) -> Vec<String> {
    if let Some(ConstVal::Str(bytes)) = eval_const(e) {
        if let Ok(s) = String::from_utf8(bytes) {
            return vec![s];
        }
    }

    let mut out = Vec::new();
    collect_literal_strings(&fa.type_of(e), &mut out);
    out
}

fn collect_literal_strings(t: &Type, out: &mut Vec<String>) {
    match t {
        Type::LiteralString(s) => {
            if !out.iter().any(|seen| seen.as_str() == &**s) {
                out.push(s.to_string());
            }
        }
        Type::Union(parts) => {
            for p in parts.iter() {
                collect_literal_strings(p, out);
            }
        }
        Type::Nullable(inner) => collect_literal_strings(inner, out),
        _ => {}
    }
}

fn pattern_delimiter(regex: &str) -> Option<String> {
    let trimmed = regex.trim_start_matches(|c: char| c.is_ascii_whitespace() || c == '\0');
    let first = trimmed.chars().next()?;
    Some(first.to_string())
}

fn valid_pattern_delimiter(delimiter: &str) -> bool {
    let mut chars = delimiter.chars();
    let Some(c) = chars.next() else {
        return false;
    };
    if chars.next().is_some() {
        return false;
    }
    !(c.is_ascii_alphanumeric() || c == '\\' || c.is_ascii_whitespace() || c == '\0')
}

fn remove_default_escaped(delimiters: Vec<String>) -> Vec<String> {
    let mut out = Vec::new();
    for delimiter in delimiters {
        if is_default_escaped(&delimiter) {
            continue;
        }
        if !out.contains(&delimiter) {
            out.push(delimiter);
        }
    }
    out
}

fn is_default_escaped(delimiter: &str) -> bool {
    if delimiter.chars().count() != 1 {
        return false;
    }
    matches!(
        delimiter,
        "." | "\\"
            | "+"
            | "*"
            | "?"
            | "["
            | "^"
            | "]"
            | "$"
            | "("
            | ")"
            | "{"
            | "}"
            | "="
            | "!"
            | "<"
            | ">"
            | "|"
            | ":"
            | "-"
            | "#"
    )
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

    #[test]
    fn preg_quote_missing_delimiter_flagged() {
        let d = run(
            r#"<?php preg_match('&' . preg_quote('&oops') . 'pattern&', $s);"#,
            run_quoting,
        );
        assert_eq!(d.len(), 1);
        assert_eq!(d[0].code, Some("argument.invalidPregQuote"));
        assert_eq!(
            d[0].message,
            "Call to preg_quote() is missing delimiter & to be effective."
        );
    }

    #[test]
    fn preg_quote_wrong_delimiter_flagged() {
        let d = run(
            r#"<?php preg_match('&' . preg_quote('&oops', '/') . 'pattern&', $s);"#,
            run_quoting,
        );
        assert_eq!(d.len(), 1);
        assert_eq!(
            d[0].message,
            "Call to preg_quote() uses invalid delimiter / while pattern uses &."
        );
    }

    #[test]
    fn preg_quote_walks_nested_concat() {
        let c = codes(
            r#"<?php preg_match('&' . preg_quote('&oops', '/') . preg_quote('&oops') . preg_quote('&ok', '&') . 'pattern&', $s);"#,
            run_quoting,
        );
        assert_eq!(
            c,
            vec!["argument.invalidPregQuote", "argument.invalidPregQuote"]
        );
    }

    #[test]
    fn preg_quote_correct_delimiter_not_flagged() {
        assert!(codes(
            r#"<?php preg_match('&' . preg_quote('&oops', '&') . 'pattern&', $s);"#,
            run_quoting,
        )
        .is_empty());
    }

    #[test]
    fn preg_quote_default_escaped_pattern_delimiter_not_flagged() {
        assert!(codes(
            r#"<?php preg_match('{' . preg_quote('&oops') . 'pattern}', $s);"#,
            run_quoting,
        )
        .is_empty());
    }

    #[test]
    fn preg_quote_named_args_on_preg_split_are_checked() {
        let d = run(
            r#"<?php preg_split(subject: $s, pattern: '&' . preg_quote(delimiter: '/', str: '&oops') . 'pattern&');"#,
            run_quoting,
        );
        assert_eq!(d.len(), 1);
        assert_eq!(
            d[0].message,
            "Call to preg_quote() uses invalid delimiter / while pattern uses &."
        );
    }

    #[test]
    fn preg_quote_non_constant_delimiter_not_flagged() {
        assert!(codes(
            r#"<?php preg_match('&' . preg_quote('&oops', $delimiter) . 'pattern&', $s);"#,
            run_quoting,
        )
        .is_empty());
    }

    #[test]
    fn preg_quote_dynamic_pattern_prefix_not_flagged() {
        assert!(codes(
            r#"<?php preg_match($prefix . preg_quote('&oops') . 'pattern&', $s);"#,
            run_quoting,
        )
        .is_empty());
    }

    #[test]
    fn namespaced_user_preg_quote_not_flagged() {
        let src = r#"<?php namespace App; function preg_quote($s){} preg_match('&' . preg_quote('&oops') . 'pattern&', $s);"#;
        assert!(codes(src, run_quoting).is_empty());
    }
}
