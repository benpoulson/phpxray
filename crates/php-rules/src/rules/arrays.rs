//! phpstan category **Arrays** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Arrays/` — 15 rule(s), most at level 0–2.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to `RULES`
//! (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented (level 0, purely syntactic):
//! - `array.duplicateKey` (`DuplicateKeysInLiteralArraysRule`) — duplicate
//!   constant keys within one array literal. We only evaluate literal `Int` /
//!   `Str` keys (and the auto-incrementing index for keyless items), mirroring
//!   phpstan's constant-scalar handling and PHP's array-key coercion.
//! - `offsetAccess.noDim` (`OffsetAccessWithoutDimForReadingRule`) — `$a[]`
//!   used for *reading* (an `Index` with no dimension outside a write/assignment
//!   position).
//!
//! Deferred (need the type system — flagged here, not faked):
//! - `NonexistentOffsetInArrayDimFetchRule` / `…Check` — needs the value's type
//!   to know which offsets exist.
//! - `InvalidKeyInArrayDimFetchRule` / `InvalidKeyInArrayItemRule` /
//!   `AllowedArrayKeysTypes` — need the *type* of the key expression.
//! - `OffsetAccessAssignmentRule` / `OffsetAccessAssignOpRule` /
//!   `OffsetAccessValueAssignmentRule` — need the offset/value types.
//! - `IterableInForeachRule` / `DeadForeachRule` — need the iterated type.
//! - `ArrayUnpackingRule` / `UnpackIterableInArrayRule` — need the spread
//!   operand's type (string-keyed pre-8.1, non-iterable, …).
//! - `ArrayDestructuringRule` — needs the assigned-value type.

use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{ArrayItem, Expr, ExprKind, StmtKind};
use php_diagnostics::Diagnostic;
use php_span::Span;
use std::collections::HashSet;

/// A constant array-key value, after PHP's array-key coercion. Booleans/floats
/// coerce to int and null to "" in PHP, but those can't appear as *literal*
/// `Int`/`Str` keys here, so we only model the two cases we can evaluate.
#[derive(Clone, PartialEq, Eq, Hash)]
enum KeyVal {
    Int(i64),
    Str(Vec<u8>),
}

/// Coerce a constant key value the way PHP coerces array keys: a string that is
/// the canonical decimal form of an integer becomes that integer.
fn coerce_string_key(bytes: &[u8]) -> KeyVal {
    if let Some(n) = canonical_int_string(bytes) {
        KeyVal::Int(n)
    } else {
        KeyVal::Str(bytes.to_vec())
    }
}

/// `Some(n)` iff `bytes` is the canonical base-10 representation of `n` (so PHP
/// would coerce it to an int array key). Rejects leading zeros (`"01"`), a
/// leading `+`, whitespace, and `"-0"`.
fn canonical_int_string(bytes: &[u8]) -> Option<i64> {
    if bytes.is_empty() {
        return None;
    }
    let (neg, digits): (bool, &[u8]) = match bytes.first() {
        Some(b'-') => (true, &bytes[1..]),
        _ => (false, bytes),
    };
    if digits.is_empty() || !digits.iter().all(|b| b.is_ascii_digit()) {
        return None;
    }
    // No leading zeros, except the single literal "0".
    if digits.len() > 1 && digits[0] == b'0' {
        return None;
    }
    let s = std::str::from_utf8(bytes).ok()?;
    let n: i64 = s.parse().ok()?;
    // "-0" parses to 0 but is not canonical.
    if neg && n == 0 {
        return None;
    }
    Some(n)
}

/// The constant key value for a literal key expression, or `None` if it isn't a
/// constant `Int`/`Str` we can evaluate.
fn const_key(e: &Expr) -> Option<KeyVal> {
    match &e.kind {
        ExprKind::Int(n) => Some(KeyVal::Int(*n)),
        ExprKind::Str(bytes) => Some(coerce_string_key(bytes)),
        _ => None,
    }
}

/// `var_export`-style rendering of a resolved key value (the `%s` value field in
/// phpstan's message): ints bare, strings single-quoted with `'`/`\` escaped.
fn export_key(k: &KeyVal) -> String {
    match k {
        KeyVal::Int(n) => n.to_string(),
        KeyVal::Str(bytes) => {
            let mut out = String::from("'");
            for &b in bytes {
                match b {
                    b'\'' => out.push_str("\\'"),
                    b'\\' => out.push_str("\\\\"),
                    _ => out.push(b as char),
                }
            }
            out.push('\'');
            out
        }
    }
}

/// `DuplicateKeysInLiteralArraysRule` (`array.duplicateKey`, level 0): within a
/// single array literal, report constant keys that appear more than once.
fn run_duplicate_keys(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        if let ExprKind::Array { items, .. } = &e.kind {
            out.extend(duplicate_keys_in_one_array(items, fa.source, e.span));
        }
    });
    out
}

fn duplicate_keys_in_one_array(items: &[ArrayItem], source: &str, array_span: Span) -> Vec<Diagnostic> {
    // For each resolved key value: the printed key expressions (in order) and
    // the span to report at (the first occurrence).
    let mut printed: Vec<(KeyVal, Vec<String>, Span)> = Vec::new();
    // The auto-increment index high-water mark. `None` until the first integer
    // (explicit or implicit) is seen; `auto_broken` once a non-constant/spread
    // item makes the next implicit index unpredictable.
    let mut auto_index: Option<i64> = None;
    let mut auto_broken = false;

    let record = |kv: KeyVal, label: String, span: Span, printed: &mut Vec<(KeyVal, Vec<String>, Span)>| {
        if let Some(entry) = printed.iter_mut().find(|(k, _, _)| *k == kv) {
            entry.1.push(label);
        } else {
            printed.push((kv, vec![label], span));
        }
    };

    for it in items {
        // A spread (`...$x`) contributes unknown keys.
        if it.spread {
            auto_broken = true;
            continue;
        }
        match &it.key {
            None => {
                // Keyless item: takes the next auto-incremented integer index.
                if auto_broken {
                    continue;
                }
                let idx = match auto_index {
                    None => 0,
                    Some(prev) => prev + 1,
                };
                auto_index = Some(idx);
                record(KeyVal::Int(idx), idx.to_string(), it.span, &mut printed);
            }
            Some(key_expr) => {
                let Some(kv) = const_key(key_expr) else {
                    // Non-constant key — if it were an int it would advance the
                    // auto index, so stop predicting implicit indices.
                    auto_broken = true;
                    continue;
                };
                // An integer key advances the auto-index high-water mark.
                if let KeyVal::Int(n) = kv {
                    auto_index = Some(match auto_index {
                        None => n,
                        Some(prev) => prev.max(n),
                    });
                }
                let label = key_expr.span.text(source).to_string();
                record(kv, label, it.span, &mut printed);
            }
        }
    }

    let mut out = Vec::new();
    for (kv, labels, span) in printed {
        if labels.len() < 2 {
            continue;
        }
        let report_span = if span.is_empty() { array_span } else { span };
        // count >= 2 here, so the plural "duplicate keys" always applies, but
        // keep phpstan's exact branch for fidelity.
        let noun = if labels.len() == 1 { "duplicate key" } else { "duplicate keys" };
        let msg = format!(
            "Array has {} {} with value {} ({}).",
            labels.len(),
            noun,
            export_key(&kv),
            labels.join(", "),
        );
        out.push(Diagnostic::error(report_span, msg).with_code("array.duplicateKey"));
    }
    out
}

/// `OffsetAccessWithoutDimForReadingRule` (`offsetAccess.noDim`, level 0): `$a[]`
/// (an `Index` with no dimension) is only valid as a write target. Anywhere it
/// is read, report it.
fn run_offset_access_no_dim(fa: &FileAnalysis) -> Vec<Diagnostic> {
    // Collect the spans of every `Index{ index: None }` that sits in a write
    // (assignment) position — those are the allowed `$a[] = …` appends.
    let mut allowed: HashSet<(u32, u32)> = HashSet::new();

    walk::for_each_expr(fa.program, &mut |e| match &e.kind {
        ExprKind::Assign { target, .. }
        | ExprKind::AssignRef { target, .. }
        | ExprKind::AssignOp { target, .. } => {
            mark_write_targets(target, &mut allowed);
        }
        _ => {}
    });
    // `foreach (... as $a[])` — the value (and key) are write targets.
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::Foreach { key, value, .. } = &s.kind {
            if let Some(k) = key {
                mark_write_targets(k, &mut allowed);
            }
            mark_write_targets(value, &mut allowed);
        }
    });

    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        if let ExprKind::Index { index: None, .. } = &e.kind {
            let r = e.span.range();
            if !allowed.contains(&(r.start as u32, r.end as u32)) {
                out.push(Diagnostic::error(e.span, "Cannot use [] for reading.").with_code("offsetAccess.noDim"));
            }
        }
    });
    out
}

/// Mark `$a[]` nodes that appear as write targets (assignment LHS, foreach value,
/// or nested inside an array/list destructuring target). PHP allows `[]` append
/// in any of these positions.
fn mark_write_targets(target: &Expr, allowed: &mut HashSet<(u32, u32)>) {
    match &target.kind {
        // An `Index` in write position — `$a[]`, `$a[k]`, or a nested chain like
        // `$a[][]`. If this level is a bare append, allow it; either way descend
        // through the base so inner appends (e.g. the inner `$a[]` of `$a[][]`)
        // are allowed too.
        ExprKind::Index { base, index } => {
            if index.is_none() {
                let r = target.span.range();
                allowed.insert((r.start as u32, r.end as u32));
            }
            mark_write_targets(base, allowed);
        }
        // List/array destructuring target: each element value is a write target.
        ExprKind::Array { items, .. } => {
            for it in items {
                if let Some(v) = &it.value {
                    mark_write_targets(v, allowed);
                }
            }
        }
        _ => {}
    }
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "array.duplicateKey", level: 0, run: run_duplicate_keys },
    RuleEntry { name: "offsetAccess.noDim", level: 0, run: run_offset_access_no_dim },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- array.duplicateKey ---

    #[test]
    fn duplicate_int_keys_flagged() {
        assert_eq!(codes("<?php $a = [1 => 'a', 1 => 'b'];", run_duplicate_keys), ["array.duplicateKey"]);
    }

    #[test]
    fn duplicate_string_keys_flagged() {
        assert_eq!(codes("<?php $a = ['x' => 1, 'x' => 2];", run_duplicate_keys), ["array.duplicateKey"]);
    }

    #[test]
    fn distinct_keys_ok() {
        assert!(codes("<?php $a = [1 => 'a', 2 => 'b', 'x' => 1];", run_duplicate_keys).is_empty());
    }

    #[test]
    fn keyless_then_explicit_same_index_is_duplicate() {
        // `'a'` is index 0, then `0 => 'b'` collides.
        assert_eq!(codes("<?php $a = ['a', 0 => 'b'];", run_duplicate_keys), ["array.duplicateKey"]);
    }

    #[test]
    fn explicit_index_then_keyless_advances() {
        // `5 => 'a'` then keyless `'b'` becomes index 6 — no collision.
        assert!(codes("<?php $a = [5 => 'a', 'b'];", run_duplicate_keys).is_empty());
    }

    #[test]
    fn numeric_string_key_coerces_to_int() {
        // "0" coerces to int 0, colliding with int 0.
        assert_eq!(codes("<?php $a = ['0' => 1, 0 => 2];", run_duplicate_keys), ["array.duplicateKey"]);
    }

    #[test]
    fn non_canonical_numeric_string_stays_string() {
        // "01" is NOT coerced (leading zero), so no collision with int 1.
        assert!(codes("<?php $a = ['01' => 1, 1 => 2];", run_duplicate_keys).is_empty());
    }

    #[test]
    fn non_constant_keys_skipped() {
        assert!(codes("<?php $a = [$x => 1, $y => 2, foo() => 3];", run_duplicate_keys).is_empty());
    }

    #[test]
    fn duplicate_in_nested_array_flagged() {
        let src = "<?php $a = [[1 => 'a', 1 => 'b']];";
        assert_eq!(codes(src, run_duplicate_keys), ["array.duplicateKey"]);
    }

    #[test]
    fn triple_duplicate_counts_one_diagnostic() {
        // Three occurrences of key 1 → one diagnostic for that key.
        assert_eq!(codes("<?php $a = [1 => 'a', 1 => 'b', 1 => 'c'];", run_duplicate_keys), ["array.duplicateKey"]);
    }

    #[test]
    fn spread_breaks_auto_index_no_false_positive() {
        // After a spread the auto index is unknown; we don't invent collisions.
        assert!(codes("<?php $a = [...$b, 'c'];", run_duplicate_keys).is_empty());
    }

    // --- offsetAccess.noDim ---

    #[test]
    fn append_assignment_is_allowed() {
        assert!(codes("<?php $a[] = 1;", run_offset_access_no_dim).is_empty());
    }

    #[test]
    fn read_with_empty_dim_is_flagged() {
        assert_eq!(codes("<?php $x = $a[];", run_offset_access_no_dim), ["offsetAccess.noDim"]);
    }

    #[test]
    fn append_in_argument_read_is_flagged() {
        assert_eq!(codes("<?php foo($a[]);", run_offset_access_no_dim), ["offsetAccess.noDim"]);
    }

    #[test]
    fn dimmed_read_is_ok() {
        assert!(codes("<?php $x = $a[0]; $y = $a['k'];", run_offset_access_no_dim).is_empty());
    }

    #[test]
    fn append_via_assign_ref_is_allowed() {
        assert!(codes("<?php $a[] =& $b;", run_offset_access_no_dim).is_empty());
    }

    #[test]
    fn nested_append_chain_is_allowed() {
        // `$a[][]` on the LHS: both the outer and inner appends are write targets.
        assert!(codes("<?php $a[][] = 1;", run_offset_access_no_dim).is_empty());
    }

    #[test]
    fn foreach_value_append_is_allowed() {
        assert!(codes("<?php foreach ($xs as $a[]) {}", run_offset_access_no_dim).is_empty());
    }

    #[test]
    fn destructuring_append_is_allowed() {
        assert!(codes("<?php [$a[], $b[]] = $pair;", run_offset_access_no_dim).is_empty());
    }

    #[test]
    fn no_offset_access_no_diagnostics() {
        assert!(codes("<?php $a = 1 + 2; echo $a;", run_offset_access_no_dim).is_empty());
    }
}
