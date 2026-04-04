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
//! Implemented (type-based — use `fa.type_of` + the conservative classifiers
//! below; flag only when the inferred type is *concrete and certainly*
//! incompatible, never on `mixed`/unknown/objects-of-unindexed-classes/unions
//! that contain a compatible member):
//! - `foreach.nonIterable` (`IterableInForeachRule`, level 3) — `foreach` over a
//!   value that is definitely not iterable (a scalar/null, or an object of a
//!   fully-known class that does not implement `Traversable`).
//! - `arrayUnpacking.nonIterable` (`UnpackIterableInArrayRule`, level 3) — a
//!   spread element `[...$x]` whose operand is definitely not iterable.
//! - `offsetAccess.nonArray` (`ArrayDestructuringRule`, level 3) — array
//!   destructuring `[$a, $b] = $x` / `list(...) = $x` where `$x` is definitely
//!   neither an array nor `ArrayAccess`.
//! - `array.invalidKey` (`InvalidKeyInArrayItemRule`, level 3) — an array-literal
//!   key whose type can never be a valid array key (array/object/resource).
//! - `offsetAccess.invalidOffset` (`InvalidKeyInArrayDimFetchRule`, level 3) — an
//!   array dim-fetch `$arr[$k]` on a definite array with a key whose type can
//!   never be a valid array key.
//!
//! Deferred (need richer type modelling than we have):
//! - DEFERRED: `NonexistentOffsetInArrayDimFetchRule` / `…Check` — needs precise
//!   per-offset shape tracking (`hasOffsetValueType`) to know which offsets a
//!   value actually has; we model only `array<K,V>`, not constant-key shapes
//!   with definedness, so any check would either false-positive or do nothing.
//! - DEFERRED: `OffsetAccessAssignmentRule` / `OffsetAccessAssignOpRule` /
//!   `OffsetAccessValueAssignmentRule` — need `Type::setOffsetValueType` (whether
//!   a *specific* offset/value can be written into a type), which we don't model.
//! - DEFERRED: `ArrayUnpackingRule` (`arrayUnpacking.stringOffset`) — only fires
//!   when string keys in `[...]` unpacking are unsupported, i.e. PHP < 8.1; our
//!   target is 8.6, where it is always supported, so the rule never reports.
//! - DEFERRED: `DeadForeachRule` (`foreach.emptyArray`) — fires only on a value
//!   that is iterable but *never iterable at least once* (an empty-array type);
//!   we don't track non-emptiness, so we can't tell `array{}` from `array`.

use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{ArrayItem, Expr, ExprKind, StmtKind};
use php_diagnostics::Diagnostic;
use php_span::Span;
use php_types::Type;
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

// ---------------------------------------------------------------------------
// Conservative type classifiers for the type-driven Arrays rules.
//
// Cardinal rule: ZERO false positives. Every classifier returns `false`
// ("don't flag — could be ok") for anything we are not certain about: `mixed`,
// `Unknown`, templates/conditionals, `self`/`static`/`parent`, objects whose
// class we cannot fully resolve, and any union/nullable with one acceptable
// member. We flag only when the type is concrete and *certainly* incompatible.
// ---------------------------------------------------------------------------

/// Interfaces/classes that make an object iterable (`foreach`-able). Any class
/// reaching one of these — or any of their descendants — is iterable.
const TRAVERSABLE_FQNS: &[&str] = &["Traversable", "Iterator", "IteratorAggregate", "Generator"];

/// `true` iff every runtime value of `t` is definitely NOT iterable. Mirrors
/// phpstan's `$type->isIterable()->no()`. Arrays/iterables/lists/shapes ARE
/// iterable; scalars/null are not; an object is non-iterable only if its class
/// is *fully known* (so we'd see any `Traversable` ancestor) and reaches no
/// traversable interface. Conservative on everything else.
fn definitely_not_iterable(fa: &FileAnalysis, t: &Type) -> bool {
    match t {
        Type::Int
        | Type::Float
        | Type::String
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Null
        | Type::Resource
        | Type::LiteralInt(_)
        | Type::LiteralString(_) => true,
        Type::Named { fqn, .. } => {
            fa.class_fully_known(fqn)
                && !TRAVERSABLE_FQNS.iter().any(|tr| fa.reflection.is_subclass_of(fqn, tr))
        }
        // A union is non-iterable only when *every* member is.
        Type::Union(parts) => !parts.is_empty() && parts.iter().all(|p| definitely_not_iterable(fa, p)),
        // `?T` includes `null` (non-iterable) and `T`: non-iterable iff `T` is.
        Type::Nullable(inner) => definitely_not_iterable(fa, inner),
        // Arrays/iterables/lists/shapes are iterable; everything we are unsure
        // about (`mixed`, `object`, `self`, templates, callables, class-string,
        // unknown, …) is treated as possibly-iterable → not flagged.
        _ => false,
    }
}

/// `true` iff `t` is definitely neither an array nor (possibly) `ArrayAccess`,
/// i.e. array destructuring can never apply. Mirrors phpstan's
/// `!isArray()->yes() && !ObjectType(ArrayAccess)->isSuperTypeOf()->yes()`, but
/// conservatively: an object is rejected only when its class is fully known and
/// does not implement `ArrayAccess`.
fn definitely_not_array_destructurable(fa: &FileAnalysis, t: &Type) -> bool {
    match t {
        Type::Int
        | Type::Float
        | Type::String
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Null
        | Type::Resource
        | Type::LiteralInt(_)
        | Type::LiteralString(_) => true,
        Type::Named { fqn, .. } => {
            fa.class_fully_known(fqn) && !fa.reflection.is_subclass_of(fqn, "ArrayAccess")
        }
        Type::Union(parts) => {
            !parts.is_empty() && parts.iter().all(|p| definitely_not_array_destructurable(fa, p))
        }
        Type::Nullable(inner) => definitely_not_array_destructurable(fa, inner),
        _ => false,
    }
}

/// `true` iff `t` is definitely an array (so an offset access on it is an array
/// dim-fetch, not an object/string offset). Used to gate the invalid-key rule.
fn definitely_array(t: &Type) -> bool {
    match t {
        Type::Array(_) | Type::List(_) | Type::Shape { .. } => true,
        Type::Union(parts) => !parts.is_empty() && parts.iter().all(definitely_array),
        _ => false,
    }
}

/// `true` iff `t` can never be a legal PHP array key. Legal keys are
/// `int|string` (and PHP also coerces `bool|float|null` to int/"", so those are
/// NOT errors). Only array/object/resource (and unions wholly of those) are
/// definitely invalid. Conservative on `mixed`/unknown/scalars.
fn definitely_invalid_key(t: &Type) -> bool {
    match t {
        Type::Array(_) | Type::Iterable(_) | Type::List(_) | Type::Shape { .. } => true,
        Type::Object | Type::Named { .. } | Type::Resource => true,
        // Legal or coercible-to-legal keys.
        Type::Int
        | Type::Float
        | Type::String
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Null
        | Type::LiteralInt(_)
        | Type::LiteralString(_) => false,
        Type::Union(parts) => !parts.is_empty() && parts.iter().all(definitely_invalid_key),
        Type::Nullable(inner) => definitely_invalid_key(inner),
        _ => false,
    }
}

/// `IterableInForeachRule` (`foreach.nonIterable`, level 3): the subject of a
/// `foreach` must be iterable. We flag only when the subject's inferred type is
/// definitely non-iterable (see [`definitely_not_iterable`]).
fn run_iterable_in_foreach(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::Foreach { subject, .. } = &s.kind {
            let ty = fa.type_of(subject);
            if definitely_not_iterable(fa, &ty) {
                out.push(
                    Diagnostic::error(
                        subject.span,
                        format!(
                            "Argument of an invalid type {ty} supplied for foreach, only iterables are supported.",
                        ),
                    )
                    .with_code("foreach.nonIterable"),
                );
            }
        }
    });
    out
}

/// `UnpackIterableInArrayRule` (`arrayUnpacking.nonIterable`, level 3): a spread
/// element `[...$x]` requires `$x` to be iterable.
fn run_unpack_iterable_in_array(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Array { items, .. } = &e.kind else { return };
        for it in items {
            if !it.spread {
                continue;
            }
            let Some(value) = &it.value else { continue };
            let ty = fa.type_of(value);
            if definitely_not_iterable(fa, &ty) {
                out.push(
                    Diagnostic::error(
                        value.span,
                        format!("Only iterables can be unpacked, {ty} given."),
                    )
                    .with_code("arrayUnpacking.nonIterable"),
                );
            }
        }
    });
    out
}

/// `ArrayDestructuringRule` (`offsetAccess.nonArray`, level 3): the right side of
/// an array-destructuring assignment (`[$a, $b] = $x` or `list(...) = $x`) must
/// be an array or `ArrayAccess`.
fn run_array_destructuring(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Assign { target, rhs } = &e.kind else { return };
        // Only a list/array destructuring target triggers this rule.
        if !matches!(target.kind, ExprKind::Array { .. }) {
            return;
        }
        let ty = fa.type_of(rhs);
        if definitely_not_array_destructurable(fa, &ty) {
            out.push(
                Diagnostic::error(
                    rhs.span,
                    format!("Cannot use array destructuring on {ty}."),
                )
                .with_code("offsetAccess.nonArray"),
            );
        }
    });
    out
}

/// `InvalidKeyInArrayItemRule` (`array.invalidKey`, level 3): a key in an array
/// literal must be a valid array-key type (`int|string`, or a bool/float/null
/// PHP coerces). We flag only keys whose type is definitely invalid
/// (array/object/resource).
fn run_invalid_key_in_array_item(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Array { items, .. } = &e.kind else { return };
        for it in items {
            let Some(key) = &it.key else { continue };
            let ty = fa.type_of(key);
            if definitely_invalid_key(&ty) {
                out.push(
                    Diagnostic::error(key.span, format!("Invalid array key type {ty}."))
                        .with_code("array.invalidKey"),
                );
            }
        }
    });
    out
}

/// `InvalidKeyInArrayDimFetchRule` (`offsetAccess.invalidOffset`, level 3): an
/// array dim-fetch `$arr[$k]` (on a value we know is an array) must use a valid
/// array-key type. Gated on the base being *definitely* an array so we don't
/// misfire on string offsets (`$s[$i]`) or `ArrayAccess` objects.
fn run_invalid_key_in_dim_fetch(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Index { base, index: Some(dim) } = &e.kind else { return };
        if !definitely_array(&fa.type_of(base)) {
            return;
        }
        let ty = fa.type_of(dim);
        if definitely_invalid_key(&ty) {
            out.push(
                Diagnostic::error(dim.span, format!("Invalid array key type {ty}."))
                    .with_code("offsetAccess.invalidOffset"),
            );
        }
    });
    out
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "array.duplicateKey", level: 0, run: run_duplicate_keys },
    RuleEntry { name: "offsetAccess.noDim", level: 0, run: run_offset_access_no_dim },
    RuleEntry { name: "foreach.nonIterable", level: 3, run: run_iterable_in_foreach },
    RuleEntry { name: "arrayUnpacking.nonIterable", level: 3, run: run_unpack_iterable_in_array },
    RuleEntry { name: "offsetAccess.nonArray", level: 3, run: run_array_destructuring },
    RuleEntry { name: "array.invalidKey", level: 3, run: run_invalid_key_in_array_item },
    RuleEntry { name: "offsetAccess.invalidOffset", level: 3, run: run_invalid_key_in_dim_fetch },
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

    // --- foreach.nonIterable ---

    #[test]
    fn foreach_over_int_flagged() {
        assert_eq!(
            codes("<?php $n = 1; foreach ($n as $x) {}", run_iterable_in_foreach),
            ["foreach.nonIterable"]
        );
    }

    #[test]
    fn foreach_over_string_flagged() {
        assert_eq!(
            codes("<?php $s = 'hi'; foreach ($s as $x) {}", run_iterable_in_foreach),
            ["foreach.nonIterable"]
        );
    }

    #[test]
    fn foreach_over_array_ok() {
        assert!(codes("<?php $a = [1, 2]; foreach ($a as $x) {}", run_iterable_in_foreach).is_empty());
    }

    #[test]
    fn foreach_over_mixed_ok() {
        // Unknown/mixed subject: never flagged.
        assert!(codes("<?php foreach ($a as $x) {}", run_iterable_in_foreach).is_empty());
    }

    #[test]
    fn foreach_over_plain_object_flagged() {
        // A fully-known class with no Traversable ancestor is not iterable.
        let src = "<?php class Foo {} $o = new Foo(); foreach ($o as $x) {}";
        assert_eq!(codes(src, run_iterable_in_foreach), ["foreach.nonIterable"]);
    }

    #[test]
    fn foreach_over_traversable_object_ok() {
        let src = "<?php class Foo implements \\IteratorAggregate {} $o = new Foo(); foreach ($o as $x) {}";
        assert!(codes(src, run_iterable_in_foreach).is_empty());
    }

    // --- arrayUnpacking.nonIterable ---

    #[test]
    fn unpack_int_flagged() {
        assert_eq!(
            codes("<?php $n = 1; $a = [...$n];", run_unpack_iterable_in_array),
            ["arrayUnpacking.nonIterable"]
        );
    }

    #[test]
    fn unpack_array_ok() {
        assert!(codes("<?php $b = [1]; $a = [...$b];", run_unpack_iterable_in_array).is_empty());
    }

    #[test]
    fn unpack_unknown_ok() {
        assert!(codes("<?php $a = [...$b];", run_unpack_iterable_in_array).is_empty());
    }

    // --- offsetAccess.nonArray ---

    #[test]
    fn destructure_int_flagged() {
        assert_eq!(
            codes("<?php $n = 1; [$a, $b] = $n;", run_array_destructuring),
            ["offsetAccess.nonArray"]
        );
    }

    #[test]
    fn destructure_array_ok() {
        assert!(codes("<?php $p = [1, 2]; [$a, $b] = $p;", run_array_destructuring).is_empty());
    }

    #[test]
    fn destructure_unknown_ok() {
        assert!(codes("<?php [$a, $b] = $p;", run_array_destructuring).is_empty());
    }

    #[test]
    fn plain_assignment_not_flagged() {
        // A non-destructuring assignment is irrelevant.
        assert!(codes("<?php $n = 1; $a = $n;", run_array_destructuring).is_empty());
    }

    // --- array.invalidKey ---

    #[test]
    fn array_literal_array_key_flagged() {
        assert_eq!(
            codes("<?php $k = [1]; $a = [$k => 'v'];", run_invalid_key_in_array_item),
            ["array.invalidKey"]
        );
    }

    #[test]
    fn array_literal_int_key_ok() {
        assert!(codes("<?php $a = [1 => 'v', 'x' => 'y'];", run_invalid_key_in_array_item).is_empty());
    }

    #[test]
    fn array_literal_object_key_flagged() {
        let src = "<?php class Foo {} $k = new Foo(); $a = [$k => 'v'];";
        assert_eq!(codes(src, run_invalid_key_in_array_item), ["array.invalidKey"]);
    }

    #[test]
    fn array_literal_unknown_key_ok() {
        assert!(codes("<?php $a = [$k => 'v'];", run_invalid_key_in_array_item).is_empty());
    }

    // --- offsetAccess.invalidOffset ---

    #[test]
    fn dim_fetch_array_key_flagged() {
        assert_eq!(
            codes("<?php $arr = [1, 2]; $k = ['x']; $v = $arr[$k];", run_invalid_key_in_dim_fetch),
            ["offsetAccess.invalidOffset"]
        );
    }

    #[test]
    fn dim_fetch_int_key_ok() {
        assert!(codes("<?php $arr = [1, 2]; $v = $arr[0];", run_invalid_key_in_dim_fetch).is_empty());
    }

    #[test]
    fn dim_fetch_unknown_base_ok() {
        // Base type unknown → not gated as an array → not flagged.
        assert!(codes("<?php $k = [1]; $v = $arr[$k];", run_invalid_key_in_dim_fetch).is_empty());
    }
}
