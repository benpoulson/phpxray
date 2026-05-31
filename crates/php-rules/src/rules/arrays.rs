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
//! - `arrayUnpacking.stringOffset` (`ArrayUnpackingRule`, level 3) — for projects
//!   targeting PHP < 8.1, a spread element whose iterable key type is definitely
//!   or potentially string-keyed.
//! - `offsetAccess.notFound` (`NonexistentOffsetInArrayDimFetchRule`, level 3) —
//!   a literal-key read from a sealed shape where the offset is definitely absent.
//! - `offsetAssign.dimType` (`OffsetAccessAssignmentRule` /
//!   `OffsetAccessAssignOpRule`, level 3) — a narrow subset for writes to
//!   string offsets: append or a definitely non-int offset.
//! - `offsetAssign.valueType` (`OffsetAccessValueAssignmentRule`, level 3) — an
//!   explicit `ArrayAccess<TKey, TValue>` write whose value is definitely not
//!   accepted by `TValue`.
//! - `foreach.emptyArray` (`DeadForeachRule`, level 4) — `foreach` over a
//!   definitely empty literal/shape.
//!
//! Deferred (need richer type modelling than we have):
//! - DEFERRED: the general `OffsetAccessAssignmentRule` / `OffsetAccessAssignOpRule`
//!   / `OffsetAccessValueAssignmentRule` surface — needs `Type::setOffsetValueType`
//!   (whether a *specific* offset/value can be written into a type). The subsets
//!   here intentionally skip unions, maybe-empty arrays, and object-specific
//!   offset key contracts unless they are explicit in `ArrayAccess<_, _>`.

use crate::{facts::AssignmentKind, walk, FileAnalysis, RuleEntry};
use php_ast::{ArrayItem, Expr, ExprKind};
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
    if let Some(n) = php_infer::arrays::canonical_int_string(bytes) {
        KeyVal::Int(n)
    } else {
        KeyVal::Str(bytes.to_vec())
    }
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
    for array in fa.facts.arrays() {
        out.extend(duplicate_keys_in_one_array(
            array.items,
            fa.source,
            array.expr.span,
        ));
    }
    out
}

fn duplicate_keys_in_one_array(
    items: &[ArrayItem],
    source: &str,
    array_span: Span,
) -> Vec<Diagnostic> {
    // For each resolved key value: the printed key expressions (in order) and
    // the span to report at (the first occurrence).
    let mut printed: Vec<(KeyVal, Vec<String>, Span)> = Vec::new();
    // The auto-increment index high-water mark. `None` until the first integer
    // (explicit or implicit) is seen; `auto_broken` once a non-constant/spread
    // item makes the next implicit index unpredictable.
    let mut auto_index: Option<i64> = None;
    let mut auto_broken = false;

    let record =
        |kv: KeyVal, label: String, span: Span, printed: &mut Vec<(KeyVal, Vec<String>, Span)>| {
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
        let noun = if labels.len() == 1 {
            "duplicate key"
        } else {
            "duplicate keys"
        };
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

    for assign in fa.facts.assignments() {
        mark_write_targets(assign.target, &mut allowed);
    }
    // `foreach (... as $a[])` — the value (and key) are write targets.
    for foreach in fa.facts.foreaches() {
        if let Some(k) = foreach.key {
            mark_write_targets(k, &mut allowed);
        }
        mark_write_targets(foreach.value, &mut allowed);
    }

    let mut out = Vec::new();
    for index in fa.facts.indexes() {
        if index.index.is_none() && !allowed.contains(&span_key(index.expr.span)) {
            out.push(
                Diagnostic::error(index.expr.span, "Cannot use [] for reading.")
                    .with_code("offsetAccess.noDim"),
            );
        }
    }
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
                allowed.insert(span_key(target.span));
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

fn span_key(span: Span) -> (u32, u32) {
    let r = span.range();
    (r.start as u32, r.end as u32)
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
                && !TRAVERSABLE_FQNS
                    .iter()
                    .any(|tr| fa.reflection.is_subclass_of(fqn, tr))
        }
        // A union is non-iterable only when *every* member is.
        Type::Union(parts) => {
            !parts.is_empty() && parts.iter().all(|p| definitely_not_iterable(fa, p))
        }
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
            !parts.is_empty()
                && parts
                    .iter()
                    .all(|p| definitely_not_array_destructurable(fa, p))
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

fn definitely_string_offset_base(t: &Type) -> bool {
    matches!(
        t,
        Type::String | Type::LiteralString(_) | Type::ClassString(_)
    )
}

fn definitely_invalid_string_write_offset(dim: Option<&Type>) -> bool {
    let Some(dim) = dim else { return true };
    !matches!(
        dim,
        Type::Int
            | Type::LiteralInt(_)
            | Type::IntRange { .. }
            | Type::Mixed
            | Type::ExplicitMixed
            | Type::Never
            | Type::Unknown(_)
            | Type::TemplateVar(_)
            | Type::Union(_)
            | Type::Intersection(_)
            | Type::Nullable(_)
            | Type::Conditional { .. }
    )
}

fn definitely_offset_accessible(fa: &FileAnalysis, t: &Type) -> bool {
    match t {
        Type::Array(_) | Type::List(_) | Type::Shape { .. } => true,
        Type::String | Type::LiteralString(_) | Type::ClassString(_) => true,
        Type::Named { fqn, .. } => {
            fqn.trim_start_matches('\\')
                .eq_ignore_ascii_case("ArrayAccess")
                || (fa.class_fully_known(fqn) && fa.reflection.is_subclass_of(fqn, "ArrayAccess"))
        }
        Type::Union(parts) => {
            !parts.is_empty() && parts.iter().all(|p| definitely_offset_accessible(fa, p))
        }
        Type::Intersection(parts) => parts.iter().any(|p| definitely_offset_accessible(fa, p)),
        Type::Nullable(inner) => definitely_offset_accessible(fa, inner),
        _ => false,
    }
}

fn definitely_not_offset_accessible(fa: &FileAnalysis, t: &Type) -> bool {
    match t {
        Type::Int
        | Type::Float
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Resource
        | Type::LiteralInt(_) => true,
        Type::Named { fqn, .. } => {
            !fqn.trim_start_matches('\\')
                .eq_ignore_ascii_case("ArrayAccess")
                && fa.class_fully_known(fqn)
                && !fa.reflection.is_subclass_of(fqn, "ArrayAccess")
        }
        Type::Union(parts) => {
            !parts.is_empty()
                && parts
                    .iter()
                    .all(|p| definitely_not_offset_accessible(fa, p))
        }
        Type::Nullable(inner) => definitely_not_offset_accessible(fa, inner),
        _ => false,
    }
}

fn array_access_value_type(fa: &FileAnalysis, t: &Type) -> Option<Type> {
    match t {
        Type::Named { fqn, args } => array_access_value_type_named(fa, fqn, args, &mut Vec::new()),
        Type::Intersection(parts) => parts.iter().find_map(|p| array_access_value_type(fa, p)),
        _ => None,
    }
}

fn array_access_value_type_named(
    fa: &FileAnalysis,
    fqn: &str,
    args: &[Type],
    seen: &mut Vec<String>,
) -> Option<Type> {
    let key = fqn.trim_start_matches('\\').to_ascii_lowercase();
    if key == "arrayaccess" {
        return args.get(1).cloned();
    }
    if seen.contains(&key) {
        return None;
    }
    seen.push(key);
    let class = fa.reflection.class(fqn)?;
    class
        .interfaces
        .iter()
        .chain(&class.parents)
        .chain(&class.traits)
        .chain(&class.mixins)
        .find_map(|parent| match parent {
            Type::Named { fqn, args } => {
                let mut branch_seen = seen.clone();
                array_access_value_type_named(fa, fqn, args, &mut branch_seen)
            }
            Type::Intersection(parts) => parts.iter().find_map(|p| array_access_value_type(fa, p)),
            _ => None,
        })
}

fn definitely_empty_iterable_expr(fa: &FileAnalysis, expr: &Expr) -> bool {
    if matches!(&expr.kind, ExprKind::Array { items, .. } if items.is_empty()) {
        return true;
    }
    definitely_empty_iterable_type(&fa.type_of(expr))
}

fn definitely_empty_iterable_type(t: &Type) -> bool {
    matches!(t, Type::Shape { fields, sealed: true } if fields.is_empty())
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum StringKeyStatus {
    No,
    Potential,
    Yes,
}

fn combine_string_key_statuses(statuses: impl Iterator<Item = StringKeyStatus>) -> StringKeyStatus {
    let mut saw_yes = false;
    let mut saw_potential = false;
    let mut saw_no = false;
    for status in statuses {
        match status {
            StringKeyStatus::Yes => saw_yes = true,
            StringKeyStatus::Potential => saw_potential = true,
            StringKeyStatus::No => saw_no = true,
        }
    }
    if saw_yes && !saw_potential && !saw_no {
        StringKeyStatus::Yes
    } else if saw_yes || saw_potential {
        StringKeyStatus::Potential
    } else {
        StringKeyStatus::No
    }
}

fn key_type_string_status(t: &Type) -> StringKeyStatus {
    match t {
        Type::String | Type::LiteralString(_) | Type::ClassString(_) => StringKeyStatus::Yes,
        Type::Union(parts) => combine_string_key_statuses(parts.iter().map(key_type_string_status)),
        Type::Nullable(inner) => match key_type_string_status(inner) {
            StringKeyStatus::No => StringKeyStatus::No,
            _ => StringKeyStatus::Potential,
        },
        _ => StringKeyStatus::No,
    }
}

fn shape_key_is_string(key: &str) -> bool {
    php_infer::arrays::shape_key_is_string(key)
}

/// The key-type verdict used by `ArrayUnpackingRule` for PHP < 8.1. We do not
/// infer from bare `array`/`iterable`/unsealed tails: those could have string
/// keys, but our current type says nothing exact about them.
fn string_key_status(t: &Type) -> StringKeyStatus {
    match t {
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => key_type_string_status(&kv.0),
        Type::Shape { fields, .. } => {
            let mut optional_string = false;
            for f in fields {
                let Some(key) = &f.key else { continue };
                if !shape_key_is_string(key) {
                    continue;
                }
                if f.optional {
                    optional_string = true;
                } else {
                    return StringKeyStatus::Yes;
                }
            }
            if optional_string {
                StringKeyStatus::Potential
            } else {
                StringKeyStatus::No
            }
        }
        Type::Union(parts) => combine_string_key_statuses(parts.iter().map(string_key_status)),
        Type::Nullable(inner) => match string_key_status(inner) {
            StringKeyStatus::No => StringKeyStatus::No,
            _ => StringKeyStatus::Potential,
        },
        _ => StringKeyStatus::No,
    }
}

type ShapeOffsetStatus = php_infer::arrays::ShapeOffsetPresence;

fn const_shape_key(expr: &Expr) -> Option<String> {
    php_infer::arrays::const_shape_key(expr)
}

fn shape_offset_status(base_ty: &Type, key: &str) -> Option<ShapeOffsetStatus> {
    php_infer::arrays::shape_offset_status(base_ty, key).map(|status| status.without_type())
}

fn shape_offset_maybe_reportable(base_ty: &Type, key: &str) -> bool {
    php_infer::arrays::shape_offset_maybe_reportable(base_ty, key)
}

fn mark_index_subtree(expr: &Expr, spans: &mut HashSet<(u32, u32)>) {
    walk::for_each_subexpr(expr, &mut |e| {
        if matches!(e.kind, ExprKind::Index { .. }) {
            spans.insert(span_key(e.span));
        }
    });
}

fn write_index_spans(fa: &FileAnalysis) -> HashSet<(u32, u32)> {
    let mut spans = HashSet::new();
    for assign in fa.facts.assignments() {
        mark_index_subtree(assign.target, &mut spans);
    }
    for foreach in fa.facts.foreaches() {
        if let Some(key) = foreach.key {
            mark_index_subtree(key, &mut spans);
        }
        mark_index_subtree(foreach.value, &mut spans);
    }
    spans
}

fn undefined_allowed_index_spans(fa: &FileAnalysis) -> HashSet<(u32, u32)> {
    let mut spans = HashSet::new();
    for isset in fa.facts.issets() {
        for v in isset.vars {
            mark_index_subtree(v, &mut spans);
        }
    }
    for empty in fa.facts.empties() {
        mark_index_subtree(empty.inner, &mut spans);
    }
    for coalesce in fa.facts.coalesces() {
        mark_index_subtree(coalesce.lhs, &mut spans);
    }
    for assign in fa.facts.assignments() {
        if matches!(assign.kind, AssignmentKind::Op(php_ast::BinOp::Coalesce)) {
            mark_index_subtree(assign.target, &mut spans);
        }
    }
    spans
}

/// `IterableInForeachRule` (`foreach.nonIterable`, level 3): the subject of a
/// `foreach` must be iterable. We flag only when the subject's inferred type is
/// definitely non-iterable (see [`definitely_not_iterable`]).
fn run_iterable_in_foreach(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for foreach in fa.facts.foreaches() {
        let ty = fa.type_of(foreach.subject);
        if definitely_not_iterable(fa, &ty) {
            out.push(
                Diagnostic::error(
                    foreach.subject.span,
                    format!(
                        "Argument of an invalid type {ty} supplied for foreach, only iterables are supported.",
                    ),
                )
                .with_code("foreach.nonIterable"),
            );
        }
    }
    out
}

/// `UnpackIterableInArrayRule` (`arrayUnpacking.nonIterable`, level 3): a spread
/// element `[...$x]` requires `$x` to be iterable.
fn run_unpack_iterable_in_array(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for array in fa.facts.arrays() {
        for it in array.items {
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
    }
    out
}

/// `ArrayUnpackingRule` (`arrayUnpacking.stringOffset`, level 3): before PHP
/// 8.1, unpacking an iterable with string keys in an array literal is not
/// supported. We mirror phpstan's version gate and report only when our key type
/// information proves string keys or an exact type admits them.
fn run_array_unpacking_string_offset(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if fa.php_version.at_least(80100) {
        return Vec::new();
    }

    let mut out = Vec::new();
    for array in fa.facts.arrays() {
        for it in array.items {
            if !it.spread {
                continue;
            }
            let Some(value) = &it.value else { continue };
            let ty = fa.type_of(value);
            let status = string_key_status(&ty);
            if status == StringKeyStatus::No {
                continue;
            }
            let potential = if status == StringKeyStatus::Potential {
                "potential "
            } else {
                ""
            };
            out.push(
                Diagnostic::error(
                    value.span,
                    format!(
                        "Array unpacking cannot be used on an array with {potential}string keys: {ty}",
                    ),
                )
                .with_code("arrayUnpacking.stringOffset"),
            );
        }
    }
    out
}

/// `ArrayDestructuringRule` (`offsetAccess.nonArray`, level 3): the right side of
/// an array-destructuring assignment (`[$a, $b] = $x` or `list(...) = $x`) must
/// be an array or `ArrayAccess`.
fn run_array_destructuring(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for assign in fa.facts.assignments() {
        if !matches!(assign.kind, AssignmentKind::Plain) {
            continue;
        }
        // Only a list/array destructuring target triggers this rule.
        if !matches!(assign.target.kind, ExprKind::Array { .. }) {
            continue;
        }
        let ty = fa.type_of(assign.rhs);
        if definitely_not_array_destructurable(fa, &ty) {
            out.push(
                Diagnostic::error(
                    assign.rhs.span,
                    format!("Cannot use array destructuring on {ty}."),
                )
                .with_code("offsetAccess.nonArray"),
            );
        }
    }
    out
}

/// `InvalidKeyInArrayItemRule` (`array.invalidKey`, level 3): a key in an array
/// literal must be a valid array-key type (`int|string`, or a bool/float/null
/// PHP coerces). We flag only keys whose type is definitely invalid
/// (array/object/resource).
fn run_invalid_key_in_array_item(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for array in fa.facts.arrays() {
        for it in array.items {
            let Some(key) = &it.key else { continue };
            let ty = fa.type_of(key);
            if definitely_invalid_key(&ty) {
                out.push(
                    Diagnostic::error(key.span, format!("Invalid array key type {ty}."))
                        .with_code("array.invalidKey"),
                );
            }
        }
    }
    out
}

/// `InvalidKeyInArrayDimFetchRule` (`offsetAccess.invalidOffset`, level 3): an
/// array dim-fetch `$arr[$k]` (on a value we know is an array) must use a valid
/// array-key type. Gated on the base being *definitely* an array so we don't
/// misfire on string offsets (`$s[$i]`) or `ArrayAccess` objects.
fn run_invalid_key_in_dim_fetch(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for index in fa.facts.indexes() {
        let Some(dim) = index.index else {
            continue;
        };
        if !definitely_array(&fa.type_of(index.base)) {
            continue;
        }
        let ty = fa.type_of(dim);
        if definitely_invalid_key(&ty) {
            out.push(
                Diagnostic::error(dim.span, format!("Invalid array key type {ty}."))
                    .with_code("offsetAccess.invalidOffset"),
            );
        }
    }
    out
}

/// `OffsetAccessAssignmentRule` / `OffsetAccessAssignOpRule`
/// (`offsetAssign.dimType`, level 3): assigning to a string offset must use an
/// existing integer offset. This is a deliberately small subset of phpstan's
/// `setOffsetValueType` logic: arrays, unions, `ArrayAccess` key contracts,
/// array-shape mutations, and maybe cases are left alone.
fn run_offset_access_assignment(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for assign in fa.facts.assignments() {
        let target = assign.target;
        let ExprKind::Index { base, index } = &target.kind else {
            continue;
        };
        let base_ty = fa.type_of(base);
        if !definitely_string_offset_base(&base_ty) {
            continue;
        }
        let dim_ty = index.as_ref().map(|dim| fa.type_of(dim));
        if !definitely_invalid_string_write_offset(dim_ty.as_ref()) {
            continue;
        }
        let msg = match &dim_ty {
            None => format!("Cannot assign new offset to {base_ty}."),
            Some(dim_ty) => format!("Cannot assign offset {dim_ty} to {base_ty}."),
        };
        out.push(Diagnostic::error(target.span, msg).with_code("offsetAssign.dimType"));
    }
    out
}

/// `OffsetAccessValueAssignmentRule` (`offsetAssign.valueType`, level 3):
/// `ArrayAccess<TKey, TValue>` accepts only values assignable to `TValue`.
/// Without the explicit generic contract we cannot know what `offsetSet`
/// accepts, so this under-reports by design.
fn run_offset_access_value_assignment(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for assign in fa.facts.assignments() {
        let assigned_ty = match assign.kind {
            AssignmentKind::Plain | AssignmentKind::Ref => fa.type_of(assign.rhs),
            AssignmentKind::Op(_) => fa.type_of(assign.expr),
        };
        let ExprKind::Index { base, .. } = &assign.target.kind else {
            continue;
        };
        let base_ty = fa.type_of(base);
        let Some(accepted_ty) = array_access_value_type(fa, &base_ty) else {
            continue;
        };
        let checked_value = fa.lenient_src(assigned_ty.clone());
        if crate::is_assignable(fa.reflection, &checked_value, &accepted_ty) {
            continue;
        }
        out.push(
            Diagnostic::error(
                assign.target.span,
                format!("{base_ty} does not accept {assigned_ty}."),
            )
            .with_code("offsetAssign.valueType"),
        );
    }
    out
}

/// `NonexistentOffsetInArrayDimFetchRule` / `NonexistentOffsetInArrayDimFetchCheck`
/// (`offsetAccess.notFound`, level 3): a literal-key read from a sealed array
/// shape must refer to a declared field. This is the exact branch our current
/// type map can prove; general `array<K,V>`, optional fields, writes, and
/// `isset`/`empty`/`??` contexts are left alone.
fn run_nonexistent_offset_in_array_dim_fetch(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let write_spans = write_index_spans(fa);
    let undefined_allowed = undefined_allowed_index_spans(fa);
    let mut out = Vec::new();
    for index in fa.facts.indexes() {
        let Some(dim) = index.index else {
            continue;
        };
        let key = span_key(index.expr.span);
        if write_spans.contains(&key) || undefined_allowed.contains(&key) {
            continue;
        }
        let Some(shape_key) = const_shape_key(dim) else {
            continue;
        };
        let base_ty = fa.type_of(index.base);
        if !matches!(
            shape_offset_status(&base_ty, &shape_key),
            Some(ShapeOffsetStatus::Missing)
        ) {
            continue;
        }
        let dim_ty = fa.type_of(dim);
        out.push(
            Diagnostic::error(
                index.expr.span,
                format!("Offset {dim_ty} does not exist on {base_ty}."),
            )
            .with_code("offsetAccess.notFound"),
        );
    }
    out
}

fn run_maybe_nonexistent_offset_in_array_dim_fetch(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.report_maybes {
        return Vec::new();
    }
    let write_spans = write_index_spans(fa);
    let undefined_allowed = undefined_allowed_index_spans(fa);
    let mut out = Vec::new();
    for index in fa.facts.indexes() {
        let Some(dim) = index.index else {
            continue;
        };
        let key = span_key(index.expr.span);
        if write_spans.contains(&key) || undefined_allowed.contains(&key) {
            continue;
        }
        let Some(shape_key) = const_shape_key(dim) else {
            continue;
        };
        let base_ty = fa.type_of(index.base);
        if !shape_offset_maybe_reportable(&base_ty, &shape_key) {
            continue;
        }
        let dim_ty = fa.type_of(dim);
        out.push(
            Diagnostic::error(
                index.expr.span,
                format!("Offset {dim_ty} might not exist on {base_ty}."),
            )
            .with_code("offsetAccess.notFound"),
        );
    }
    out
}

/// Level-8 `checkNullables` strictness for offset access. We only report the
/// unambiguous nullable-container slice: the non-null part is definitely
/// offset-readable, and the read is not in `isset`/`empty`/`??` or an
/// auto-vivifying write context.
fn run_nullable_offset_access(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let write_spans = write_index_spans(fa);
    let undefined_allowed = undefined_allowed_index_spans(fa);
    let mut out = Vec::new();
    for index in fa.facts.indexes() {
        let key = span_key(index.expr.span);
        if write_spans.contains(&key) || undefined_allowed.contains(&key) {
            continue;
        }
        let base_ty = fa.type_of(index.base);
        let Some(non_null) = super::non_null_part(&base_ty) else {
            continue;
        };
        if !definitely_offset_accessible(fa, &non_null) {
            continue;
        }
        let message = if let Some(dim) = index.index {
            let dim_ty = fa.type_of(dim);
            format!(
                "Cannot access offset {dim_ty} on {}.",
                super::nullable_type_display(&base_ty)
            )
        } else {
            format!(
                "Cannot access an offset on {}.",
                super::nullable_type_display(&base_ty)
            )
        };
        out.push(
            Diagnostic::error(index.expr.span, message)
                .with_code("offsetAccess.nonOffsetAccessible"),
        );
    }
    out
}

/// Level-7 `checkUnionTypes` / partial union offset access: report when an
/// offset read is valid for some union arms but definitely invalid for others.
fn run_union_offset_access(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.report_maybes {
        return Vec::new();
    }
    let write_spans = write_index_spans(fa);
    let undefined_allowed = undefined_allowed_index_spans(fa);
    let mut out = Vec::new();
    for index in fa.facts.indexes() {
        let key = span_key(index.expr.span);
        if write_spans.contains(&key) || undefined_allowed.contains(&key) {
            continue;
        }
        let base_ty = fa.type_of(index.base);
        let Some((accessible, inaccessible)) = union_offset_status(fa, &base_ty) else {
            continue;
        };
        if !(accessible && inaccessible) {
            continue;
        }
        let message = if let Some(dim) = index.index {
            let dim_ty = fa.type_of(dim);
            format!("Cannot access offset {dim_ty} on {base_ty}.")
        } else {
            format!("Cannot access an offset on {base_ty}.")
        };
        out.push(
            Diagnostic::error(index.expr.span, message)
                .with_code("offsetAccess.nonOffsetAccessible"),
        );
    }
    out
}

fn union_offset_status(fa: &FileAnalysis, ty: &Type) -> Option<(bool, bool)> {
    let Type::Union(parts) = ty else {
        return None;
    };
    if parts.len() < 2 || super::type_contains_null(ty) {
        return None;
    }
    let mut accessible = false;
    let mut inaccessible = false;
    for part in parts {
        if definitely_offset_accessible(fa, part) {
            accessible = true;
        } else if definitely_not_offset_accessible(fa, part) {
            inaccessible = true;
        } else {
            return None;
        }
    }
    Some((accessible, inaccessible))
}

/// `DeadForeachRule` (`foreach.emptyArray`, level 4): a foreach over a value
/// that is definitely iterable but never has an element. We currently know that
/// only for the literal `[]` and empty sealed shapes.
fn run_dead_foreach(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for foreach in fa.facts.foreaches() {
        if definitely_empty_iterable_expr(fa, foreach.subject) {
            out.push(
                Diagnostic::error(foreach.subject.span, "Empty array passed to foreach.")
                    .with_code("foreach.emptyArray"),
            );
        }
    }
    out
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "array.duplicateKey",
        level: 0,
        run: run_duplicate_keys,
    },
    RuleEntry {
        name: "offsetAccess.noDim",
        level: 0,
        run: run_offset_access_no_dim,
    },
    RuleEntry {
        name: "foreach.nonIterable",
        level: 3,
        run: run_iterable_in_foreach,
    },
    RuleEntry {
        name: "arrayUnpacking.nonIterable",
        level: 3,
        run: run_unpack_iterable_in_array,
    },
    RuleEntry {
        name: "arrayUnpacking.stringOffset",
        level: 3,
        run: run_array_unpacking_string_offset,
    },
    RuleEntry {
        name: "offsetAccess.nonArray",
        level: 3,
        run: run_array_destructuring,
    },
    RuleEntry {
        name: "array.invalidKey",
        level: 3,
        run: run_invalid_key_in_array_item,
    },
    RuleEntry {
        name: "offsetAccess.invalidOffset",
        level: 3,
        run: run_invalid_key_in_dim_fetch,
    },
    RuleEntry {
        name: "offsetAssign.dimType",
        level: 3,
        run: run_offset_access_assignment,
    },
    RuleEntry {
        name: "offsetAssign.valueType",
        level: 3,
        run: run_offset_access_value_assignment,
    },
    RuleEntry {
        name: "offsetAccess.notFound",
        level: 3,
        run: run_nonexistent_offset_in_array_dim_fetch,
    },
    RuleEntry {
        name: "offsetAccess.maybeNotFound",
        level: 7,
        run: run_maybe_nonexistent_offset_in_array_dim_fetch,
    },
    RuleEntry {
        name: "offsetAccess.nullable",
        level: 8,
        run: run_nullable_offset_access,
    },
    RuleEntry {
        name: "offsetAccess.union",
        level: 7,
        run: run_union_offset_access,
    },
    RuleEntry {
        name: "foreach.emptyArray",
        level: 4,
        run: run_dead_foreach,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        testutil::{codes, codes_version},
        PhpVersion,
    };

    // --- array.duplicateKey ---

    #[test]
    fn duplicate_int_keys_flagged() {
        assert_eq!(
            codes("<?php $a = [1 => 'a', 1 => 'b'];", run_duplicate_keys),
            ["array.duplicateKey"]
        );
    }

    #[test]
    fn duplicate_string_keys_flagged() {
        assert_eq!(
            codes("<?php $a = ['x' => 1, 'x' => 2];", run_duplicate_keys),
            ["array.duplicateKey"]
        );
    }

    #[test]
    fn distinct_keys_ok() {
        assert!(codes(
            "<?php $a = [1 => 'a', 2 => 'b', 'x' => 1];",
            run_duplicate_keys
        )
        .is_empty());
    }

    #[test]
    fn keyless_then_explicit_same_index_is_duplicate() {
        // `'a'` is index 0, then `0 => 'b'` collides.
        assert_eq!(
            codes("<?php $a = ['a', 0 => 'b'];", run_duplicate_keys),
            ["array.duplicateKey"]
        );
    }

    #[test]
    fn explicit_index_then_keyless_advances() {
        // `5 => 'a'` then keyless `'b'` becomes index 6 — no collision.
        assert!(codes("<?php $a = [5 => 'a', 'b'];", run_duplicate_keys).is_empty());
    }

    #[test]
    fn numeric_string_key_coerces_to_int() {
        // "0" coerces to int 0, colliding with int 0.
        assert_eq!(
            codes("<?php $a = ['0' => 1, 0 => 2];", run_duplicate_keys),
            ["array.duplicateKey"]
        );
    }

    #[test]
    fn non_canonical_numeric_string_stays_string() {
        // "01" is NOT coerced (leading zero), so no collision with int 1.
        assert!(codes("<?php $a = ['01' => 1, 1 => 2];", run_duplicate_keys).is_empty());
    }

    #[test]
    fn non_constant_keys_skipped() {
        assert!(codes(
            "<?php $a = [$x => 1, $y => 2, foo() => 3];",
            run_duplicate_keys
        )
        .is_empty());
    }

    #[test]
    fn duplicate_in_nested_array_flagged() {
        let src = "<?php $a = [[1 => 'a', 1 => 'b']];";
        assert_eq!(codes(src, run_duplicate_keys), ["array.duplicateKey"]);
    }

    #[test]
    fn triple_duplicate_counts_one_diagnostic() {
        // Three occurrences of key 1 → one diagnostic for that key.
        assert_eq!(
            codes(
                "<?php $a = [1 => 'a', 1 => 'b', 1 => 'c'];",
                run_duplicate_keys
            ),
            ["array.duplicateKey"]
        );
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
        assert_eq!(
            codes("<?php $x = $a[];", run_offset_access_no_dim),
            ["offsetAccess.noDim"]
        );
    }

    #[test]
    fn append_in_argument_read_is_flagged() {
        assert_eq!(
            codes("<?php foo($a[]);", run_offset_access_no_dim),
            ["offsetAccess.noDim"]
        );
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
            codes(
                "<?php $n = 1; foreach ($n as $x) {}",
                run_iterable_in_foreach
            ),
            ["foreach.nonIterable"]
        );
    }

    #[test]
    fn foreach_over_string_flagged() {
        assert_eq!(
            codes(
                "<?php $s = 'hi'; foreach ($s as $x) {}",
                run_iterable_in_foreach
            ),
            ["foreach.nonIterable"]
        );
    }

    #[test]
    fn foreach_over_array_ok() {
        assert!(codes(
            "<?php $a = [1, 2]; foreach ($a as $x) {}",
            run_iterable_in_foreach
        )
        .is_empty());
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
        assert!(codes(
            "<?php $b = [1]; $a = [...$b];",
            run_unpack_iterable_in_array
        )
        .is_empty());
    }

    #[test]
    fn unpack_unknown_ok() {
        assert!(codes("<?php $a = [...$b];", run_unpack_iterable_in_array).is_empty());
    }

    // --- arrayUnpacking.stringOffset ---

    #[test]
    fn unpack_string_keyed_shape_flagged_before_php_81() {
        let v80 = PhpVersion::parse("8.0").unwrap();
        assert_eq!(
            codes_version(
                "<?php $b = ['a' => 1]; $a = [...$b];",
                run_array_unpacking_string_offset,
                v80,
            ),
            ["arrayUnpacking.stringOffset"]
        );
    }

    #[test]
    fn unpack_string_keys_allowed_on_php_81() {
        let v81 = PhpVersion::parse("8.1").unwrap();
        assert!(codes_version(
            "<?php $b = ['a' => 1]; $a = [...$b];",
            run_array_unpacking_string_offset,
            v81,
        )
        .is_empty());
    }

    #[test]
    fn unpack_int_keyed_shape_ok_before_php_81() {
        let v80 = PhpVersion::parse("8.0").unwrap();
        assert!(codes_version(
            "<?php $b = [0 => 1]; $a = [...$b];",
            run_array_unpacking_string_offset,
            v80,
        )
        .is_empty());
    }

    #[test]
    fn unpack_noncanonical_numeric_string_key_flagged_before_php_81() {
        let v80 = PhpVersion::parse("8.0").unwrap();
        assert_eq!(
            codes_version(
                "<?php $b = ['01' => 1]; $a = [...$b];",
                run_array_unpacking_string_offset,
                v80,
            ),
            ["arrayUnpacking.stringOffset"]
        );
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
            codes(
                "<?php $k = [1]; $a = [$k => 'v'];",
                run_invalid_key_in_array_item
            ),
            ["array.invalidKey"]
        );
    }

    #[test]
    fn array_literal_int_key_ok() {
        assert!(codes(
            "<?php $a = [1 => 'v', 'x' => 'y'];",
            run_invalid_key_in_array_item
        )
        .is_empty());
    }

    #[test]
    fn array_literal_object_key_flagged() {
        let src = "<?php class Foo {} $k = new Foo(); $a = [$k => 'v'];";
        assert_eq!(
            codes(src, run_invalid_key_in_array_item),
            ["array.invalidKey"]
        );
    }

    #[test]
    fn array_literal_unknown_key_ok() {
        assert!(codes("<?php $a = [$k => 'v'];", run_invalid_key_in_array_item).is_empty());
    }

    // --- offsetAccess.invalidOffset ---

    #[test]
    fn dim_fetch_array_key_flagged() {
        assert_eq!(
            codes(
                "<?php $arr = [1, 2]; $k = ['x']; $v = $arr[$k];",
                run_invalid_key_in_dim_fetch
            ),
            ["offsetAccess.invalidOffset"]
        );
    }

    #[test]
    fn dim_fetch_int_key_ok() {
        assert!(codes(
            "<?php $arr = [1, 2]; $v = $arr[0];",
            run_invalid_key_in_dim_fetch
        )
        .is_empty());
    }

    #[test]
    fn dim_fetch_unknown_base_ok() {
        // Base type unknown → not gated as an array → not flagged.
        assert!(codes(
            "<?php $k = [1]; $v = $arr[$k];",
            run_invalid_key_in_dim_fetch
        )
        .is_empty());
    }

    // --- offsetAssign.dimType ---

    #[test]
    fn string_offset_assignment_with_string_key_flagged() {
        assert_eq!(
            codes(
                "<?php $s = 'abc'; $s['foo'] = 'x';",
                run_offset_access_assignment
            ),
            ["offsetAssign.dimType"]
        );
    }

    #[test]
    fn string_append_assignment_flagged() {
        assert_eq!(
            codes(
                "<?php $s = 'abc'; $s[] = 'x';",
                run_offset_access_assignment
            ),
            ["offsetAssign.dimType"]
        );
    }

    #[test]
    fn string_integer_offset_assignment_ok() {
        assert!(codes(
            "<?php $s = 'abc'; $s[1] = 'x';",
            run_offset_access_assignment
        )
        .is_empty());
    }

    #[test]
    fn array_offset_assignment_not_dim_type_subset() {
        assert!(codes(
            "<?php $a = []; $a['foo'] = 'x';",
            run_offset_access_assignment
        )
        .is_empty());
    }

    #[test]
    fn compound_string_append_assignment_flagged() {
        assert_eq!(
            codes("<?php $s = 'abc'; $s[] += 1;", run_offset_access_assignment),
            ["offsetAssign.dimType"]
        );
    }

    #[test]
    fn compound_string_offset_assignment_with_string_key_flagged() {
        assert_eq!(
            codes(
                "<?php $s = 'abc'; $s['foo'] .= 'x';",
                run_offset_access_assignment
            ),
            ["offsetAssign.dimType"]
        );
    }

    #[test]
    fn compound_string_integer_offset_assignment_ok() {
        assert!(codes(
            "<?php $s = 'abc'; $s[1] .= 'x';",
            run_offset_access_assignment
        )
        .is_empty());
    }

    // --- offsetAssign.valueType ---

    #[test]
    fn arrayaccess_value_assignment_flagged() {
        let src = r#"<?php
        /** @param \ArrayAccess<int, int> $a */
        function f(\ArrayAccess $a): void {
            $a[] = 'x';
        }
        "#;
        assert_eq!(
            codes(src, run_offset_access_value_assignment),
            ["offsetAssign.valueType"]
        );
    }

    #[test]
    fn arrayaccess_value_assignment_ok() {
        let src = r#"<?php
        /** @param \ArrayAccess<int, int> $a */
        function f(\ArrayAccess $a): void {
            $a[] = 1;
        }
        "#;
        assert!(codes(src, run_offset_access_value_assignment).is_empty());
    }

    #[test]
    fn array_value_assignment_not_arrayaccess_subset() {
        assert!(codes(
            "<?php $a = []; $a[] = 'x';",
            run_offset_access_value_assignment
        )
        .is_empty());
    }

    // --- offsetAccess.notFound ---

    #[test]
    fn missing_literal_offset_on_sealed_shape_flagged() {
        assert_eq!(
            codes(
                "<?php $a = ['a' => 1]; echo $a['b'];",
                run_nonexistent_offset_in_array_dim_fetch
            ),
            ["offsetAccess.notFound"]
        );
    }

    #[test]
    fn existing_literal_offset_on_shape_ok() {
        assert!(codes(
            "<?php $a = ['a' => 1]; echo $a['a'];",
            run_nonexistent_offset_in_array_dim_fetch
        )
        .is_empty());
    }

    #[test]
    fn dynamic_offset_on_shape_ok() {
        assert!(codes(
            "<?php $a = ['a' => 1]; echo $a[$k];",
            run_nonexistent_offset_in_array_dim_fetch
        )
        .is_empty());
    }

    #[test]
    fn numeric_offset_on_keyless_shape_is_not_definitely_missing() {
        let shape = Type::Shape {
            fields: vec![
                php_types::ShapeField {
                    key: None,
                    optional: false,
                    ty: Type::Int,
                },
                php_types::ShapeField {
                    key: None,
                    optional: false,
                    ty: Type::Int,
                },
                php_types::ShapeField {
                    key: None,
                    optional: false,
                    ty: Type::Int,
                },
            ],
            sealed: true,
        };
        assert!(!matches!(
            shape_offset_status(&shape, "0"),
            Some(ShapeOffsetStatus::Missing)
        ));
    }

    #[test]
    fn missing_offset_write_is_not_reported() {
        assert!(codes(
            "<?php $a = ['a' => 1]; $a['b'] = 2;",
            run_nonexistent_offset_in_array_dim_fetch
        )
        .is_empty());
    }

    #[test]
    fn missing_offset_isset_is_not_reported() {
        assert!(codes(
            "<?php $a = ['a' => 1]; isset($a['b']);",
            run_nonexistent_offset_in_array_dim_fetch
        )
        .is_empty());
    }

    #[test]
    fn missing_offset_null_coalesce_is_not_reported() {
        assert!(codes(
            "<?php $a = ['a' => 1]; $x = $a['b'] ?? null;",
            run_nonexistent_offset_in_array_dim_fetch
        )
        .is_empty());
    }

    #[test]
    fn optional_shape_offset_is_reported_as_maybe_missing() {
        let src = r#"<?php
            /** @param array{foo?:int} $a */
            function f($a) { return $a['foo']; }"#;
        assert_eq!(
            codes(src, run_maybe_nonexistent_offset_in_array_dim_fetch),
            ["offsetAccess.notFound"]
        );
    }

    #[test]
    fn union_shape_offset_is_reported_as_maybe_missing() {
        let src = r#"<?php
            /** @param array{foo:int}|array{bar:int} $a */
            function f($a) { return $a['foo']; }"#;
        assert_eq!(
            codes(src, run_maybe_nonexistent_offset_in_array_dim_fetch),
            ["offsetAccess.notFound"]
        );
    }

    #[test]
    fn nullable_array_offset_read_is_flagged_at_strict_level() {
        assert_eq!(
            codes(
                "<?php function f(?array $a): mixed { return $a['x']; }",
                run_nullable_offset_access
            ),
            ["offsetAccess.nonOffsetAccessible"]
        );
    }

    #[test]
    fn nullable_shape_offset_read_is_flagged_at_strict_level() {
        assert_eq!(
            codes(
                "<?php /** @param array{x:int}|null $a */ function f($a): mixed { return $a['x']; }",
                run_nullable_offset_access
            ),
            ["offsetAccess.nonOffsetAccessible"]
        );
    }

    #[test]
    fn nullable_offset_in_null_coalesce_is_clean() {
        assert!(codes(
            "<?php function f(?array $a): mixed { return $a['x'] ?? null; }",
            run_nullable_offset_access
        )
        .is_empty());
    }

    #[test]
    fn nullable_offset_plain_assignment_is_clean() {
        assert!(codes(
            "<?php function f(?array $a): void { $a['x'] = 1; }",
            run_nullable_offset_access
        )
        .is_empty());
    }

    #[test]
    fn union_offset_access_missing_on_one_arm_is_flagged() {
        assert_eq!(
            codes(
                "<?php /** @param array<string, int>|int $a */ function f($a): mixed { return $a['x']; }",
                run_union_offset_access
            ),
            ["offsetAccess.nonOffsetAccessible"]
        );
    }

    #[test]
    fn union_offset_accessible_on_all_arms_is_clean() {
        assert!(codes(
            "<?php /** @param array<string, int>|string $a */ function f($a): mixed { return $a['x']; }",
            run_union_offset_access
        )
        .is_empty());
    }

    #[test]
    fn nullable_union_offset_access_is_left_to_nullable_rule() {
        assert!(codes(
            "<?php /** @param array<string, int>|null $a */ function f($a): mixed { return $a['x']; }",
            run_union_offset_access
        )
        .is_empty());
    }

    // --- foreach.emptyArray ---

    #[test]
    fn foreach_empty_literal_flagged() {
        assert_eq!(
            codes("<?php foreach ([] as $v) {}", run_dead_foreach),
            ["foreach.emptyArray"]
        );
    }

    #[test]
    fn foreach_non_empty_literal_ok() {
        assert!(codes("<?php foreach ([1] as $v) {}", run_dead_foreach).is_empty());
    }

    #[test]
    fn foreach_empty_phpdoc_shape_flagged() {
        let src = r#"<?php
        $a = [];
        /** @var array{} $a */
        foreach ($a as $v) {}
        "#;
        assert_eq!(codes(src, run_dead_foreach), ["foreach.emptyArray"]);
    }

    #[test]
    fn foreach_bare_array_variable_not_flagged() {
        assert!(codes(
            "<?php function f(array $a): void { foreach ($a as $v) {} }",
            run_dead_foreach
        )
        .is_empty());
    }
}
