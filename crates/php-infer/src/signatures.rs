//! Whole-project signature inference for **fully untyped** functions/methods.
//!
//! PHPStan trusts declarations: on untyped legacy PHP everything is `mixed`, so
//! almost no checks fire. This pass synthesizes signatures for functions/methods
//! that have *no* declared type, from two evidence sources:
//!
//! 1. **Call sites** — the argument types callers actually pass become the
//!    parameter types (union across all observed positional call sites).
//! 2. **Bodies** — the union of a function's `return <expr>` statement types
//!    becomes its return type.
//!
//! Results are folded back into the stored [`ReflectionIndex`] via
//! [`ReflectionIndex::apply_inferred`], treated exactly like PHPDoc types: they
//! refine `ty`/`return_type` only, never `native_*`, and only ever overwrite a
//! slot that was not explicitly declared. Every inferred type is the **union of
//! observed evidence with `mixed` retained on any uncertainty** — an unanalyzable
//! return path or an unknown argument poisons the union, which we then decline to
//! record, so uncertainty degrades to today's behavior rather than to a false
//! positive. Under-narrowing (e.g. inferring `User` for what is really
//! `User|null`) produces false negatives, never false positives — the safe
//! direction for this analyzer.
//!
//! Parameters are applied *before* returns so a body's return inference sees its
//! own (call-site-derived) parameter types; the return phase then iterates to a
//! small fixpoint so a function returning the result of another untyped function
//! converges.

use crate::returns::collect_returns;
use crate::{type_map, TypeCtx, TypeMap};
use php_ast::{walk, Arg, Expr, ExprKind, MemberName, Program, Stmt};
use php_intern::Interner;
use php_reflect::{InferredSig, InferredSignatures, ParamReflection, ReflectionIndex};
use php_resolve::{resolve_references, RefKind, Resolution, ResolvedRef, Scope};
use php_types::Type;
use rayon::prelude::*;
use std::collections::HashMap;

/// Tuning for [`infer_and_apply`].
#[derive(Debug, Clone, Copy)]
pub struct InferOpts {
    /// Maximum return-inference fixpoint rounds (converges earlier when stable).
    pub rounds: u32,
}

impl Default for InferOpts {
    fn default() -> Self {
        InferOpts {
            rounds: crate::limits::SIGNATURE_INFERENCE_ROUNDS,
        }
    }
}

/// Infer signatures for untyped functions/methods across `programs` and fold them
/// into `index` in place. `programs` must be the same parsed files the `index`
/// was built from (they supply the call sites). Idempotent-ish: re-running on an
/// already-enriched index reproduces the same result.
///
/// Returns the **combined** signatures that were applied (call-site params merged
/// with the final fixpoint returns, per key) — incremental analysis diffs this
/// against the previous pass to invalidate files that depend on an *inferred*
/// signature that changed.
pub fn infer_and_apply(
    index: &mut ReflectionIndex,
    programs: &[&Program],
    interner: &Interner,
    opts: InferOpts,
) -> InferredSignatures {
    // Phase A — parameter types from call sites (one pass; the expensive part, as
    // it builds a type map per file). Apply before returns so bodies see them.
    let mut combined = infer_params_from_callsites(index, programs, interner);
    index.apply_inferred(&combined);

    // Phase B — return types from bodies, to a small fixpoint so a function whose
    // return is another untyped function's result converges.
    let mut prev = InferredSignatures::default();
    for _ in 0..opts.rounds.max(1) {
        let returns = infer_returns_from_bodies(index, interner);
        if returns == prev {
            break;
        }
        index.apply_inferred(&returns);
        prev = returns;
    }
    merge_returns(&mut combined, prev);
    combined
}

/// Merge the final return-inference results into the param results: per key,
/// keep the inferred params and adopt the return.
fn merge_returns(combined: &mut InferredSignatures, returns: InferredSignatures) {
    for (fqn, sig) in returns.fns {
        combined.fns.entry(fqn).or_default().ret = sig.ret;
    }
    for (key, sig) in returns.methods {
        combined.methods.entry(key).or_default().ret = sig.ret;
    }
}

// --- return inference -------------------------------------------------------

fn infer_returns_from_bodies(index: &ReflectionIndex, interner: &Interner) -> InferredSignatures {
    let mut out = InferredSignatures::default();

    // Each function/method is independent — infer returns in parallel and
    // collect (HashMap insertion order is irrelevant to the result).
    let fn_rets: Vec<(String, Type)> = index
        .function_fqns()
        .into_par_iter()
        .filter_map(|fqn| {
            let f = index.function(&fqn)?;
            if f.builtin || f.explicit_return || !index.has_function_body(&fqn) {
                return None;
            }
            let params = param_seeds(&f.params);
            let (body, scope) = index.function_body(&fqn)?;
            let ret = body_return_type(index, interner, body, scope, None, &params)?;
            Some((fqn, ret))
        })
        .collect();
    for (fqn, ret) in fn_rets {
        out.fns.insert(fqn, InferredSig::ret_only(ret));
    }

    let method_rets: Vec<((String, String), Type)> = index
        .class_fqns()
        .into_par_iter()
        .flat_map_iter(|class_fqn| {
            let mut rets = Vec::new();
            let Some(c) = index.class(&class_fqn) else {
                return rets.into_iter();
            };
            if c.builtin {
                return rets.into_iter();
            }
            // Snapshot the inferable methods first so we don't hold `c`'s borrow
            // while re-borrowing the index for each body.
            let targets: Vec<(String, Vec<(String, Type)>)> = c
                .methods
                .iter()
                .filter(|m| {
                    !m.magic && !m.explicit_return && index.has_method_body(&class_fqn, &m.name)
                })
                .map(|m| (m.name.clone(), param_seeds(&m.params)))
                .collect();
            for (mname, params) in targets {
                if let Some((body, scope)) = index.method_body(&class_fqn, &mname) {
                    let class = Some(class_fqn.clone());
                    if let Some(ret) =
                        body_return_type(index, interner, body, scope, class, &params)
                    {
                        rets.push(((class_fqn.clone(), mname), ret));
                    }
                }
            }
            rets.into_iter()
        })
        .collect();
    for (key, ret) in method_rets {
        out.methods.insert(key, InferredSig::ret_only(ret));
    }

    out
}

/// The seed `(name, local_type)` pairs for a body's parameters.
fn param_seeds(params: &[ParamReflection]) -> Vec<(String, Type)> {
    params
        .iter()
        .map(|p| (p.name.clone(), p.local_type()))
        .collect()
}

/// Union of the value-`return` types reachable in `body`, or `None` when the
/// function has no value returns or the union is not more precise than `mixed`.
/// Skips generators (a `yield` body returns a `Generator`, not its yield values).
fn body_return_type(
    index: &ReflectionIndex,
    interner: &Interner,
    body: &[Stmt],
    scope: &Scope,
    class: Option<String>,
    params: &[(String, Type)],
) -> Option<Type> {
    if is_generator(body) {
        return None;
    }
    let mut ctx = TypeCtx::new(index, scope, interner);
    ctx.class = class;
    // depth 1 so any nested per-call refinement stays shallow (one more level).
    ctx.depth = crate::limits::CALLEE_ANALYSIS_DEPTH;
    ctx.vars = params.iter().cloned().collect();

    let mut returns = Vec::new();
    collect_returns(&mut ctx, body, &mut returns);
    if returns.is_empty() {
        return None;
    }
    let ty = Type::union(returns);
    useful_inference(&ty).then_some(ty)
}

/// Whether `body` is a generator (contains `yield`/`yield from` in its own scope).
fn is_generator(body: &[Stmt]) -> bool {
    let mut found = false;
    for s in body {
        walk::for_each_expr_in_scope(s, &mut |e| {
            if matches!(e.kind, ExprKind::Yield { .. } | ExprKind::YieldFrom(_)) {
                found = true;
            }
        });
        if found {
            break;
        }
    }
    found
}

// --- parameter inference from call sites ------------------------------------

fn infer_params_from_callsites(
    index: &ReflectionIndex,
    programs: &[&Program],
    interner: &Interner,
) -> InferredSignatures {
    // Harvest per file in parallel (the throwaway per-file type map is the
    // expensive part), then merge **in file order**: observation order feeds
    // `Type::union`'s order-preserving dedup, so the merged result must be
    // byte-identical to the old sequential pass.
    let per_file: Vec<(FnArgs, MethodArgs)> = programs
        .par_iter()
        .map(|program| harvest_file(index, program, interner))
        .collect();

    // Observed argument types per (target, position).
    let mut fn_args: FnArgs = HashMap::new();
    let mut method_args: MethodArgs = HashMap::new();
    for (file_fns, file_methods) in per_file {
        for (fqn, positions) in file_fns {
            merge_positions(fn_args.entry(fqn).or_default(), positions);
        }
        for (key, positions) in file_methods {
            merge_positions(method_args.entry(key).or_default(), positions);
        }
    }

    let mut out = InferredSignatures::default();
    for (fqn, positions) in fn_args {
        let Some(f) = index.function(&fqn) else {
            continue;
        };
        if f.builtin {
            continue;
        }
        let sig = build_param_sig(&f.params, &positions);
        if !sig.is_empty() {
            out.fns.insert(fqn, sig);
        }
    }
    for ((class_fqn, mname), positions) in method_args {
        let Some(c) = index.class(&class_fqn) else {
            continue;
        };
        if c.builtin {
            continue;
        }
        let Some(m) = c
            .methods
            .iter()
            .find(|m| m.name.eq_ignore_ascii_case(&mname))
        else {
            continue;
        };
        let sig = build_param_sig(&m.params, &positions);
        if !sig.is_empty() {
            out.methods.insert((class_fqn, mname), sig);
        }
    }
    out
}

type FnArgs = HashMap<String, Vec<Vec<Type>>>;
type MethodArgs = HashMap<(String, String), Vec<Vec<Type>>>;

// --- explicit-`array` parameter evidence (for `--fix`) -----------------------

/// Call-site evidence for parameters *explicitly* declared as a bare
/// `array`/`iterable`: the refined union of observed argument types, keyed by
/// [`evidence_key`]. The ordinary inference above deliberately skips explicit
/// params (declarations are trusted); this side-channel exists solely so
/// `--fix` can fill in `@param array<K, V>` value types — it is **never**
/// applied to the [`ReflectionIndex`] and cannot change analysis results.
pub type ExplicitParamEvidence = HashMap<(String, String, usize), Type>;

/// Canonical evidence-map key: lowercased, `\`-stripped function/class FQN,
/// lowercased method name (empty for free functions), parameter index.
pub fn evidence_key(
    class_or_fn: &str,
    method: Option<&str>,
    idx: usize,
) -> (String, String, usize) {
    (
        class_or_fn.trim_start_matches('\\').to_ascii_lowercase(),
        method.unwrap_or("").to_ascii_lowercase(),
        idx,
    )
}

/// Harvest [`ExplicitParamEvidence`] across `programs`. Same call-site walk as
/// parameter inference (skips builtins, spread/named/placeholder calls), but
/// selecting explicitly-typed bare-iterable params, and only recording evidence
/// that is useful and actually refines (no bare iterable left in the union).
pub fn explicit_iterable_param_evidence(
    index: &ReflectionIndex,
    programs: &[&Program],
    interner: &Interner,
) -> ExplicitParamEvidence {
    let per_file: Vec<(FnArgs, MethodArgs)> = programs
        .par_iter()
        .map(|program| harvest_file(index, program, interner))
        .collect();
    let mut fn_args: FnArgs = HashMap::new();
    let mut method_args: MethodArgs = HashMap::new();
    for (file_fns, file_methods) in per_file {
        for (fqn, positions) in file_fns {
            merge_positions(fn_args.entry(fqn).or_default(), positions);
        }
        for (key, positions) in file_methods {
            merge_positions(method_args.entry(key).or_default(), positions);
        }
    }

    let mut out = ExplicitParamEvidence::new();
    for (fqn, positions) in fn_args {
        let Some(f) = index.function(&fqn) else {
            continue;
        };
        if f.builtin {
            continue;
        }
        collect_explicit_iterable(&f.params, &positions, |idx, ty| {
            out.insert(evidence_key(&fqn, None, idx), ty);
        });
    }
    for ((class_fqn, mname), positions) in method_args {
        let Some(c) = index.class(&class_fqn) else {
            continue;
        };
        if c.builtin {
            continue;
        }
        let Some(m) = c
            .methods
            .iter()
            .find(|m| m.name.eq_ignore_ascii_case(&mname))
        else {
            continue;
        };
        collect_explicit_iterable(&m.params, &positions, |idx, ty| {
            out.insert(evidence_key(&class_fqn, Some(&mname), idx), ty);
        });
    }
    out
}

fn collect_explicit_iterable(
    params: &[ParamReflection],
    positions: &[Vec<Type>],
    mut record: impl FnMut(usize, Type),
) {
    for (i, p) in params.iter().enumerate() {
        if !p.explicit || p.variadic || !contains_bare_iterable(&p.ty) {
            continue;
        }
        let Some(observed) = positions.get(i) else {
            continue;
        };
        if observed.is_empty() {
            continue;
        }
        let u = Type::union(observed.iter().cloned().map(widen_literals).collect());
        if useful_inference(&u) && !contains_bare_iterable(&u) {
            record(i, u);
        }
    }
}

/// Whether `ty` contains a bare `array`/`iterable` (no key/value) anywhere.
fn contains_bare_iterable(ty: &Type) -> bool {
    let mut found = false;
    ty.clone().map(&mut |t| {
        if matches!(t, Type::Array(None) | Type::Iterable(None)) {
            found = true;
        }
        t
    });
    found
}

/// Collect one file's observed argument types per resolved call target.
fn harvest_file(
    index: &ReflectionIndex,
    program: &Program,
    interner: &Interner,
) -> (FnArgs, MethodArgs) {
    let mut fn_args: FnArgs = HashMap::new();
    let mut method_args: MethodArgs = HashMap::new();
    let map = type_map(index, program, interner, false);
    let refs = resolve_references(program, interner);
    let fmap = function_ref_map(&refs);
    walk::for_each_expr(program, &mut |e| match &e.kind {
        ExprKind::Call { callee, args } => {
            if let Some(fqn) = resolve_call_fqn(callee, &fmap, index) {
                record_args(&map, args, fn_args.entry(fqn).or_default());
            }
        }
        ExprKind::MethodCall {
            recv,
            method: MemberName::Ident(sym),
            args,
            ..
        } => {
            let recv_ty = type_of(&map, recv);
            if let Some(class_fqn) = named_fqn(&recv_ty) {
                let mname = interner.resolve(*sym);
                if let Some(found) = index.find_method(&class_fqn, mname) {
                    if !found.member.magic {
                        let key = (found.declaring_class.to_string(), found.member.name.clone());
                        record_args(&map, args, method_args.entry(key).or_default());
                    }
                }
            }
        }
        _ => {}
    });
    (fn_args, method_args)
}

/// Append one file's per-position observations onto the accumulated ones (in
/// file order, preserving the sequential pass's observation order exactly).
fn merge_positions(acc: &mut Vec<Vec<Type>>, file: Vec<Vec<Type>>) {
    for (i, observed) in file.into_iter().enumerate() {
        if acc.len() <= i {
            acc.resize(i + 1, Vec::new());
        }
        acc[i].extend(observed);
    }
}

/// Record each positional argument's type into the per-position accumulator.
/// Calls with spread/named/first-class-callable args break positional pairing
/// and are skipped wholesale.
fn record_args(map: &TypeMap, args: &[Arg], positions: &mut Vec<Vec<Type>>) {
    if args
        .iter()
        .any(|a| a.spread || a.placeholder || a.name.is_some())
    {
        return;
    }
    for (i, a) in args.iter().enumerate() {
        if positions.len() <= i {
            positions.resize(i + 1, Vec::new());
        }
        positions[i].push(type_of(map, &a.value));
    }
}

/// Build an inferred signature filling only untyped, non-variadic parameters from
/// the union of their observed argument types.
fn build_param_sig(params: &[ParamReflection], positions: &[Vec<Type>]) -> InferredSig {
    let params = params
        .iter()
        .enumerate()
        .map(|(i, p)| {
            if p.explicit || p.variadic {
                return None;
            }
            let observed = positions.get(i)?;
            if observed.is_empty() {
                return None;
            }
            // A parameter's type is the *general* type of the values passed, not the
            // specific literals observed — widen `'x'`→`string`, `7`→`int`, etc.
            let u = Type::union(observed.iter().cloned().map(widen_literals).collect());
            useful_inference(&u).then_some(u)
        })
        .collect();
    InferredSig { params, ret: None }
}

// --- helpers ----------------------------------------------------------------

/// A type precise enough to record: not `mixed`/unknown/`never`/`void`, and (for a
/// union) every member is itself useful — so a union that retained `mixed` from an
/// uncertain branch is rejected, falling back to the declared `mixed`.
pub fn useful_inference(ty: &Type) -> bool {
    match ty {
        Type::Mixed | Type::ExplicitMixed | Type::Never | Type::Void | Type::Unknown(_) => false,
        Type::Union(parts) => !parts.is_empty() && parts.iter().all(useful_inference),
        _ => true,
    }
}

/// Widen literal/singleton types to their base for parameter inference:
/// `'draft'`→`string`, `42`→`int`, `true`/`false`→`bool`.
pub fn widen_literals(ty: Type) -> Type {
    ty.map(&mut |part| match part {
        Type::LiteralInt(_) => Type::Int,
        Type::LiteralString(_) => Type::String,
        Type::True | Type::False => Type::Bool,
        other => other,
    })
}

/// The class FQN named by a type (through nullability), if any.
fn named_fqn(t: &Type) -> Option<String> {
    match t {
        Type::Named { fqn, .. } => Some(fqn.to_string()),
        Type::Nullable(inner) => named_fqn(inner),
        _ => None,
    }
}

fn type_of(map: &TypeMap, e: &Expr) -> Type {
    map.get(&php_span::NodeKey::of(e.span))
        .map(|f| f.merged.clone())
        .unwrap_or(Type::Mixed)
}

fn function_ref_map(refs: &[ResolvedRef]) -> HashMap<php_span::NodeKey, &ResolvedRef> {
    refs.iter()
        .filter(|r| r.kind == RefKind::Function)
        .map(|r| (php_span::NodeKey::of(r.span), r))
        .collect()
}

/// The resolved canonical function name for a call's callee, honouring the
/// global fallback (prefer the namespaced candidate when it exists).
fn resolve_call_fqn(
    callee: &Expr,
    fmap: &HashMap<php_span::NodeKey, &ResolvedRef>,
    index: &ReflectionIndex,
) -> Option<String> {
    let ExprKind::Name(n) = &callee.kind else {
        return None;
    };
    let r = fmap.get(&php_span::NodeKey::of(n.span))?;
    match &r.resolution {
        Resolution::Fqn(fqn) => Some(fqn.clone()),
        Resolution::Fallback { namespaced, global } => {
            if index.function(namespaced).is_some() {
                Some(namespaced.clone())
            } else {
                Some(global.clone())
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Parse `<?php` + `src`, index it, run signature inference, return the index.
    fn run(src: &str) -> ReflectionIndex {
        let full = format!("<?php {src}");
        let r = php_parser::parse(&full);
        assert!(!r.has_errors(), "parse errors in: {src}");
        let mut index = ReflectionIndex::with_builtins();
        index.add_file(&r.program, &r.interner);
        infer_and_apply(&mut index, &[&r.program], &r.interner, InferOpts::default());
        index
    }

    fn fret(idx: &ReflectionIndex, fqn: &str) -> String {
        idx.function(fqn).expect("function").return_type.to_string()
    }

    fn fparam(idx: &ReflectionIndex, fqn: &str, i: usize) -> String {
        idx.function(fqn).expect("function").params[i]
            .ty
            .to_string()
    }

    #[test]
    fn return_single() {
        let idx = run("function g() { return 42; }");
        assert_eq!(fret(&idx, "g"), "42");
        assert!(idx.function("g").unwrap().inferred_return);
    }

    #[test]
    fn bare_return_this_infers_static() {
        // `return $this;` is a late-static return: in a trait method it must not
        // bind to the trait, and in a class it must not lose subclass identity.
        let idx = run("trait T { public function chain() { return $this; } }");
        let m = idx.find_method("T", "chain").expect("method");
        assert_eq!(m.member.return_type.to_string(), "static");
    }

    #[test]
    fn return_union_of_branches() {
        let idx = run(r#"function g($c) { if ($c) { return 1; } return "x"; }"#);
        assert_eq!(fret(&idx, "g"), "1|'x'");
    }

    #[test]
    fn return_with_concat_is_string() {
        // The "!" side is provably non-empty, so the concat is too.
        let idx = run(r#"function g($x) { return $x . "!"; }"#);
        assert_eq!(fret(&idx, "g"), "non-empty-string");
    }

    #[test]
    fn param_from_call_site() {
        let idx = run(r#"function f($x) { return 1; } f("hello");"#);
        assert_eq!(fparam(&idx, "f", 0), "string");
        let p = &idx.function("f").unwrap().params[0];
        assert!(p.inferred);
        // native_ty and explicit are untouched — PHPDoc-grade.
        assert_eq!(p.native_ty, Type::Mixed);
        assert!(!p.explicit);
    }

    #[test]
    fn param_union_across_sites() {
        let idx = run(r#"function f($x) { return 1; } f("a"); f(7);"#);
        assert_eq!(fparam(&idx, "f", 0), "string|int");
    }

    #[test]
    fn param_flows_into_return() {
        let idx = run(r#"function g($x) { return $x; } g("hello");"#);
        assert_eq!(fparam(&idx, "g", 0), "string");
        assert_eq!(fret(&idx, "g"), "string");
    }

    #[test]
    fn cross_function_return_propagates() {
        let idx = run("function g() { return 7; } function h() { return g(); }");
        assert_eq!(fret(&idx, "g"), "7");
        assert_eq!(fret(&idx, "h"), "7");
    }

    #[test]
    fn generator_is_skipped() {
        let idx = run("function g() { yield 1; return 2; }");
        assert_eq!(fret(&idx, "g"), "mixed");
        assert!(!idx.function("g").unwrap().inferred_return);
    }

    #[test]
    fn unanalyzable_return_stays_mixed() {
        let idx = run("function g($x) { return $x; }");
        assert_eq!(fret(&idx, "g"), "mixed");
        assert!(!idx.function("g").unwrap().inferred_return);
    }

    #[test]
    fn explicit_types_are_not_overwritten() {
        let idx = run(r#"function f(int $x): string { return "y"; } f(5);"#);
        assert_eq!(fparam(&idx, "f", 0), "int");
        assert_eq!(fret(&idx, "f"), "string");
        assert!(!idx.function("f").unwrap().inferred_return);
        assert!(!idx.function("f").unwrap().params[0].inferred);
    }

    #[test]
    fn method_return_inferred() {
        let idx = run(r#"class C { function make() { return 5; } }
               function use_it(C $c) { return $c->make(); }"#);
        let found = idx.find_method("C", "make").expect("method make");
        assert_eq!(found.member.return_type.to_string(), "5");
        assert_eq!(fret(&idx, "use_it"), "5");
    }

    #[test]
    fn method_param_from_call_site() {
        let idx = run(r#"class C { function take($x) { return 1; } }
               function caller(C $c) { return $c->take("hi"); }"#);
        let found = idx.find_method("C", "take").expect("method take");
        assert_eq!(found.member.params[0].ty.to_string(), "string");
    }
}
