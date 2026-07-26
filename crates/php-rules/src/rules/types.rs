//! phpstan category **Types** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Types/` — 1 rule(s) at level(s) 0.
//! The rule set's coverage truth is `cargo run -p xtask -- rule-manifest`; for phpstan's behaviour read `phpstan-src/src/Rules/` directly. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented (level 0, purely syntactic — no inference):
//! - `unionType.<type>` / `nullableType.<type>` (`InvalidTypesInUnionRule`) — a
//!   native union/nullable typehint that contains one of the "standalone-only"
//!   types (`mixed`, `never`, `void`), which may not appear as a *member* of a
//!   union or nullable type declaration. Every native type annotation is
//!   visited: function/method params + returns, typed properties, closures,
//!   arrow functions, and property-hook params (incl. promoted ctor params).

#![allow(unused_imports)]
use crate::members;
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{
    ArrowFn, ClassDecl, ClosureExpr, Expr, ExprKind, FunctionDecl, Member, MemberName, MethodDecl,
    Param, PropertyHook, Stmt, StmtKind, Type, TypeKind,
};
use php_diagnostics::Diagnostic;
use php_resolve::{for_each_region, RefKind, Resolution, ResolvedRef, Scope};
use std::collections::HashMap;

/// The reserved keywords that may only appear *standalone*, never as a member of
/// a union or nullable type. Mirrors phpstan's `ONLY_STANDALONE_TYPES`.
const ONLY_STANDALONE_TYPES: &[&str] = &["mixed", "never", "void"];

/// If `t` is a bare type name (phpstan's `Identifier`) that is one of the
/// standalone-only keywords, return `(original_spelling, lowercased)`; else
/// `None`. phpstan reports the original spelling in the message and the
/// lowercased form in the identifier.
fn standalone_name(t: &Type) -> Option<(String, String)> {
    if let TypeKind::Simple(name) = &t.kind {
        let lower = name.text.to_ascii_lowercase();
        if ONLY_STANDALONE_TYPES.contains(&lower.as_str()) {
            return Some((name.text.clone(), lower));
        }
    }
    None
}

/// Inspect a single (outermost) type annotation. phpstan only looks at the
/// outermost `ComplexType` — a `UnionType` or a `NullableType` — and reports at
/// most one error per annotation (it returns on the first offending member).
fn check_type(t: &Type, out: &mut Vec<Diagnostic>) {
    match &t.kind {
        TypeKind::Union(members) => {
            for m in members {
                if let Some((orig, lower)) = standalone_name(m) {
                    out.push(
                        Diagnostic::error(
                            t.span,
                            format!("Type {orig} cannot be part of a union type declaration."),
                        )
                        .with_code(union_code(&lower)),
                    );
                    return;
                }
            }
        }
        TypeKind::Nullable(inner) => {
            if let Some((orig, lower)) = standalone_name(inner) {
                out.push(
                    Diagnostic::error(
                        t.span,
                        format!("Type {orig} cannot be part of a nullable type declaration."),
                    )
                    .with_code(nullable_code(&lower)),
                );
            }
        }
        // A bare `Simple` type or an `Intersection` is not flagged by this rule
        // (phpstan only inspects UnionType / NullableType).
        _ => {}
    }
}

/// `unionType.mixed` / `unionType.never` / `unionType.void`.
fn union_code(lower: &str) -> &'static str {
    match lower {
        "mixed" => "unionType.mixed",
        "never" => "unionType.never",
        "void" => "unionType.void",
        _ => "unionType",
    }
}

/// `nullableType.mixed` / `nullableType.never` / `nullableType.void`.
fn nullable_code(lower: &str) -> &'static str {
    match lower {
        "mixed" => "nullableType.mixed",
        "never" => "nullableType.never",
        "void" => "nullableType.void",
        _ => "nullableType",
    }
}

fn check_params(params: &[Param], out: &mut Vec<Diagnostic>) {
    for p in params {
        if let Some(ty) = &p.ty {
            check_type(ty, out);
        }
        // Hooks on a promoted property param carry their own param lists.
        for h in &p.hooks {
            check_hook(h, out);
        }
    }
}

fn check_hook(h: &PropertyHook, out: &mut Vec<Diagnostic>) {
    if let Some(params) = &h.params {
        check_params(params, out);
    }
}

fn check_function(f: &FunctionDecl, out: &mut Vec<Diagnostic>) {
    check_params(&f.params, out);
    if let Some(rt) = &f.return_type {
        check_type(rt, out);
    }
}

fn check_method(m: &MethodDecl, out: &mut Vec<Diagnostic>) {
    check_params(&m.params, out);
    if let Some(rt) = &m.return_type {
        check_type(rt, out);
    }
}

fn check_closure(c: &ClosureExpr, out: &mut Vec<Diagnostic>) {
    check_params(&c.params, out);
    if let Some(rt) = &c.return_type {
        check_type(rt, out);
    }
}

fn check_arrow(a: &ArrowFn, out: &mut Vec<Diagnostic>) {
    check_params(&a.params, out);
    if let Some(rt) = &a.return_type {
        check_type(rt, out);
    }
}

fn check_class(c: &ClassDecl, out: &mut Vec<Diagnostic>) {
    for m in &c.members {
        match m {
            Member::Method(md) => check_method(md, out),
            Member::Property(pd) => {
                if let Some(ty) = &pd.ty {
                    check_type(ty, out);
                }
                for el in &pd.props {
                    if let Some(hooks) = &el.hooks {
                        for h in hooks {
                            check_hook(h, out);
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// `InvalidTypesInUnionRule` — `mixed`/`never`/`void` used inside a union or
/// nullable native type declaration.
fn run_invalid_types_in_union(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();

    // Named function and class declarations (incl. nested ones — `for_each_stmt`
    // visits every statement in the file).
    walk::for_each_stmt(fa.program, &mut |s| match &s.kind {
        StmtKind::Function(f) => check_function(f, &mut out),
        StmtKind::Class(c) => check_class(c, &mut out),
        _ => {}
    });

    // Closures, arrow functions, and anonymous classes live in expression
    // position.
    walk::for_each_expr(fa.program, &mut |e| match &e.kind {
        ExprKind::Closure(c) => check_closure(c, &mut out),
        ExprKind::ArrowFn(a) => check_arrow(a, &mut out),
        ExprKind::NewAnon { class, .. } => check_class(class, &mut out),
        _ => {}
    });

    out
}

fn run_explicit_mixed_strictness(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.check_explicit_mixed {
        return Vec::new();
    }
    run_strict_mixed(fa, true, false)
}

fn run_implicit_mixed_strictness(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.check_implicit_mixed {
        return Vec::new();
    }
    run_strict_mixed(fa, false, true)
}

fn run_strict_mixed(
    fa: &FileAnalysis,
    include_explicit: bool,
    include_implicit: bool,
) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    check_function_call_mixed(fa, include_explicit, include_implicit, &mut out);
    check_method_call_mixed(fa, include_explicit, include_implicit, &mut out);
    check_return_mixed(fa, include_explicit, include_implicit, &mut out);
    check_member_access_mixed(fa, include_explicit, include_implicit, &mut out);
    out
}

/// Whether a member-access receiver *is* mixed. Unlike [`strict_mixed_source`]
/// this is a top-level test: `Collection<mixed, mixed>` or `array<int, mixed>`
/// merely *contain* mixed in a type argument — calling/indexing on them is
/// fine, and phpstan does not report it. Unions stay unreported (conservative).
fn receiver_is_mixed(ty: &php_types::Type, include_explicit: bool, include_implicit: bool) -> bool {
    match ty {
        php_types::Type::ExplicitMixed => include_explicit,
        php_types::Type::Mixed => include_implicit,
        _ => false,
    }
}

fn reflected_function_target(fa: &FileAnalysis, r: &ResolvedRef) -> Option<String> {
    match &r.resolution {
        Resolution::Fqn(fqn) => fa.reflection.function(fqn).map(|_| fqn.clone()),
        Resolution::Fallback { namespaced, global } => {
            if fa.reflection.function(namespaced).is_some() {
                Some(namespaced.clone())
            } else {
                fa.reflection.function(global).map(|_| global.clone())
            }
        }
        _ => None,
    }
}

fn check_function_call_mixed(
    fa: &FileAnalysis,
    include_explicit: bool,
    include_implicit: bool,
    out: &mut Vec<Diagnostic>,
) {
    let fmap = members::function_refs(fa.resolved_refs);
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        let Some(fqn) = reflected_function_target(fa, r) else {
            return;
        };
        let Some(func) = fa.reflection.function(&fqn) else {
            return;
        };
        if func.builtin && !func.params.iter().any(|p| p.variadic) && args.len() > func.params.len()
        {
            return;
        }
        let display = r.name.trim_start_matches('\\');
        for (i, arg) in args.iter().enumerate() {
            let Some(param) = func.params.get(i) else {
                break;
            };
            // A variadic absorbs every remaining argument, so stop. But a
            // parameter whose target is not concrete only means *this* argument
            // cannot be judged — `break` here silently disabled checking of every
            // LATER parameter (e.g. `is_callable`'s `callable|mixed` first param
            // hid its `string` third param).
            if param.variadic {
                break;
            }
            if !crate::compat::concrete_target(&param.ty) {
                continue;
            }
            let given = fa.type_of(&arg.value);
            if crate::compat::mixed_violates_target(
                &given,
                &param.ty,
                include_explicit,
                include_implicit,
            ) {
                out.push(
                    Diagnostic::error(
                        arg.value.span,
                        format!(
                            "Parameter #{} ${} of function {display} expects {}, mixed given.",
                            i + 1,
                            param.name,
                            param.ty
                        ),
                    )
                    .with_code("argument.type"),
                );
            }
        }
    });
}

fn check_method_call_mixed(
    fa: &FileAnalysis,
    include_explicit: bool,
    include_implicit: bool,
    out: &mut Vec<Diagnostic>,
) {
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::MethodCall {
            recv, method, args, ..
        } = &e.kind
        else {
            return;
        };
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        let Some(fqn) = named_fqn(&fa.type_of(recv)) else {
            return;
        };
        let MemberName::Ident(name) = method else {
            return;
        };
        let mname = fa.interner.resolve(*name);
        let Some(found) = fa.reflection.find_method(&fqn, mname) else {
            return;
        };
        if found.member.magic {
            return;
        }
        let short = fqn.trim_start_matches('\\');
        for (i, arg) in args.iter().enumerate() {
            let Some(param) = found.member.params.get(i) else {
                break;
            };
            // A variadic absorbs every remaining argument, so stop. But a
            // parameter whose target is not concrete only means *this* argument
            // cannot be judged — `break` here silently disabled checking of every
            // LATER parameter (e.g. `is_callable`'s `callable|mixed` first param
            // hid its `string` third param).
            if param.variadic {
                break;
            }
            if !crate::compat::concrete_target(&param.ty) {
                continue;
            }
            let given = fa.type_of(&arg.value);
            if crate::compat::mixed_violates_target(
                &given,
                &param.ty,
                include_explicit,
                include_implicit,
            ) {
                out.push(
                    Diagnostic::error(
                        arg.value.span,
                        format!(
                            "Parameter #{} ${} of method {short}::{mname}() expects {}, mixed given.",
                            i + 1,
                            param.name,
                            param.ty
                        ),
                    )
                    .with_code("argument.type"),
                );
            }
        }
    });
}

fn named_fqn(ty: &php_types::Type) -> Option<String> {
    match ty {
        php_types::Type::Named { fqn, .. } => Some(fqn.to_string()),
        php_types::Type::Nullable(inner) => named_fqn(inner),
        _ => None,
    }
}

fn check_return_mixed(
    fa: &FileAnalysis,
    include_explicit: bool,
    include_implicit: bool,
    out: &mut Vec<Diagnostic>,
) {
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            collect_return_scopes(fa, scope, st, include_explicit, include_implicit, out);
        }
    });
}

fn collect_return_scopes(
    fa: &FileAnalysis,
    scope: &Scope,
    st: &php_ast::Stmt,
    include_explicit: bool,
    include_implicit: bool,
    out: &mut Vec<Diagnostic>,
) {
    match &st.kind {
        StmtKind::Function(f) => {
            let refl = fa.reflect_function(scope, f);
            if crate::compat::concrete_target(&refl.return_type) {
                for s in &f.body {
                    check_return_stmts(
                        fa,
                        &format!("function {}()", refl.fqn),
                        &refl.return_type,
                        s,
                        include_explicit,
                        include_implicit,
                        out,
                    );
                }
            }
        }
        StmtKind::Class(c) => {
            let Some(name) = c.name else { return };
            let fqn = scope.qualify(fa.interner.resolve(name));
            let cls = fa.reflect_class(scope, &fqn, c);
            for m in &c.members {
                let Member::Method(md) = m else { continue };
                let Some(body) = &md.body else { continue };
                let mname = fa.interner.resolve(md.name);
                let Some(mr) = cls
                    .methods
                    .iter()
                    .find(|x| !x.magic && x.name.eq_ignore_ascii_case(mname))
                else {
                    continue;
                };
                if !crate::compat::concrete_target(&mr.return_type) {
                    continue;
                }
                for s in body {
                    check_return_stmts(
                        fa,
                        &format!("{fqn}::{}()", mr.name),
                        &mr.return_type,
                        s,
                        include_explicit,
                        include_implicit,
                        out,
                    );
                }
            }
        }
        _ => {}
    }
}

fn check_return_stmts(
    fa: &FileAnalysis,
    label: &str,
    target: &php_types::Type,
    st: &Stmt,
    include_explicit: bool,
    include_implicit: bool,
    out: &mut Vec<Diagnostic>,
) {
    match &st.kind {
        StmtKind::Return(Some(value)) => {
            let given = fa.type_of(value);
            if crate::compat::mixed_violates_target(
                &given,
                target,
                include_explicit,
                include_implicit,
            ) {
                out.push(
                    Diagnostic::error(
                        value.span,
                        format!("{label} should return {target} but returns mixed."),
                    )
                    .with_code("return.type"),
                );
            }
        }
        StmtKind::Block(body) => {
            for s in body {
                check_return_stmts(fa, label, target, s, include_explicit, include_implicit, out);
            }
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            check_return_stmts(fa, label, target, then, include_explicit, include_implicit, out);
            for elseif in elseifs {
                check_return_stmts(
                    fa,
                    label,
                    target,
                    &elseif.body,
                    include_explicit,
                    include_implicit,
                    out,
                );
            }
            if let Some(els) = els {
                check_return_stmts(fa, label, target, els, include_explicit, include_implicit, out);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. }
        | StmtKind::Declare {
            body: Some(body), ..
        } => check_return_stmts(fa, label, target, body, include_explicit, include_implicit, out),
        StmtKind::Switch { cases, .. } => {
            for case in cases {
                for s in &case.body {
                    check_return_stmts(fa, label, target, s, include_explicit, include_implicit, out);
                }
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for s in body {
                check_return_stmts(fa, label, target, s, include_explicit, include_implicit, out);
            }
            for catch in catches {
                for s in &catch.body {
                    check_return_stmts(fa, label, target, s, include_explicit, include_implicit, out);
                }
            }
            if let Some(finally) = finally {
                for s in finally {
                    check_return_stmts(fa, label, target, s, include_explicit, include_implicit, out);
                }
            }
        }
        StmtKind::Function(_) | StmtKind::Class(_) => {}
        _ => {}
    }
}

fn check_member_access_mixed(
    fa: &FileAnalysis,
    include_explicit: bool,
    include_implicit: bool,
    out: &mut Vec<Diagnostic>,
) {
    walk::for_each_expr(fa.program, &mut |e| match &e.kind {
        ExprKind::MethodCall { recv, method, .. } => {
            if !receiver_is_mixed(&fa.type_of(recv), include_explicit, include_implicit) {
                return;
            }
            let MemberName::Ident(name) = method else {
                return;
            };
            let mname = fa.interner.resolve(*name);
            out.push(
                Diagnostic::error(e.span, format!("Cannot call method {mname}() on mixed."))
                    .with_code("method.nonObject"),
            );
        }
        ExprKind::Prop { base, name, .. } => {
            if !receiver_is_mixed(&fa.type_of(base), include_explicit, include_implicit) {
                return;
            }
            let MemberName::Ident(name) = name else {
                return;
            };
            let pname = fa.interner.resolve(*name);
            out.push(
                Diagnostic::error(e.span, format!("Cannot access property ${pname} on mixed."))
                    .with_code("property.nonObject"),
            );
        }
        ExprKind::Index { base, index } => {
            if !receiver_is_mixed(&fa.type_of(base), include_explicit, include_implicit) {
                return;
            }
            let message = if let Some(index) = index {
                let dim_ty = fa.type_of(index);
                format!("Cannot access offset {dim_ty} on mixed.")
            } else {
                "Cannot access an offset on mixed.".to_string()
            };
            out.push(
                Diagnostic::error(e.span, message).with_code("offsetAccess.nonOffsetAccessible"),
            );
        }
        _ => {}
    });
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "types.invalidTypesInUnion",
        level: 0,
        run: run_invalid_types_in_union,
    },
    // Registered at level 0 but gated entirely on the `checkExplicitMixed` /
    // `checkImplicitMixed` switches (which default to level 9 / max via
    // `RuleOptions`, so default runs are unchanged). Scheduling them at every
    // level is what lets the config overrides enable strict-mixed checking
    // independently of level — phpstan's semantics.
    RuleEntry {
        name: "types.explicitMixedStrictness",
        level: 0,
        run: run_explicit_mixed_strictness,
    },
    RuleEntry {
        name: "types.implicitMixedStrictness",
        level: 0,
        run: run_implicit_mixed_strictness,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- strict-mixed argument reporting ------------------------------------

    /// A target that itself **accepts** `mixed` must never yield a
    /// "mixed given" report — `is_callable(callable|mixed)` did exactly that,
    /// 22 times on the Zend corpus.
    #[test]
    fn a_mixed_accepting_target_is_never_reported() {
        // `is_callable`'s first parameter is `callable|mixed`: anything fits.
        let src = "<?php function f($x) { is_callable($x); }";
        assert!(
            codes(src, run_implicit_mixed_strictness).is_empty(),
            "reported against a target that accepts mixed: {:?}",
            codes(src, run_implicit_mixed_strictness)
        );
    }

    /// A parameter whose target is not concrete means *that argument* cannot be
    /// judged — it must not stop the loop. The old `break` let a `mixed` first
    /// parameter hide every later one (`in_array`'s `array` haystack,
    /// `json_encode`'s `int` flags).
    #[test]
    fn a_non_concrete_parameter_does_not_hide_later_ones() {
        // `in_array(mixed $needle, array $haystack)` — #1 is unjudgeable, #2 is not.
        let src = "<?php function f($x) { in_array('a', $x); }";
        assert_eq!(
            codes(src, run_implicit_mixed_strictness),
            ["argument.type"],
            "the array haystack should still be checked"
        );

        // `json_encode(mixed $value, int $flags)` — same shape.
        let src = "<?php function f($x) { json_encode([1], $x); }";
        assert_eq!(codes(src, run_implicit_mixed_strictness), ["argument.type"]);
    }

    /// Level gating, which the harness previously masked by forcing every
    /// strictness switch on: implicit-mixed checks exist only at `max`, explicit
    /// ones from level 9.
    #[test]
    fn strict_mixed_rules_respect_their_levels() {
        use crate::testutil::codes_at_level;
        let implicit = "<?php function f($x) { strlen($x); }";
        for level in [0, 7, 8, 9] {
            assert!(
                codes_at_level(implicit, run_implicit_mixed_strictness, level).is_empty(),
                "implicit-mixed must not fire at level {level}"
            );
        }
        assert_eq!(
            codes_at_level(implicit, run_implicit_mixed_strictness, 10),
            ["argument.type"]
        );

        let explicit = "<?php /** @param mixed $x */ function f($x) { strlen($x); }";
        for level in [0, 7, 8] {
            assert!(
                codes_at_level(explicit, run_explicit_mixed_strictness, level).is_empty(),
                "explicit-mixed must not fire at level {level}"
            );
        }
        assert_eq!(
            codes_at_level(explicit, run_explicit_mixed_strictness, 9),
            ["argument.type"]
        );
    }

    /// The discriminating pair, end to end through the rule.
    ///
    /// A `mixed` written in a docblock is **explicit** mixed, so these go through
    /// `run_explicit_mixed_strictness`; the engine runs both strictness rules at
    /// max level. Measured on the corpus: testing *containment* reports 54
    /// findings where the target constrains nothing, while testing only the *top
    /// level* loses 65 real ones where it does.
    #[test]
    fn nested_mixed_reports_only_where_the_target_constrains_it() {
        // `count(array|Countable)` — the `array` arm pins no value type.
        let unconstrained = "<?php /** @param array<int, mixed> $a */\n\
                             function f(array $a) { count($a); }";
        assert!(
            codes(unconstrained, run_explicit_mixed_strictness).is_empty(),
            "an unconstrained value position must not be reported: {:?}",
            codes(unconstrained, run_explicit_mixed_strictness)
        );

        // `str_replace($search)` wants `array<int|string, string>` — the mixed
        // value type genuinely violates it.
        let constrained = "<?php /** @param array<int, mixed> $a */\n\
                           function f(array $a) { str_replace($a, 'a', 'b'); }";
        assert_eq!(
            codes(constrained, run_explicit_mixed_strictness),
            ["argument.type"],
            "a constrained value position must still be reported"
        );

        // A plainly `mixed` argument against a concrete target still reports.
        let top_level = "<?php function f($x) { strlen($x); }";
        assert_eq!(
            codes(top_level, run_implicit_mixed_strictness),
            ["argument.type"]
        );
    }

    // --- union types ---------------------------------------------------------

    #[test]
    fn void_in_union_return_is_flagged() {
        assert_eq!(
            codes(
                "<?php function f(): int|void {}",
                run_invalid_types_in_union
            ),
            ["unionType.void"]
        );
    }

    #[test]
    fn never_in_union_param_is_flagged() {
        assert_eq!(
            codes(
                "<?php function f(int|never $x) {}",
                run_invalid_types_in_union
            ),
            ["unionType.never"]
        );
    }

    #[test]
    fn mixed_in_union_is_flagged() {
        assert_eq!(
            codes(
                "<?php function f(): int|mixed {}",
                run_invalid_types_in_union
            ),
            ["unionType.mixed"]
        );
    }

    // --- nullable types ------------------------------------------------------

    #[test]
    fn nullable_void_is_flagged() {
        assert_eq!(
            codes("<?php function f(): ?void {}", run_invalid_types_in_union),
            ["nullableType.void"]
        );
    }

    #[test]
    fn nullable_never_is_flagged() {
        assert_eq!(
            codes("<?php function f(?never $x) {}", run_invalid_types_in_union),
            ["nullableType.never"]
        );
    }

    // --- negatives -----------------------------------------------------------

    #[test]
    fn standalone_void_return_is_ok() {
        assert!(codes("<?php function f(): void {}", run_invalid_types_in_union).is_empty());
    }

    #[test]
    fn standalone_never_return_is_ok() {
        assert!(codes(
            "<?php function f(): never { throw new E(); }",
            run_invalid_types_in_union
        )
        .is_empty());
    }

    #[test]
    fn ordinary_union_is_ok() {
        assert!(codes(
            "<?php function f(): int|string|null {}",
            run_invalid_types_in_union
        )
        .is_empty());
    }

    #[test]
    fn ordinary_nullable_is_ok() {
        assert!(codes("<?php function f(): ?int {}", run_invalid_types_in_union).is_empty());
    }

    #[test]
    fn case_insensitive() {
        assert_eq!(
            codes(
                "<?php function f(): int|VOID {}",
                run_invalid_types_in_union
            ),
            ["unionType.void"]
        );
    }

    // --- coverage of every declaration site ----------------------------------

    #[test]
    fn method_return_in_union_is_flagged() {
        assert_eq!(
            codes(
                "<?php class C { function m(): int|void {} }",
                run_invalid_types_in_union
            ),
            ["unionType.void"]
        );
    }

    #[test]
    fn typed_property_in_union_is_flagged() {
        assert_eq!(
            codes(
                "<?php class C { public int|void $p; }",
                run_invalid_types_in_union
            ),
            ["unionType.void"]
        );
    }

    #[test]
    fn closure_param_in_union_is_flagged() {
        assert_eq!(
            codes(
                "<?php $f = function (int|never $x) {};",
                run_invalid_types_in_union
            ),
            ["unionType.never"]
        );
    }

    #[test]
    fn arrow_fn_return_in_union_is_flagged() {
        assert_eq!(
            codes(
                "<?php $f = fn (): int|void => 1;",
                run_invalid_types_in_union
            ),
            ["unionType.void"]
        );
    }

    #[test]
    fn anon_class_method_in_union_is_flagged() {
        assert_eq!(
            codes(
                "<?php $o = new class { function m(): int|void {} };",
                run_invalid_types_in_union
            ),
            ["unionType.void"]
        );
    }

    #[test]
    fn nested_function_is_flagged() {
        assert_eq!(
            codes(
                "<?php function outer() { function inner(): int|void {} }",
                run_invalid_types_in_union
            ),
            ["unionType.void"]
        );
    }

    #[test]
    fn promoted_ctor_param_in_union_is_flagged() {
        assert_eq!(
            codes(
                "<?php class C { public function __construct(public int|void $x) {} }",
                run_invalid_types_in_union
            ),
            ["unionType.void"]
        );
    }

    #[test]
    fn no_types_no_diagnostics() {
        assert!(codes(
            "<?php function f($a) { return $a; }",
            run_invalid_types_in_union
        )
        .is_empty());
    }

    // --- strict mixed --------------------------------------------------------

    #[test]
    fn explicit_mixed_argument_is_flagged_at_level_9_strictness() {
        let src =
            "<?php function takesInt(int $i): void {} function f(mixed $x): void { takesInt($x); }";
        assert_eq!(codes(src, run_explicit_mixed_strictness), ["argument.type"]);
    }

    #[test]
    fn implicit_mixed_argument_waits_for_level_10_strictness() {
        let src = "<?php function takesInt(int $i): void {} function f($x): void { takesInt($x); }";
        assert!(codes(src, run_explicit_mixed_strictness).is_empty());
        assert_eq!(codes(src, run_implicit_mixed_strictness), ["argument.type"]);
    }

    #[test]
    fn explicit_mixed_return_to_concrete_type_is_flagged() {
        let src = "<?php function f(mixed $x): int { return $x; }";
        assert_eq!(codes(src, run_explicit_mixed_strictness), ["return.type"]);
    }

    #[test]
    fn generic_receiver_with_mixed_args_is_not_a_mixed_receiver() {
        // The receiver IS a Collection — it merely has `mixed` in its generic
        // arguments (the unbound-template case, e.g. Laravel's `collect($x)`).
        // phpstan does not report member access on it; neither must we.
        let src = r#"<?php
class Collection { /** @return static */ public function filter(callable $cb) { return $this; } }
/**
 * @template TKey of array-key
 * @template TValue
 * @param iterable<TKey, TValue>|null $value
 * @return Collection<TKey, TValue>
 */
function collect($value = []) { return new Collection(); }
function f(mixed $x): void { collect($x)->filter(fn ($v) => $v !== false); }
"#;
        assert!(
            !codes(src, run_explicit_mixed_strictness).contains(&"method.nonObject"),
            "Collection<mixed, mixed> receiver must not count as mixed"
        );
        assert!(!codes(src, run_implicit_mixed_strictness).contains(&"method.nonObject"));
    }

    #[test]
    fn array_of_mixed_values_is_not_a_mixed_offset_receiver() {
        // `array<int, mixed>` is offset-accessible; only the VALUE is mixed.
        // (Accessing an offset on that mixed value is a different expression.)
        let src = r#"<?php
/** @param array<int, mixed> $rows */
function f(array $rows): void { $x = $rows[0]; }
"#;
        assert!(!codes(src, run_implicit_mixed_strictness)
            .contains(&"offsetAccess.nonOffsetAccessible"));
    }

    #[test]
    fn explicit_mixed_method_access_is_flagged() {
        let src = "<?php function f(mixed $x): void { $x->foo(); }";
        assert_eq!(
            codes(src, run_explicit_mixed_strictness),
            ["method.nonObject"]
        );
    }

    #[test]
    fn explicit_mixed_property_and_offset_access_are_flagged() {
        let src = "<?php function f(mixed $x): void { echo $x->p; echo $x['k']; }";
        let codes = codes(src, run_explicit_mixed_strictness);
        assert!(codes.contains(&"property.nonObject"));
        assert!(codes.contains(&"offsetAccess.nonOffsetAccessible"));
    }
}
