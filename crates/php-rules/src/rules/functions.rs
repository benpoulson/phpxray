//! phpstan category **Functions** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Functions/` — 41 rule(s) at level(s) 0–6.
//! The rule set's coverage truth is `cargo run -p xtask -- rule-manifest`; for phpstan's behaviour read `phpstan-src/src/Rules/` directly. Add each rule as a `RuleEntry` to `RULES`
//! (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented here (besides the pre-existing `return-type`):
//! - `parameter.duplicate` (`RedefinedParametersRule`) — a parameter name reused
//!   in the same signature.
//! - `parameter.this` / `parameter.superglobal` (`InvalidParameterNameRule`) —
//!   `$this` or a superglobal used as a parameter.
//! - `parameter.variadicNotLast` (`VariadicParametersDeclarationRule`) — a
//!   variadic parameter that isn't the last one.
//! - `function.inner` (`InnerFunctionRule`) — a named function declared inside
//!   another function/method/closure.
//! - `closure.useThis` / `closure.useSuperGlobal` / `closure.useDuplicate`
//!   (`InvalidLexicalVariablesInClosureUseRule`) — bad closure `use (...)` vars.
//! - `closure.unusedUse` (`UnusedClosureUsesRule`) — a closure `use ($x)` never
//!   referenced in the body.
//! - `function.notFound` (`CallToNonExistentFunctionRule`) — a call to a function
//!   that exists neither in the project nor in the built-in stubs.
//! - `function.nameCase` (`CallToNonExistentFunctionRule`) — a call whose case
//!   differs from the declared/built-in casing.
//! - `return.type` / `return.empty` / `return.void` / `return.never`
//!   (`ClosureReturnTypeRule`, `ArrowFunctionReturnTypeRule`, conservative
//!   subsets) — explicit native closure/arrow return types checked against
//!   empty returns and known simple return expressions.
//! - `function.resultDiscarded` / `function.inVoidCast` and
//!   `callable.resultDiscarded` / `callable.inVoidCast`
//!   (`CallToFunctionStatementWithNoDiscardRule`) — PHP 8.5 `#[NoDiscard]`
//!   calls and unnecessary `(void)` casts.
//! - `argument.sprintf` / `argument.printf` (`PrintfParametersRule`) — wrong
//!   number of values for the placeholders in a constant format string.
//! - `argument.unused` (`DefineParametersRule`) — the removed 3rd argument to
//!   `define()`.
//! - `arguments.count` (`CallToFunctionParametersRule`, count-only subset) — too
//!   few required / too many positional args to a known function (no type check).
//! - `callable.nonCallable` (`FunctionCallableRule`, subset) — `Foo::class(...)`
//!   first-class-callable on a non-existent function.
//!
//! Deferred (need expression *type* inference):
//! - `CallToFunctionParametersRule` (argument TYPE checking) — only the count
//!   subset is done here.
//! - `CallCallablesRule`, `CallUserFuncRule`, `RandomIntParametersRule`,
//!   `ArrayValuesRule`, `ArrayFilterRule`, `FilterVarRule`, `ImplodeParameter*`,
//!   `Parameter*CastableTo*`, `SortParameter*`, `PrintfParameterType*`,
//!   `Incompatible*DefaultParameterTypeRule`, `UselessFunctionReturnValueRule`,
//!   closure/arrow callable NoDiscard metadata propagation,
//!   `CallToFunctionStatementWithoutSideEffectsRule`, `ReturnNullsafeByRefRule`,
//!   `MissingFunctionParameter/ReturnTypehintRule`, `ExistingClassesIn*Typehints`
//!   (latter handled by unknown-symbol resolution) — all need the type system.

use crate::{
    compat, function_like,
    members::{self, CallResolver, ResolveStatus},
    return_type_errors, FileAnalysis, RuleEntry,
};
use php_ast::{
    BinOp, CastKind, ClassDecl, ClosureExpr, Expr, ExprKind, HookBody, Member, Param, Stmt,
    StmtKind,
};
use php_diagnostics::Diagnostic;
use php_intern::{Interner, Symbol};
use php_resolve::{for_each_region, Resolution, ResolvedRef, Scope};
use php_types::Type;
use std::collections::{HashMap, HashSet};

fn run_return_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    return_type_errors(
        fa.reflection,
        fa.program,
        fa.interner,
        fa.types,
        fa.treat_phpdoc_types_as_certain,
        fa.check_nullables,
        fa.report_maybes,
        fa.collect_fixes.then_some(fa.source),
    )
}

/// First-class callables (`f(...)`, `$o->m(...)`, `C::m(...)`) are only valid on
/// PHP 8.1+. Mirrors the version gate of phpstan's `FunctionCallableRule`,
/// `MethodCallableRule`, and `StaticMethodCallableRule` (`callable.notSupported`).
/// Gated on `fa.php_version` (default 8.4 → silent). The existence half of those
/// rules is handled by the shared `function.notFound`/`method.notFound`/
/// `staticMethod.notFound` rules, which walk these call nodes regardless of the
/// first-class-callable placeholder.
fn run_first_class_callable_version(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if fa.php_version.at_least(80100) {
        return Vec::new();
    }
    let mut out = Vec::new();
    for call in fa.facts.function_calls() {
        if call.args.iter().any(|a| a.placeholder) {
            out.push(
                Diagnostic::error(
                    call.expr.span,
                    "First-class callables are supported only on PHP 8.1 and later.".to_string(),
                )
                .with_code("callable.notSupported"),
            );
        }
    }
    for call in fa.facts.method_calls() {
        if call.args.iter().any(|a| a.placeholder) {
            out.push(
                Diagnostic::error(
                    call.expr.span,
                    "First-class callables are supported only on PHP 8.1 and later.".to_string(),
                )
                .with_code("callable.notSupported"),
            );
        }
    }
    for call in fa.facts.static_calls() {
        if call.args.iter().any(|a| a.placeholder) {
            out.push(
                Diagnostic::error(
                    call.expr.span,
                    "First-class callables are supported only on PHP 8.1 and later.".to_string(),
                )
                .with_code("callable.notSupported"),
            );
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Parameter-name rules (operate on every FunctionLike's params)
// ---------------------------------------------------------------------------

/// Visit every parameter list in the file (functions, methods, closures, arrow
/// fns, anonymous classes' methods), passing the params slice to `f`.
fn for_each_param_list<F: FnMut(&[Param])>(program: &php_ast::Program, mut f: F) {
    crate::walk::for_each_stmt(program, &mut |s| {
        if let StmtKind::Function(fd) = &s.kind {
            f(&fd.params);
        }
        if let StmtKind::Class(c) = &s.kind {
            for m in &c.members {
                if let Member::Method(md) = m {
                    f(&md.params);
                }
            }
        }
    });
    crate::walk::for_each_expr(program, &mut |e| match &e.kind {
        ExprKind::Closure(c) => f(&c.params),
        ExprKind::ArrowFn(a) => f(&a.params),
        ExprKind::NewAnon { class, .. } => {
            for m in &class.members {
                if let Member::Method(md) = m {
                    f(&md.params);
                }
            }
        }
        _ => {}
    });
}

/// `RedefinedParametersRule` — a parameter name used more than once in the same
/// signature (`function f($a, $a)`).
fn run_redefined_parameters(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_param_list(fa.program, |params| {
        if params.len() <= 1 {
            return;
        }
        let mut seen: HashSet<Symbol> = HashSet::new();
        for p in params {
            if !seen.insert(p.name) {
                let name = fa.interner.resolve(p.name);
                out.push(
                    Diagnostic::error(p_span(p), format!("Redefinition of parameter ${name}."))
                        .with_code("parameter.duplicate"),
                );
            }
        }
    });
    out
}

/// `InvalidParameterNameRule` — `$this` and superglobals cannot be parameters.
fn run_invalid_parameter_name(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_param_list(fa.program, |params| {
        for p in params {
            let name = fa.interner.resolve(p.name);
            if crate::symbols::SUPERGLOBALS.contains(&name) {
                out.push(
                    Diagnostic::error(
                        p_span(p),
                        format!("Superglobal variable ${name} cannot be used as a parameter."),
                    )
                    .with_code("parameter.superglobal"),
                );
            } else if name == "this" {
                out.push(
                    Diagnostic::error(p_span(p), "Cannot use $this as parameter.".to_string())
                        .with_code("parameter.this"),
                );
            }
        }
    });
    out
}

/// `VariadicParametersDeclarationRule` — only the last parameter may be variadic.
fn run_variadic_parameters(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_param_list(fa.program, |params| {
        if params.is_empty() {
            return;
        }
        let last = params.len() - 1;
        for (i, p) in params.iter().enumerate() {
            if p.variadic && i != last {
                out.push(
                    Diagnostic::error(
                        p_span(p),
                        "Only the last parameter can be variadic.".to_string(),
                    )
                    .with_code("parameter.variadicNotLast"),
                );
            }
        }
    });
    out
}

/// If `ty` (a resolved param/return/property type) is a bare `array`/`iterable`
/// with no value type — including through nullability and unions — the iterable
/// word to report. The substrate of phpstan's `missingType.iterableValue` checks.
pub(crate) fn bare_iterable_word(ty: &php_types::Type) -> Option<&'static str> {
    crate::missing_type::type_iterable_word(ty)
}

pub(crate) fn p_span(p: &Param) -> php_span::Span {
    p.span
}

// ---------------------------------------------------------------------------
// Inner named functions
// ---------------------------------------------------------------------------

/// `InnerFunctionRule` — a named function declared inside another function-like
/// scope (function/method/closure/arrow-fn body). phpstan does not support these.
fn run_inner_function(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for s in &fa.program.stmts {
        inner_stmt(s, false, &mut out);
    }
    out
}

/// Recursively walk statements tracking `in_fn` — whether we are inside a
/// function-like scope (function / method / closure / arrow-fn body). A named
/// `Function` declaration found while `in_fn` is flagged. Entering any
/// function-like body sets `in_fn = true` for its contents. A `class`
/// declaration's methods are members, not inner functions: each method body is
/// its own function scope, so they re-enter with `in_fn = true` regardless.
fn inner_stmt(s: &Stmt, in_fn: bool, out: &mut Vec<Diagnostic>) {
    match &s.kind {
        StmtKind::Function(fd) => {
            if in_fn {
                out.push(
                    Diagnostic::error(
                        s.span,
                        "Inner named functions are not supported by PHPStan. Consider refactoring \
                         to an anonymous function, class method, or a top-level-defined function."
                            .to_string(),
                    )
                    .with_code("function.inner"),
                );
            }
            inner_params(&fd.params, out);
            for st in &fd.body {
                inner_stmt(st, true, out);
            }
        }
        StmtKind::Class(c) => {
            for m in &c.members {
                if let Member::Method(md) = m {
                    inner_params(&md.params, out);
                    if let Some(body) = &md.body {
                        for st in body {
                            inner_stmt(st, true, out);
                        }
                    }
                }
            }
        }
        StmtKind::Block(b) => b.iter().for_each(|st| inner_stmt(st, in_fn, out)),
        StmtKind::Namespace { body: Some(b), .. } => {
            b.iter().for_each(|st| inner_stmt(st, in_fn, out));
        }
        StmtKind::If {
            cond,
            then,
            elseifs,
            els,
        } => {
            inner_expr(cond, in_fn, out);
            inner_stmt(then, in_fn, out);
            for ei in elseifs {
                inner_expr(&ei.cond, in_fn, out);
                inner_stmt(&ei.body, in_fn, out);
            }
            if let Some(e) = els {
                inner_stmt(e, in_fn, out);
            }
        }
        StmtKind::While { cond, body } => {
            inner_expr(cond, in_fn, out);
            inner_stmt(body, in_fn, out);
        }
        StmtKind::DoWhile { body, cond } => {
            inner_stmt(body, in_fn, out);
            inner_expr(cond, in_fn, out);
        }
        StmtKind::For {
            init,
            cond,
            update,
            body,
        } => {
            for e in init.iter().chain(cond).chain(update) {
                inner_expr(e, in_fn, out);
            }
            inner_stmt(body, in_fn, out);
        }
        StmtKind::Foreach { subject, body, .. } => {
            inner_expr(subject, in_fn, out);
            inner_stmt(body, in_fn, out);
        }
        StmtKind::Switch { subject, cases } => {
            inner_expr(subject, in_fn, out);
            for c in cases {
                if let Some(t) = &c.test {
                    inner_expr(t, in_fn, out);
                }
                c.body.iter().for_each(|st| inner_stmt(st, in_fn, out));
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter().for_each(|st| inner_stmt(st, in_fn, out));
            for c in catches {
                c.body.iter().for_each(|st| inner_stmt(st, in_fn, out));
            }
            if let Some(f) = finally {
                f.iter().for_each(|st| inner_stmt(st, in_fn, out));
            }
        }
        StmtKind::Declare { body: Some(b), .. } => inner_stmt(b, in_fn, out),
        StmtKind::Expr(e) => inner_expr(e, in_fn, out),
        StmtKind::Return(Some(e)) => inner_expr(e, in_fn, out),
        StmtKind::Echo(es) => es.iter().for_each(|e| inner_expr(e, in_fn, out)),
        _ => {}
    }
}

/// Descend into an expression, finding the function scopes it opens (closures /
/// arrow fns / anon-class methods) and recursing into their bodies with
/// `in_fn = true`. We collect only the *outermost* such scopes here (the
/// recursion into their bodies via `inner_stmt`/`inner_expr` handles deeper
/// nesting), so no node is visited twice.
fn inner_expr(e: &Expr, _in_fn: bool, out: &mut Vec<Diagnostic>) {
    let mut scopes: Vec<&Expr> = Vec::new();
    collect_outermost_scopes(e, &mut scopes);
    for sc in scopes {
        match &sc.kind {
            ExprKind::Closure(c) => {
                inner_params(&c.params, out);
                for st in &c.body {
                    inner_stmt(st, true, out);
                }
            }
            ExprKind::ArrowFn(a) => {
                inner_params(&a.params, out);
                inner_expr(&a.body, true, out);
            }
            ExprKind::NewAnon { class, .. } => {
                for m in &class.members {
                    if let Member::Method(md) = m {
                        inner_params(&md.params, out);
                        if let Some(body) = &md.body {
                            for st in body {
                                inner_stmt(st, true, out);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// Collect the outermost closure / arrow-fn / anon-class expressions reachable
/// from `e` without descending past one. Reuses the lexical traversal shape from
/// `keywords::collect_closures` but lives here to keep this module self-contained.
fn collect_outermost_scopes<'a>(e: &'a Expr, found: &mut Vec<&'a Expr>) {
    use ExprKind::*;
    match &e.kind {
        Closure(_) | ArrowFn(_) | NewAnon { .. } => found.push(e),
        Interpolated(parts) | ShellExec(parts) | Isset(parts) => {
            parts
                .iter()
                .for_each(|p| collect_outermost_scopes(p, found));
        }
        VariableVariable(x) | DollarBrace(x) => collect_outermost_scopes(x, found),
        Array { items, .. } => {
            for it in items {
                if let Some(k) = &it.key {
                    collect_outermost_scopes(k, found);
                }
                if let Some(v) = &it.value {
                    collect_outermost_scopes(v, found);
                }
            }
        }
        Call { callee, args } => {
            collect_outermost_scopes(callee, found);
            args.iter()
                .for_each(|a| collect_outermost_scopes(&a.value, found));
        }
        MethodCall { recv, args, .. } => {
            collect_outermost_scopes(recv, found);
            args.iter()
                .for_each(|a| collect_outermost_scopes(&a.value, found));
        }
        StaticCall { class, args, .. } => {
            collect_outermost_scopes(class, found);
            args.iter()
                .for_each(|a| collect_outermost_scopes(&a.value, found));
        }
        New { class, args } => {
            collect_outermost_scopes(class, found);
            args.iter()
                .for_each(|a| collect_outermost_scopes(&a.value, found));
        }
        Index { base, index } => {
            collect_outermost_scopes(base, found);
            if let Some(i) = index {
                collect_outermost_scopes(i, found);
            }
        }
        Prop { base, .. } => collect_outermost_scopes(base, found),
        StaticProp { class, .. } | ClassConst { class, .. } => {
            collect_outermost_scopes(class, found)
        }
        Unary { expr, .. } | Cast { expr, .. } => collect_outermost_scopes(expr, found),
        Binary { lhs, rhs, .. }
        | Assign { target: lhs, rhs }
        | AssignOp {
            target: lhs, rhs, ..
        }
        | AssignRef { target: lhs, rhs }
        | Coalesce { lhs, rhs } => {
            collect_outermost_scopes(lhs, found);
            collect_outermost_scopes(rhs, found);
        }
        Ternary { cond, then, els } => {
            collect_outermost_scopes(cond, found);
            if let Some(t) = then {
                collect_outermost_scopes(t, found);
            }
            collect_outermost_scopes(els, found);
        }
        PreInc(x) | PreDec(x) | PostInc(x) | PostDec(x) => collect_outermost_scopes(x, found),
        Instanceof { expr, class } => {
            collect_outermost_scopes(expr, found);
            collect_outermost_scopes(class, found);
        }
        Clone(x) | Print(x) | Throw(x) | ErrorSuppress(x) | YieldFrom(x) | Eval(x) | Empty(x) => {
            collect_outermost_scopes(x, found)
        }
        Yield { key, value } => {
            if let Some(k) = key {
                collect_outermost_scopes(k, found);
            }
            if let Some(v) = value {
                collect_outermost_scopes(v, found);
            }
        }
        Exit(Some(x)) => collect_outermost_scopes(x, found),
        Match { subject, arms } => {
            collect_outermost_scopes(subject, found);
            for arm in arms {
                if let Some(conds) = &arm.conds {
                    conds
                        .iter()
                        .for_each(|c| collect_outermost_scopes(c, found));
                }
                collect_outermost_scopes(&arm.body, found);
            }
        }
        Include { expr, .. } => collect_outermost_scopes(expr, found),
        Paren(x) => collect_outermost_scopes(x, found),
        _ => {}
    }
}

fn inner_params(params: &[Param], out: &mut Vec<Diagnostic>) {
    for p in params {
        if let Some(d) = &p.default {
            inner_expr(d, false, out);
        }
    }
}

// ---------------------------------------------------------------------------
// Closure `use (...)` rules
// ---------------------------------------------------------------------------

/// `InvalidLexicalVariablesInClosureUseRule` — `use ($this)`, `use ($_GET)`, or a
/// `use` var that collides with a parameter name.
fn run_invalid_lexical_use(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for e in fa.facts.expressions() {
        let ExprKind::Closure(c) = &e.kind else {
            continue;
        };
        let param_names: HashSet<&str> = c
            .params
            .iter()
            .map(|p| fa.interner.resolve(p.name))
            .collect();
        for u in &c.uses {
            let name = fa.interner.resolve(u.name);
            if name == "this" {
                out.push(
                    Diagnostic::error(e.span, "Cannot use $this as lexical variable.".to_string())
                        .with_code("closure.useThis"),
                );
            } else if crate::symbols::SUPERGLOBALS.contains(&name) {
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!("Cannot use superglobal variable ${name} as lexical variable."),
                    )
                    .with_code("closure.useSuperGlobal"),
                );
            } else if param_names.contains(name) {
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!(
                            "Cannot use lexical variable ${name} since a parameter with the same name already exists."
                        ),
                    )
                    .with_code("closure.useDuplicate"),
                );
            }
        }
    }
    out
}

/// `UnusedClosureUsesRule` — a `use ($x)` that the closure body never reads. A
/// by-reference use (`use (&$x)`) is always allowed (it writes back out). We
/// gather every `$var` mentioned anywhere in the body (conservative: any read or
/// write counts as "used", matching phpstan's variable-usage check closely
/// enough for a syntactic pass).
fn run_unused_closure_uses(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Closure(c) = &e.kind else {
            return;
        };
        if c.uses.is_empty() {
            return;
        }
        let used = collect_used_variables(c, fa.interner);
        let unused: Vec<php_intern::Symbol> = c
            .uses
            .iter()
            .filter(|u| !u.by_ref && !used.contains(fa.interner.resolve(u.name)))
            .map(|u| u.name)
            .collect();
        for u in &c.uses {
            if u.by_ref {
                continue; // by-ref use is never "unused" — it exports a value.
            }
            let name = fa.interner.resolve(u.name);
            if !used.contains(name) {
                let mut d = Diagnostic::error(
                    e.span,
                    format!("Anonymous function has an unused use ${name}."),
                )
                .with_code("closure.unusedUse");
                // `--fix`: delete the capture (the whole clause when every
                // capture is unused).
                if fa.collect_fixes {
                    if let Some(fix) =
                        crate::fix::closure_use_removal_fix(fa, e.span, c, u.name, &unused)
                    {
                        d = d.with_fix(fix);
                    }
                }
                out.push(d);
            }
        }
    });
    out
}

/// Every variable name referenced inside a closure's body (and nested closures'
/// own `use` lists / bodies, since a captured var can be passed down).
fn collect_used_variables(c: &ClosureExpr, interner: &Interner) -> HashSet<String> {
    let mut names: HashSet<String> = HashSet::new();
    for st in &c.body {
        crate::walk::for_each_expr_in_scope(st, &mut |e| match &e.kind {
            ExprKind::Variable(sym) => {
                names.insert(interner.resolve(*sym).to_string());
            }
            // Nested closures forward captures via their own `use` list, but a
            // bare variable reference inside the nested body belongs to that
            // nested scope and must not make the outer `use` look used.
            ExprKind::Closure(inner) => {
                for u in &inner.uses {
                    names.insert(interner.resolve(u.name).to_string());
                }
            }
            // Arrow fns auto-capture: every variable referenced in their body
            // (transitively through further arrow fns) is a use of this scope.
            ExprKind::ArrowFn(inner) => {
                collect_arrow_captured(&inner.body, interner, &mut names);
            }
            _ => {}
        });
    }
    names
}

/// Variables an arrow-fn body references from its enclosing scope: bare
/// variables (auto-capture), nested closures' `use` lists, and nested arrow
/// bodies recursively. Over-approximates (the arrow's own params count too),
/// which only makes an outer `use` look used — the safe direction.
fn collect_arrow_captured(body: &Expr, interner: &Interner, names: &mut HashSet<String>) {
    crate::walk::for_each_subexpr(body, &mut |e| match &e.kind {
        ExprKind::Variable(sym) => {
            names.insert(interner.resolve(*sym).to_string());
        }
        ExprKind::Closure(inner) => {
            for u in &inner.uses {
                names.insert(interner.resolve(u.name).to_string());
            }
        }
        ExprKind::ArrowFn(inner) => collect_arrow_captured(&inner.body, interner, names),
        _ => {}
    });
}

// ---------------------------------------------------------------------------
// Call-site rules (resolve the callee name via resolved_refs)
// ---------------------------------------------------------------------------

/// Look up a function in the project/builtins honouring the global fallback, and
/// return its canonical (declared) name if found.
/// `CallToNonExistentFunctionRule` (the `function.notFound` half — `nameCase` is
/// a separate rule below). A call `foo(...)` where `foo` resolves to neither a
/// project function nor a built-in.
fn run_call_to_non_existent_function(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let resolver = CallResolver::new(fa);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, .. } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        if matches!(resolver.function(r), ResolveStatus::Unknown) {
            let display = members::primary_name(r);
            out.push(
                Diagnostic::error(r.span, format!("Function {display} not found."))
                    .with_code("function.notFound"),
            );
        }
    });
    out
}

/// `CallToNonExistentFunctionRule` (the `function.nameCase` half). A call whose
/// spelling case-insensitively matches a known function but differs in case.
fn run_function_name_case(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let resolver = CallResolver::new(fa);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, .. } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        let ResolveStatus::Known(target) = resolver.function(r) else {
            return;
        };
        if target
            .canonical_fqn
            .eq_ignore_ascii_case(&target.called_fqn)
            && target.canonical_fqn != target.called_fqn
        {
            out.push(
                Diagnostic::error(
                    r.span,
                    format!(
                        "Call to function {}() with incorrect case: {}",
                        target.canonical_fqn, target.display_name
                    ),
                )
                .with_code("function.nameCase"),
            );
        }
    });
    out
}

/// The actual known function target for a resolved call. For PHP's unqualified
/// namespaced fallback, prefer the namespaced function when the project defines
/// it; only fall back to the global symbol when the namespaced candidate is
/// absent. Built-in-specific rules must use this instead of blindly inspecting
/// the fallback's global candidate.
fn known_function_target<'a>(fa: &FileAnalysis, r: &'a ResolvedRef) -> Option<&'a str> {
    CallResolver::new(fa).known_function_fqn(r)
}

/// The unqualified lowercase tail of the actual known function target.
fn function_tail_lower(fa: &FileAnalysis, r: &ResolvedRef) -> Option<String> {
    let candidate = known_function_target(fa, r)?;
    let tail = candidate.rsplit('\\').next().unwrap_or(candidate);
    Some(tail.to_ascii_lowercase())
}

/// `DefineParametersRule` — `define('X', $v, true)` passes the removed 3rd
/// `$case_insensitive` argument (case-insensitive constants gone since PHP 8.0).
fn run_define_parameters(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        // `define` is a global function with no namespace; only match the global.
        if function_tail_lower(fa, r).as_deref() != Some("define")
            || !is_global_function(fa, r, "define")
        {
            return;
        }
        if args.iter().any(|a| a.spread || a.placeholder) {
            return;
        }
        if args.len() >= 3 {
            out.push(
                Diagnostic::error(
                    e.span,
                    "Argument #3 ($case_insensitive) is ignored since declaration of \
                     case-insensitive constants is no longer supported."
                        .to_string(),
                )
                .with_code("argument.unused"),
            );
        }
    });
    out
}

/// `CallCallablesRule` (`callable.nonCallable`, subset) — invoking a value that
/// is definitely not callable, e.g. `$n = 5; $n();`. Conservative: only fires for
/// concrete non-callable scalars (`int`/`float`/`bool`/`null`), never for
/// `string`/`array`/objects (which *can* be callables) or `mixed`/unknown.
fn run_invoke_non_callable(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        // A named call (`foo()`) is a function reference, not a value invocation;
        // `f(...)` is a first-class-callable, not an invocation.
        if matches!(callee.kind, ExprKind::Name(_)) || args.iter().any(|a| a.placeholder) {
            return;
        }
        let t = fa.type_of(callee);
        if is_definitely_not_callable(&t) {
            out.push(
                Diagnostic::error(
                    e.span,
                    format!("Trying to invoke {t} but it's not a callable."),
                )
                .with_code("callable.nonCallable"),
            );
        }
    });
    out
}

fn run_invoke_maybe_non_callable(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        if matches!(callee.kind, ExprKind::Name(_)) || args.iter().any(|a| a.placeholder) {
            return;
        }
        let t = fa.type_of(callee);
        if is_maybe_callable(&t) {
            out.push(
                Diagnostic::error(
                    e.span,
                    format!("Trying to invoke {t} but it might not be a callable."),
                )
                .with_code("callable.nonCallable"),
            );
        }
    });
    out
}

fn is_maybe_callable(t: &php_types::Type) -> bool {
    let php_types::Type::Union(parts) = t else {
        return false;
    };
    if parts.is_empty() {
        return false;
    }
    let mut callable = false;
    let mut non_callable = false;
    for part in parts.iter() {
        if is_definitely_callable(part) {
            callable = true;
        } else if is_definitely_not_callable(part) {
            non_callable = true;
        } else {
            return false;
        }
    }
    callable && non_callable
}

fn is_definitely_callable(t: &php_types::Type) -> bool {
    matches!(t, php_types::Type::Callable(_))
}

fn is_definitely_not_callable(t: &php_types::Type) -> bool {
    use php_types::Type::*;
    matches!(
        t,
        Int | Float | Bool | True | False | Null | LiteralInt(_) | Void | Never
    )
}

/// `ImplodeParameterCastableToStringRule` — `implode`/`join`'s array argument
/// must have elements castable to string. Uses the type map (`fa.type_of`) +
/// `is_castable_to_string`; only fires when the element type is concrete and
/// definitely not stringable (arrays of arrays, etc.) — false-positive-safe.
fn run_implode_castable(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        let Some(tail) = function_tail_lower(fa, r) else {
            return;
        };
        if !matches!(tail.as_str(), "implode" | "join") || !is_global_function(fa, r, &tail) {
            return;
        }
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        // PHP 8: `implode($separator, $array)` or `implode($array)`. The array is
        // the last positional argument.
        let (idx, label) = match args.len() {
            1 => (0usize, "#1 $array"),
            2 => (1usize, "#2 $array"),
            _ => return,
        };
        let arr_ty = fa.type_of(&args[idx].value);
        let elem = match &arr_ty {
            php_types::Type::Array(Some(kv)) => kv.1.clone(),
            php_types::Type::List(v) => (**v).clone(),
            _ => return, // unknown / non-array element type — leave to argument.type.
        };
        if !crate::is_castable_to_string(fa.reflection, &elem) {
            out.push(
                Diagnostic::error(
                    e.span,
                    format!(
                        "Parameter {label} of function {} expects array<string>, {arr_ty} given.",
                        tail
                    ),
                )
                .with_code("argument.type"),
            );
        }
    });
    out
}

/// `PrintfParametersRule` (count subset). For `printf`/`sprintf` with a constant
/// (single literal) format string, count the conversion specifiers and compare
/// to the number of value args. We only handle a literal format operand (no type
/// inference), and `printf`/`sprintf` (not `sscanf`/`fscanf`, which need runtime
/// `sscanf`).
fn run_printf_parameters(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        let Some(tail) = function_tail_lower(fa, r) else {
            return;
        };
        let (name, code): (&str, &'static str) = match tail.as_str() {
            "printf" => ("printf", "argument.printf"),
            "sprintf" => ("sprintf", "argument.sprintf"),
            _ => return,
        };
        if !is_global_function(fa, r, name) {
            return;
        }
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return; // unpacking / named args: count is indeterminate.
        }
        // Format is the first argument; need at least it.
        if args.is_empty() {
            return; // too few — caught by the arg-count rule.
        }
        let Some(fmt) = literal_string(&args[0].value) else {
            return;
        };
        let Some(placeholders) = printf_placeholder_count(&fmt) else {
            out.push(
                Diagnostic::error(
                    e.span,
                    format!("Call to {name} contains an invalid placeholder."),
                )
                .with_code(code),
            );
            return;
        };
        // Values supplied (all args after the format).
        let values = args.len() - 1;
        if values != placeholders {
            let ph_word = if placeholders == 1 {
                "placeholder"
            } else {
                "placeholders"
            };
            let val_word = if values == 1 {
                "value given"
            } else {
                "values given"
            };
            out.push(
                Diagnostic::error(
                    e.span,
                    format!(
                        "Call to {name} contains {placeholders} {ph_word}, {values} {val_word}."
                    ),
                )
                .with_code(code),
            );
        }
    });
    out
}

/// The literal byte string value of an expression iff it's a single string
/// literal (no interpolation). Returns it lossily as UTF-8 (format specifiers
/// are ASCII).
fn literal_string(e: &Expr) -> Option<String> {
    match &e.kind {
        ExprKind::Str(bytes) => Some(String::from_utf8_lossy(bytes).into_owned()),
        ExprKind::Paren(inner) => literal_string(inner),
        _ => None,
    }
}

/// Count the printf-style conversion placeholders in a format string. Mirrors
/// `PrintfHelper`: a `%%` is a literal percent (skipped); a valid placeholder is
/// `%` optional `N$`, flags, width, precision, then a specifier from the printf
/// set. Positional (`%1$s`) placeholders count toward the max position. Returns
/// `None` if a `%` is not followed by a valid specifier (invalid placeholder).
fn printf_placeholder_count(format: &str) -> Option<usize> {
    let bytes = format.as_bytes();
    let mut i = 0;
    let mut auto_index = 0usize; // next implicit argument index (0-based)
    let mut max_position = 0usize; // highest argument index used + 1
    let n = bytes.len();
    while i < n {
        if bytes[i] != b'%' {
            i += 1;
            continue;
        }
        // `%%` is a literal percent.
        if i + 1 < n && bytes[i + 1] == b'%' {
            i += 2;
            continue;
        }
        i += 1; // consume '%'
                // Positional: digits followed by '$'.
        let mut position: Option<usize> = None;
        let start = i;
        while i < n && bytes[i].is_ascii_digit() {
            i += 1;
        }
        if i < n && bytes[i] == b'$' && i > start {
            let num: usize = format[start..i].parse().ok()?;
            position = Some(num);
            i += 1; // consume '$'
        } else {
            i = start; // not positional — rewind, this was width/flags
        }
        // Flags: -, +, space, 0, or '<char> (custom pad).
        while i < n {
            match bytes[i] {
                b'-' | b'+' | b' ' | b'0' => i += 1,
                b'\'' if i + 1 < n => i += 2, // custom padding char
                _ => break,
            }
        }
        // Width: digits or '*'.
        while i < n && bytes[i].is_ascii_digit() {
            i += 1;
        }
        // Precision: '.' then digits.
        if i < n && bytes[i] == b'.' {
            i += 1;
            while i < n && bytes[i].is_ascii_digit() {
                i += 1;
            }
        }
        // Specifier.
        if i >= n {
            return None; // dangling '%'
        }
        let spec = bytes[i];
        // Allow an `l` length modifier before c/d/etc per phpstan's `l?` group.
        let spec = if spec == b'l' && i + 1 < n {
            i += 1;
            bytes[i]
        } else {
            spec
        };
        const VALID: &[u8] = b"bcdeEgfFGosuxX";
        if !VALID.contains(&spec) {
            return None;
        }
        i += 1;
        // Account for this placeholder's argument index.
        match position {
            Some(p) => max_position = max_position.max(p),
            None => {
                auto_index += 1;
                max_position = max_position.max(auto_index);
            }
        }
    }
    Some(max_position)
}

// ---------------------------------------------------------------------------
// Argument count vs reflection (CallToFunctionParametersRule, count subset)
// ---------------------------------------------------------------------------

/// `CallToFunctionParametersRule` (argument-COUNT subset; no type checks). For a
/// call to a known *user* function (reflected with a real signature), flag too
/// few required arguments or too many positional arguments. We only check
/// functions present in the reflection index (project sources) — built-in stubs
/// are names-only, so their arities aren't reflected.
fn run_argument_count(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        // Spread/first-class-callable/named args: count is indeterminate or N/A.
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        let fqn = match &r.resolution {
            Resolution::Fqn(fqn) => fqn.clone(),
            Resolution::Fallback { namespaced, global } => {
                if fa.reflection.function(namespaced).is_some() {
                    namespaced.clone()
                } else {
                    global.clone()
                }
            }
            _ => return,
        };
        let Some(func) = fa.reflection.function(&fqn) else {
            return;
        };
        // Built-in stub arity is unreliable (phpstorm-stubs omits defaults on some
        // optional params and mis-counts variadics — phpstan uses a curated
        // functionMap instead). Only check user-defined functions for arity.
        if func.builtin {
            return;
        }
        let supplied = args.len();
        let variadic = func.params.iter().any(|p| p.variadic);
        let required = func
            .params
            .iter()
            .filter(|p| !p.optional && !p.variadic)
            .count();
        let max = func.params.len();
        let display = members::primary_name(r);

        let too_many = !variadic
            && supplied > max
            // A body reading `func_get_args()` legitimately takes extras.
            && !fa
                .reflection
                .function_body(&fqn)
                .is_some_and(|(body, _)| crate::function_like::body_reads_variadic_args(body));
        if supplied < required || too_many {
            let phrase = crate::function_like::invoked_with(supplied, required, max, variadic);
            out.push(
                Diagnostic::error(e.span, format!("Function {display} {phrase}."))
                    .with_code("arguments.count"),
            );
        }
    });
    out
}

/// `CallToFunctionParametersRule` (the argument-**type** half). Each positional
/// argument is checked against the matching parameter's type via the type map +
/// assignability. Lenient: unknown callee, `mixed`/unresolved arg or param types
/// produce no diagnostic.
fn run_argument_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        // Positional, fully-spelled-out calls only (named/spread/first-class break
        // positional pairing).
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        let fqn = match &r.resolution {
            Resolution::Fqn(fqn) => fqn.clone(),
            Resolution::Fallback { namespaced, global } => {
                if fa.reflection.function(namespaced).is_some() {
                    namespaced.clone()
                } else {
                    global.clone()
                }
            }
            _ => return,
        };
        let Some(func) = fa.reflection.function(&fqn) else {
            return;
        };
        let callee = crate::function_like::ResolvedCallable::function(
            &members::primary_name(r),
            &func.params,
            func.builtin,
        );
        crate::function_like::check_call_args(
            args,
            &callee,
            &|e| fa.type_of(e),
            &|e, t, nt| fa.accepts(e, t, nt),
            &mut out,
        );
    });
    out
}

// ---------------------------------------------------------------------------
// First-class-callable on a non-existent function
// ---------------------------------------------------------------------------

/// `FunctionCallableRule` (the `function.notFound` subset for `foo(...)`). A
/// first-class-callable `foo(...)` where `foo` doesn't exist. Type-based
/// callable checks are deferred.
fn run_function_callable(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let resolver = CallResolver::new(fa);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        // First-class-callable form: a single `...` placeholder argument.
        if args.len() != 1 || !args[0].placeholder {
            return;
        }
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        if matches!(resolver.function(r), ResolveStatus::Unknown) {
            out.push(
                Diagnostic::error(
                    r.span,
                    format!("Function {} not found.", members::primary_name(r)),
                )
                .with_code("function.notFound"),
            );
        }
    });
    out
}

// ---------------------------------------------------------------------------
// vprintf / vsprintf — array placeholder count (PrintfArrayParametersRule)
// ---------------------------------------------------------------------------

/// `PrintfArrayParametersRule` — for `vprintf`/`vsprintf` with a constant format
/// string and a constant array of values, check the placeholder count against the
/// array's size. We only handle a literal format and a literal `array(...)` of
/// values (no spread/named); otherwise the size is indeterminate and we skip.
fn run_printf_array_parameters(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        let Some(tail) = function_tail_lower(fa, r) else {
            return;
        };
        let name = match tail.as_str() {
            "vprintf" => "vprintf",
            "vsprintf" => "vsprintf",
            _ => return,
        };
        if !is_global_function(fa, r, name) {
            return;
        }
        let code = if name == "vprintf" {
            "argument.vprintf"
        } else {
            "argument.vsprintf"
        };
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        if args.is_empty() {
            return; // too few — caught by arg-count.
        }
        let Some(fmt) = literal_string(&args[0].value) else {
            return;
        };
        let Some(placeholders) = printf_placeholder_count(&fmt) else {
            out.push(
                Diagnostic::error(
                    e.span,
                    format!("Call to {name} contains an invalid placeholder."),
                )
                .with_code(code),
            );
            return;
        };
        // The values array is the 2nd argument; only a literal array gives a size.
        let Some(values_arg) = args.get(1) else {
            // No second arg: 0 values.
            if placeholders != 0 {
                out.push(printf_array_diag(e.span, name, placeholders, 0, code));
            }
            return;
        };
        let Some(size) = literal_array_size(&values_arg.value) else {
            return;
        };
        if size != placeholders {
            out.push(printf_array_diag(e.span, name, placeholders, size, code));
        }
    });
    out
}

fn printf_array_diag(
    span: php_span::Span,
    name: &str,
    placeholders: usize,
    values: usize,
    code: &'static str,
) -> Diagnostic {
    let ph_word = if placeholders == 1 {
        "placeholder"
    } else {
        "placeholders"
    };
    let val_word = if values == 1 {
        "value given"
    } else {
        "values given"
    };
    Diagnostic::error(
        span,
        format!("Call to {name} contains {placeholders} {ph_word}, {values} {val_word}."),
    )
    .with_code(code)
}

/// The element count of a literal `array(...)` / `[...]` expression iff every
/// item is a plain (non-spread) value; `None` for non-array or spread-bearing.
fn literal_array_size(e: &Expr) -> Option<usize> {
    match &e.kind {
        ExprKind::Array { items, .. } => {
            if items.iter().any(|it| it.spread || it.value.is_none()) {
                return None;
            }
            Some(items.len())
        }
        ExprKind::Paren(inner) => literal_array_size(inner),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Duplicate function declaration (DuplicateFunctionDeclarationRule)
// ---------------------------------------------------------------------------

/// `DuplicateFunctionDeclarationRule` — a function name declared more than once.
/// phpstan checks this project-wide; we check within a single file (a safe subset:
/// re-declaring a function in one file is always a fatal error). Function names
/// are case-insensitive. Reported once, on the second+ declaration.
fn run_duplicate_function(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    // Only top-level / namespace-region functions are real declarations; inner
    // functions are conditionally defined and handled by `function.inner`.
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for s in region {
            collect_top_functions(scope, s, &mut seen, fa, &mut out);
        }
    });
    out
}

fn collect_top_functions(
    scope: &Scope,
    s: &Stmt,
    seen: &mut HashSet<String>,
    fa: &FileAnalysis,
    out: &mut Vec<Diagnostic>,
) {
    match &s.kind {
        StmtKind::Function(fd) => {
            let display = scope.qualify(fa.interner.resolve(fd.name));
            let name = display.to_ascii_lowercase();
            if !seen.insert(name) {
                out.push(
                    Diagnostic::error(
                        s.span,
                        format!("Function {display}() declared multiple times."),
                    )
                    .with_code("function.duplicate"),
                );
            }
        }
        StmtKind::Namespace { body: Some(b), .. } => {
            for st in b {
                collect_top_functions(scope, st, seen, fa, out);
            }
        }
        StmtKind::Block(b) => {
            for st in b {
                collect_top_functions(scope, st, seen, fa, out);
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Nullsafe returned by reference (ReturnNullsafeByRefRule / arrow-fn variant)
// ---------------------------------------------------------------------------

/// Does `e` "contain" a nullsafe access in the by-ref-return sense? Mirrors
/// `NullsafeCheck::containsNullSafe`: a nullsafe prop/method directly, or one
/// reached through ordinary (non-nullsafe) member access / array index / list.
fn contains_nullsafe(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Prop { nullsafe: true, .. } | ExprKind::MethodCall { nullsafe: true, .. } => true,
        ExprKind::Index { base, .. } => contains_nullsafe(base),
        ExprKind::Prop {
            base,
            nullsafe: false,
            ..
        } => contains_nullsafe(base),
        ExprKind::MethodCall {
            recv,
            nullsafe: false,
            ..
        } => contains_nullsafe(recv),
        ExprKind::StaticProp { class, .. } | ExprKind::StaticCall { class, .. } => {
            contains_nullsafe(class)
        }
        ExprKind::Array { items, .. } => items.iter().any(|it| {
            it.key.as_ref().is_some_and(contains_nullsafe)
                || it.value.as_ref().is_some_and(contains_nullsafe)
        }),
        ExprKind::Paren(inner) => contains_nullsafe(inner),
        _ => false,
    }
}

/// `ReturnNullsafeByRefRule` — a by-reference function/method (`function &f()`)
/// that `return`s a nullsafe expression. Nullsafe chains can short-circuit to
/// `null`, which has no reference.
fn run_return_nullsafe_by_ref(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::Function(fd) = &s.kind {
            if fd.by_ref {
                check_returns_for_nullsafe(&fd.body, &mut out);
            }
        }
        if let StmtKind::Class(c) = &s.kind {
            for m in &c.members {
                if let Member::Method(md) = m {
                    if md.by_ref {
                        if let Some(body) = &md.body {
                            check_returns_for_nullsafe(body, &mut out);
                        }
                    }
                }
            }
        }
    });
    // Closures declared `function &() {}`.
    crate::walk::for_each_expr(fa.program, &mut |e| {
        if let ExprKind::Closure(c) = &e.kind {
            if c.by_ref {
                check_returns_for_nullsafe(&c.body, &mut out);
            }
        }
    });
    out
}

/// Walk a function body's `return`s (not descending into nested function-likes,
/// which have their own return scope) and flag nullsafe operands.
fn check_returns_for_nullsafe(body: &[Stmt], out: &mut Vec<Diagnostic>) {
    for s in body {
        returns_in_stmt(s, out);
    }
}

fn returns_in_stmt(s: &Stmt, out: &mut Vec<Diagnostic>) {
    match &s.kind {
        StmtKind::Return(Some(e)) => {
            if contains_nullsafe(e) {
                out.push(
                    Diagnostic::error(
                        e.span,
                        "Nullsafe cannot be returned by reference.".to_string(),
                    )
                    .with_code("nullsafe.byRef"),
                );
            }
        }
        StmtKind::Block(b) => b.iter().for_each(|st| returns_in_stmt(st, out)),
        StmtKind::Namespace { body: Some(b), .. } => {
            b.iter().for_each(|st| returns_in_stmt(st, out))
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            returns_in_stmt(then, out);
            for ei in elseifs {
                returns_in_stmt(&ei.body, out);
            }
            if let Some(e) = els {
                returns_in_stmt(e, out);
            }
        }
        StmtKind::While { body, .. } | StmtKind::DoWhile { body, .. } => returns_in_stmt(body, out),
        StmtKind::For { body, .. } | StmtKind::Foreach { body, .. } => returns_in_stmt(body, out),
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                c.body.iter().for_each(|st| returns_in_stmt(st, out));
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter().for_each(|st| returns_in_stmt(st, out));
            for c in catches {
                c.body.iter().for_each(|st| returns_in_stmt(st, out));
            }
            if let Some(f) = finally {
                f.iter().for_each(|st| returns_in_stmt(st, out));
            }
        }
        StmtKind::Declare { body: Some(b), .. } => returns_in_stmt(b, out),
        // Do NOT descend into nested Function/Class declarations — their returns
        // belong to a different (possibly non-by-ref) scope.
        _ => {}
    }
}

/// `ArrowFunctionReturnNullsafeByRefRule` — a by-reference arrow function
/// (`fn &() => ...`) whose body expression is a nullsafe access.
fn run_arrow_nullsafe_by_ref(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::ArrowFn(a) = &e.kind else {
            return;
        };
        if a.by_ref && contains_nullsafe(&a.body) {
            out.push(
                Diagnostic::error(
                    a.body.span,
                    "Nullsafe cannot be returned by reference.".to_string(),
                )
                .with_code("nullsafe.byRef"),
            );
        }
    });
    out
}

// ---------------------------------------------------------------------------
// Closure / arrow return type rules (level 3)
// ---------------------------------------------------------------------------

/// `ClosureReturnTypeRule` — conservative subset for explicit native closure
/// return types. We check empty returns, explicit `void`/`never`, and known
/// simple return expressions. Dynamic returns stay silent until closure body
/// type-map support is deeper.
fn run_closure_return_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Closure(c) = &e.kind else {
            return;
        };
        let Some(rt) = &c.return_type else {
            return;
        };
        if anonymous_body_has_yield(&c.body) {
            return;
        }
        let Some(declared) = anonymous_declared_return(rt) else {
            return;
        };
        check_anonymous_returns_in_body(fa, &c.body, &declared, &mut out);
    });
    out
}

/// `ArrowFunctionReturnTypeRule` — conservative subset for explicit native arrow
/// return types. The arrow body is a single return expression.
fn run_arrow_function_return_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::ArrowFn(a) = &e.kind else {
            return;
        };
        let Some(rt) = &a.return_type else {
            return;
        };
        if anonymous_expr_has_yield(&a.body) {
            return;
        }
        let Some(declared) = anonymous_declared_return(rt) else {
            return;
        };
        check_anonymous_return_expr(fa, &a.body, &declared, &mut out);
    });
    out
}

fn anonymous_declared_return(rt: &php_ast::Type) -> Option<Type> {
    let declared = php_reflect::resolve_ast_type(&Scope::global(), rt);
    anonymous_target_supported(&declared).then_some(declared)
}

fn anonymous_target_supported(t: &Type) -> bool {
    match t {
        Type::Mixed
        | Type::Unknown(_)
        | Type::Named { .. }
        | Type::SelfType
        | Type::StaticType
        | Type::Parent
        | Type::TemplateVar(_)
        | Type::ClassString(_)
        | Type::Callable(_)
        | Type::Conditional { .. } => false,
        Type::Nullable(inner) => anonymous_target_supported(inner),
        Type::Union(parts) | Type::Intersection(parts) => {
            parts.iter().all(anonymous_target_supported)
        }
        _ => true,
    }
}

fn check_anonymous_returns_in_body(
    fa: &FileAnalysis,
    body: &[Stmt],
    declared: &Type,
    out: &mut Vec<Diagnostic>,
) {
    for st in body {
        check_anonymous_returns_in_stmt(fa, st, declared, out);
    }
}

fn check_anonymous_returns_in_stmt(
    fa: &FileAnalysis,
    st: &Stmt,
    declared: &Type,
    out: &mut Vec<Diagnostic>,
) {
    match &st.kind {
        StmtKind::Return(Some(e)) => check_anonymous_return_expr(fa, e, declared, out),
        StmtKind::Return(None) => check_anonymous_empty_return(st, declared, out),
        StmtKind::Block(b) => check_anonymous_returns_in_body(fa, b, declared, out),
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            check_anonymous_returns_in_stmt(fa, then, declared, out);
            for ei in elseifs {
                check_anonymous_returns_in_stmt(fa, &ei.body, declared, out);
            }
            if let Some(e) = els {
                check_anonymous_returns_in_stmt(fa, e, declared, out);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => {
            check_anonymous_returns_in_stmt(fa, body, declared, out);
        }
        StmtKind::Switch { cases, .. } => {
            for case in cases {
                check_anonymous_returns_in_body(fa, &case.body, declared, out);
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            check_anonymous_returns_in_body(fa, body, declared, out);
            for catch in catches {
                check_anonymous_returns_in_body(fa, &catch.body, declared, out);
            }
            if let Some(fin) = finally {
                check_anonymous_returns_in_body(fa, fin, declared, out);
            }
        }
        StmtKind::Declare { body: Some(b), .. } => {
            check_anonymous_returns_in_stmt(fa, b, declared, out);
        }
        // Nested function/class declarations, and closure expressions contained in
        // ordinary expressions, belong to their own function-like scopes.
        _ => {}
    }
}

fn check_anonymous_empty_return(st: &Stmt, declared: &Type, out: &mut Vec<Diagnostic>) {
    if matches!(declared, Type::Void) {
        return;
    }
    if matches!(declared, Type::Never) {
        out.push(
            Diagnostic::error(
                st.span,
                "Anonymous function should never return but return statement found.".to_string(),
            )
            .with_code("return.never"),
        );
        return;
    }
    out.push(
        Diagnostic::error(
            st.span,
            format!(
                "Anonymous function should return {declared} but empty return statement found."
            ),
        )
        .with_code("return.empty"),
    );
}

fn check_anonymous_return_expr(
    fa: &FileAnalysis,
    e: &Expr,
    declared: &Type,
    out: &mut Vec<Diagnostic>,
) {
    if matches!(declared, Type::Void) {
        let actual = known_anonymous_return_type(fa, e).unwrap_or(Type::Mixed);
        out.push(
            Diagnostic::error(
                e.span,
                format!(
                    "Anonymous function with return type void returns {actual} but should not return anything."
                ),
            )
            .with_code("return.void"),
        );
        return;
    }

    let Some(actual) = known_anonymous_return_type(fa, e) else {
        return;
    };
    if matches!(declared, Type::Never) {
        if !matches!(actual, Type::Never) {
            out.push(
                Diagnostic::error(
                    e.span,
                    "Anonymous function should never return but return statement found."
                        .to_string(),
                )
                .with_code("return.never"),
            );
        }
        return;
    }

    if !function_like::type_mismatch_reportable(
        fa.reflection,
        &actual,
        declared,
        fa.check_nullables,
        fa.report_maybes,
    ) {
        return;
    }
    out.push(
        Diagnostic::error(
            e.span,
            format!("Anonymous function should return {declared} but returns {actual}."),
        )
        .with_code("return.type"),
    );
}

fn known_anonymous_return_type(fa: &FileAnalysis, e: &Expr) -> Option<Type> {
    if let Some(f) = fa.types.get(&expr_key(e)) {
        if decisive_anonymous_actual(&f.merged) {
            return Some(f.merged.clone());
        }
    }
    const_return_expr_type(e)
}

fn expr_key(e: &Expr) -> php_span::NodeKey {
    php_span::NodeKey::of(e.span)
}

fn const_return_expr_type(e: &Expr) -> Option<Type> {
    match &e.kind {
        ExprKind::Paren(inner) => return const_return_expr_type(inner),
        ExprKind::Array { .. } => return Some(Type::Array(None)),
        ExprKind::Interpolated(_) | ExprKind::ShellExec(_) => return Some(Type::String),
        ExprKind::Cast { kind, .. } => return Some(cast_return_type(*kind)),
        ExprKind::Throw(_) | ExprKind::Exit(_) => return Some(Type::Never),
        _ => {}
    }
    Some(match php_infer::eval_const(e)? {
        php_infer::ConstVal::Int(n) => Type::LiteralInt(n),
        php_infer::ConstVal::Float(_) => Type::Float,
        php_infer::ConstVal::Bool(true) => Type::True,
        php_infer::ConstVal::Bool(false) => Type::False,
        php_infer::ConstVal::Str(bytes) => literal_string_return_type(&bytes),
        php_infer::ConstVal::Null => Type::Null,
    })
}

fn literal_string_return_type(bytes: &[u8]) -> Type {
    const MAX_LITERAL_STRING: usize = 64;
    if bytes.len() <= MAX_LITERAL_STRING {
        if let Ok(s) = std::str::from_utf8(bytes) {
            return Type::LiteralString(s.into());
        }
    }
    Type::String
}

fn cast_return_type(kind: CastKind) -> Type {
    match kind {
        CastKind::Int => Type::Int,
        CastKind::Float => Type::Float,
        CastKind::String => Type::String,
        CastKind::Array => Type::Array(None),
        CastKind::Object => Type::Object,
        CastKind::Bool => Type::Bool,
        CastKind::Unset => Type::Null,
        CastKind::Void => Type::Void,
    }
}

fn decisive_anonymous_actual(t: &Type) -> bool {
    match t {
        Type::Mixed
        | Type::Unknown(_)
        | Type::Named { .. }
        | Type::SelfType
        | Type::StaticType
        | Type::Parent
        | Type::TemplateVar(_)
        | Type::Callable(_)
        | Type::Conditional { .. } => false,
        Type::Nullable(inner) => decisive_anonymous_actual(inner),
        Type::Union(parts) | Type::Intersection(parts) => {
            parts.iter().all(decisive_anonymous_actual)
        }
        _ => true,
    }
}

fn anonymous_body_has_yield(body: &[Stmt]) -> bool {
    let mut found = false;
    for st in body {
        crate::walk::for_each_expr_in_scope(st, &mut |e| {
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

fn anonymous_expr_has_yield(e: &Expr) -> bool {
    let mut found = false;
    crate::walk::for_each_subexpr(e, &mut |sub| {
        if matches!(sub.kind, ExprKind::Yield { .. } | ExprKind::YieldFrom(_)) {
            found = true;
        }
    });
    found
}

// ---------------------------------------------------------------------------
// Missing typehints (MissingFunctionReturn/ParameterTypehintRule, level 6)
// ---------------------------------------------------------------------------

/// `MissingFunctionReturnTypehintRule` — a named function with neither a native
/// return type nor an `@return` PHPDoc tag. (Only top-level/namespace functions;
/// closures/arrow-fns/methods belong to other categories.)
fn run_missing_function_return_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::decls::for_each_named_function(fa, |scope, fd| {
        if fd.return_type.is_some() {
            return;
        }
        if doc_has_tag(fd.doc.as_deref(), "@return") {
            return;
        }
        let name = fa.interner.resolve(fd.name);
        let mut d = Diagnostic::error(
            fd.name_span,
            format!("Function {name}() has no return type specified."),
        )
        .with_code("missingType.return");
        // `--fix`: signature inference (§8q) already synthesized the return
        // type from the body when it had confident evidence; a body that
        // provably returns no value is `@return void`.
        if fa.collect_fixes {
            let refl = fa.reflect_function(scope, fd);
            let first_span = crate::fix::first_attr_span(&fd.attrs).unwrap_or(fd.name_span);
            let inferred = fa
                .reflection
                .function(&refl.fqn)
                .filter(|f| f.inferred_return)
                .and_then(|f| {
                    crate::fix::typed_tag_fix(
                        fa,
                        scope,
                        &f.return_type,
                        first_span,
                        fd.doc.as_deref(),
                        php_diagnostics::DocTagKind::Return,
                        None,
                    )
                });
            if let Some(fix) = inferred {
                d = d.with_fix(fix);
            } else if crate::fix::void_return_evidence(&fd.body) {
                if let Some(fix) = crate::fix::doc_tag_fix(
                    fa,
                    first_span,
                    fd.doc.as_deref(),
                    php_diagnostics::DocTagKind::Return,
                    "@return void".to_string(),
                ) {
                    d = d.with_fix(fix);
                }
            }
        }
        out.push(d);
    });
    out
}

/// `MissingFunctionParameterTypehintRule` — a named function parameter with no
/// native type and no `@param $name` PHPDoc tag.
fn run_missing_function_parameter_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::decls::for_each_named_function(fa, |scope, fd| {
        let name = fa.interner.resolve(fd.name);
        for (idx, p) in fd.params.iter().enumerate() {
            if p.ty.is_some() {
                continue;
            }
            let pname = fa.interner.resolve(p.name);
            if doc_has_param(fd.doc.as_deref(), pname) {
                continue;
            }
            let mut d = Diagnostic::error(
                p_span(p),
                format!("Function {name}() has parameter ${pname} with no type specified."),
            )
            .with_code("missingType.parameter");
            // `--fix`: signature inference (§8q) synthesized the type from
            // call-site arguments when it had confident evidence.
            if fa.collect_fixes {
                let refl = fa.reflect_function(scope, fd);
                if let Some(fix) = fa
                    .reflection
                    .function(&refl.fqn)
                    .and_then(|f| f.params.get(idx))
                    .filter(|pr| pr.inferred)
                    .and_then(|pr| {
                        crate::fix::typed_tag_fix(
                            fa,
                            scope,
                            &pr.ty,
                            crate::fix::first_attr_span(&fd.attrs).unwrap_or(fd.name_span),
                            fd.doc.as_deref(),
                            php_diagnostics::DocTagKind::Param,
                            Some(pname),
                        )
                    })
                {
                    d = d.with_fix(fix);
                }
            }
            out.push(d);
        }
    });
    out
}

/// `MissingFunctionReturn/ParameterTypehintRule` — the `missingType.iterableValue`
/// branch: a *declared* (native or `@param`/`@return`) function type that is a bare
/// `array`/`iterable` with no value type. Uses the reflected (native ∪ PHPDoc)
/// type, so `array $x` with `@param array<int> $x` is fine. Disjoint from the
/// no-type-at-all `missingType.parameter`/`missingType.return` checks above.
fn run_missing_function_iterable_value(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    php_resolve::for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            let StmtKind::Function(fd) = &st.kind else {
                continue;
            };
            let refl = fa.reflect_function(scope, fd);
            let name = refl.fqn.trim_start_matches('\\');
            for (idx, (p, pr)) in fd.params.iter().zip(refl.params.iter()).enumerate() {
                if let Some(word) = bare_iterable_word(&pr.ty) {
                    let pname = fa.interner.resolve(p.name);
                    let mut d = Diagnostic::error(
                        p_span(p),
                        format!(
                            "Function {name}() has parameter ${pname} with no value type \
                             specified in iterable type {word}."
                        ),
                    )
                    .with_code("missingType.iterableValue");
                    // `--fix`: cross-file call-site evidence for the
                    // explicitly-`array`-typed parameter (side map, §8q).
                    if fa.collect_fixes {
                        if let Some(fix) = fa
                            .iterable_param_evidence
                            .and_then(|ev| ev.get(&php_infer::evidence_key(&refl.fqn, None, idx)))
                            .and_then(|ty| {
                                crate::fix::typed_tag_fix_ack(
                                    fa,
                                    scope,
                                    ty,
                                    crate::fix::first_attr_span(&fd.attrs).unwrap_or(fd.name_span),
                                    fd.doc.as_deref(),
                                    php_diagnostics::DocTagKind::Param,
                                    Some(pname),
                                )
                            })
                        {
                            d = d.with_fix(fix);
                        }
                    }
                    out.push(d);
                }
            }
            if let Some(rt) = &fd.return_type {
                if let Some(word) = bare_iterable_word(&refl.return_type) {
                    let mut d = Diagnostic::error(
                        rt.span,
                        format!(
                            "Function {name}() return type has no value type specified in \
                             iterable type {word}."
                        ),
                    )
                    .with_code("missingType.iterableValue");
                    // `--fix`: refine from the body's own return expressions.
                    if fa.collect_fixes {
                        if let Some(fix) = crate::fix::iterable_return_evidence(fa, &fd.body)
                            .and_then(|ty| {
                                crate::fix::typed_tag_fix_ack(
                                    fa,
                                    scope,
                                    &ty,
                                    crate::fix::first_attr_span(&fd.attrs).unwrap_or(fd.name_span),
                                    fd.doc.as_deref(),
                                    php_diagnostics::DocTagKind::Return,
                                    None,
                                )
                            })
                        {
                            d = d.with_fix(fix);
                        }
                    }
                    out.push(d);
                }
            }
        }
    });
    out
}

/// Conservative scan of a raw docblock for a tag (e.g. `@return`). Any occurrence
/// of the tag — even partial — counts as "specified", to avoid false positives.
fn doc_has_tag(doc: Option<&str>, tag: &str) -> bool {
    php_phpdoc::query::raw_contains(doc, tag)
}

/// Conservative scan for an `@param ... $name` tag. We accept any `@param` tag
/// that mentions `$name` as a whole word (or a bare `@param`, treating the doc as
/// possibly-complete to stay false-positive-free).
fn doc_has_param(doc: Option<&str>, name: &str) -> bool {
    php_phpdoc::query::has_param_conservative(doc, name)
}

// ---------------------------------------------------------------------------
// Call-as-statement with no side effects (CallToFunctionStatementWithoutSideEffectsRule)
// ---------------------------------------------------------------------------

/// `CallToFunctionStatementWithoutSideEffectsRule` — a call to a known pure
/// built-in whose result is thrown away (the call *is* the whole statement). The
/// return value is the only effect, so the statement is dead. Conservative: only
/// flagged for the curated `PURE_BUILTINS` set, and never for a user function
/// (whose purity we can't determine).
fn run_call_statement_no_side_effects(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    let mut visit = |e: &Expr| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        // First-class-callable `foo(...)` produces a Closure — that *is* a value
        // worth keeping, so skip.
        if args.len() == 1 && args[0].placeholder {
            return;
        }
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        let Some(tail) = function_tail_lower(fa, r) else {
            return;
        };
        if !php_infer::builtins::is_pure_builtin(&tail) {
            return;
        }
        if !is_global_function(fa, r, &tail) {
            return;
        }
        out.push(
            Diagnostic::error(
                e.span,
                format!("Call to function {tail}() on a separate line has no effect."),
            )
            .with_code("function.resultUnused"),
        );
    };
    // A call "on a separate line" = the entire expression of an expression
    // statement is the call. Walk only statement-position expressions.
    for s in &fa.program.stmts {
        stmt_level_calls(s, &mut visit);
    }
    out
}

// ---------------------------------------------------------------------------
// CallToFunctionStatementWithNoDiscardRule
// ---------------------------------------------------------------------------

/// `#[NoDiscard] function f(): T {}` whose call result is explicitly discarded.
///
/// Dynamic callable calls are reported only when the callable expression resolves
/// to one exact reflected function/method. Closure/arrow NoDiscard attributes and
/// first-class-callable variables are skipped until the type model carries that
/// must-use metadata.
fn run_call_statement_no_discard(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.php_version.at_least(80500) {
        return Vec::new();
    }
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    for s in &fa.program.stmts {
        stmt_level_calls(s, &mut |e| {
            let Some((call, in_void_cast, from_pipe)) = function_call_for_no_discard(e) else {
                return;
            };
            let ExprKind::Call { callee, args } = &call.kind else {
                return;
            };
            if !from_pipe && args.iter().any(|a| a.placeholder) {
                return;
            }
            match function_no_discard_target(fa, callee, &fmap) {
                Some(NoDiscardFunctionTarget::Function { display, must_use }) => {
                    if in_void_cast {
                        if !must_use {
                            out.push(
                                Diagnostic::error(
                                    e.span,
                                    format!(
                                        "Call to function {display}() in (void) cast but function allows discarding return value."
                                    ),
                                )
                                .with_code("function.inVoidCast"),
                            );
                        }
                        return;
                    }
                    if must_use {
                        out.push(
                            Diagnostic::error(
                                e.span,
                                format!(
                                    "Call to function {display}() on a separate line discards return value."
                                ),
                            )
                            .with_code("function.resultDiscarded"),
                        );
                    }
                }
                Some(NoDiscardFunctionTarget::Callable { display, must_use }) => {
                    if in_void_cast {
                        if !must_use {
                            out.push(
                                Diagnostic::error(
                                    e.span,
                                    format!(
                                        "Call to callable {display} in (void) cast but callable allows discarding return value."
                                    ),
                                )
                                .with_code("callable.inVoidCast"),
                            );
                        }
                        return;
                    }
                    if must_use {
                        out.push(
                            Diagnostic::error(
                                e.span,
                                format!(
                                    "Call to callable {display} on a separate line discards return value."
                                ),
                            )
                            .with_code("callable.resultDiscarded"),
                        );
                    }
                }
                None => {}
            }
        });
    }
    out
}

enum NoDiscardFunctionTarget {
    Function { display: String, must_use: bool },
    Callable { display: String, must_use: bool },
}

fn function_call_for_no_discard(e: &Expr) -> Option<(&Expr, bool, bool)> {
    let (e, in_void_cast) = match &e.kind {
        ExprKind::Cast {
            kind: CastKind::Void,
            expr,
        } => (php_ast::queries::peel_paren(expr), true),
        _ => (e, false),
    };
    let e = php_ast::queries::peel_paren(e);
    match &e.kind {
        ExprKind::Call { .. } => Some((e, in_void_cast, false)),
        ExprKind::Binary {
            op: BinOp::Pipe,
            rhs,
            ..
        } => pipe_function_call_for_no_discard(rhs)
            .map(|(call, from_pipe)| (call, in_void_cast, from_pipe)),
        _ => None,
    }
}

fn pipe_function_call_for_no_discard(rhs: &Expr) -> Option<(&Expr, bool)> {
    let rhs = php_ast::queries::peel_paren(rhs);
    match &rhs.kind {
        ExprKind::Call { args, .. } if args.iter().any(|a| a.placeholder) => Some((rhs, true)),
        ExprKind::ArrowFn(a)
            if matches!(
                &php_ast::queries::peel_paren(&a.body).kind,
                ExprKind::Call { .. }
            ) =>
        {
            Some((php_ast::queries::peel_paren(&a.body), false))
        }
        _ => None,
    }
}

fn function_no_discard_target(
    fa: &FileAnalysis,
    callee: &Expr,
    fmap: &HashMap<(u32, u32), &ResolvedRef>,
) -> Option<NoDiscardFunctionTarget> {
    if let Some(r) = members::resolved_callee(callee, fmap) {
        let fqn = reflection_function_fqn(fa, r)?;
        let func = fa.reflection.function(&fqn)?;
        return Some(NoDiscardFunctionTarget::Function {
            display: func.fqn.trim_start_matches('\\').to_string(),
            must_use: func.must_use_return_value,
        });
    }
    callable_no_discard_target(fa, callee)
}

fn reflection_function_fqn(fa: &FileAnalysis, r: &ResolvedRef) -> Option<String> {
    CallResolver::new(fa)
        .reflected_function(r)
        .map(|(fqn, _)| fqn)
}

fn callable_no_discard_target(fa: &FileAnalysis, callee: &Expr) -> Option<NoDiscardFunctionTarget> {
    if let Some(name) = exact_string_value(fa, callee) {
        let func = fa.reflection.function(&name)?;
        return Some(NoDiscardFunctionTarget::Callable {
            display: callable_display(fa, callee),
            must_use: func.must_use_return_value,
        });
    }
    let ExprKind::Array { items, .. } = &callee.kind else {
        return None;
    };
    if items.len() != 2 || items.iter().any(|i| i.spread || i.key.is_some()) {
        return None;
    }
    let recv = items.first()?.value.as_ref()?;
    let method = items.get(1)?.value.as_ref()?;
    let class = exact_callable_receiver_class(fa, recv)?;
    let method_name = exact_string_value(fa, method)?;
    let found = fa.reflection.find_method(&class, &method_name)?;
    Some(NoDiscardFunctionTarget::Callable {
        display: callable_display(fa, callee),
        must_use: found.member.must_use_return_value,
    })
}

fn exact_callable_receiver_class(fa: &FileAnalysis, e: &Expr) -> Option<String> {
    match fa.type_of(e) {
        Type::Named { fqn, .. } => Some(fqn.to_string()),
        Type::ClassString(Some(inner)) => named_type_fqn(&inner),
        Type::LiteralString(s) => fa.reflection.class(&s).map(|c| c.fqn.clone()),
        Type::Nullable(inner) => named_type_fqn(&inner),
        _ => None,
    }
}

fn named_type_fqn(t: &Type) -> Option<String> {
    match t {
        Type::Named { fqn, .. } => Some(fqn.to_string()),
        Type::Nullable(inner) => named_type_fqn(inner),
        _ => None,
    }
}

fn exact_string_value(fa: &FileAnalysis, e: &Expr) -> Option<String> {
    match &e.kind {
        ExprKind::Str(bytes) => std::str::from_utf8(bytes).ok().map(ToOwned::to_owned),
        ExprKind::Paren(inner) => exact_string_value(fa, inner),
        _ => match fa.type_of(e) {
            Type::LiteralString(s) => Some(s.to_string()),
            _ => None,
        },
    }
}

fn callable_display(fa: &FileAnalysis, e: &Expr) -> String {
    fa.type_of(e).to_string()
}

/// Invoke `f` on every expression that appears in *statement position* (the whole
/// value of an `Expr` statement). Descends through blocks/control flow and into
/// function-like bodies (their statement lists), but not into sub-expressions.
pub(crate) fn stmt_level_calls<F: FnMut(&Expr)>(s: &Stmt, f: &mut F) {
    match &s.kind {
        StmtKind::Expr(e) => {
            f(e);
            stmt_level_calls_in_expr_scopes(e, f);
        }
        StmtKind::Echo(es) | StmtKind::Global(es) | StmtKind::Unset(es) => {
            es.iter()
                .for_each(|e| stmt_level_calls_in_expr_scopes(e, f));
        }
        StmtKind::Return(Some(e)) | StmtKind::Break(Some(e)) | StmtKind::Continue(Some(e)) => {
            stmt_level_calls_in_expr_scopes(e, f);
        }
        StmtKind::Block(b) => b.iter().for_each(|st| stmt_level_calls(st, f)),
        StmtKind::Namespace { body: Some(b), .. } => {
            b.iter().for_each(|st| stmt_level_calls(st, f))
        }
        StmtKind::Function(fd) => fd.body.iter().for_each(|st| stmt_level_calls(st, f)),
        StmtKind::Class(c) => class_stmt_level_calls(c, f),
        StmtKind::If {
            cond,
            then,
            elseifs,
            els,
            ..
        } => {
            stmt_level_calls_in_expr_scopes(cond, f);
            stmt_level_calls(then, f);
            for ei in elseifs {
                stmt_level_calls_in_expr_scopes(&ei.cond, f);
                stmt_level_calls(&ei.body, f);
            }
            if let Some(e) = els {
                stmt_level_calls(e, f);
            }
        }
        StmtKind::While { cond, body } => {
            stmt_level_calls_in_expr_scopes(cond, f);
            stmt_level_calls(body, f);
        }
        StmtKind::DoWhile { body, cond } => {
            stmt_level_calls(body, f);
            stmt_level_calls_in_expr_scopes(cond, f);
        }
        StmtKind::For {
            init,
            cond,
            update,
            body,
        } => {
            init.iter()
                .chain(cond)
                .chain(update)
                .for_each(|e| stmt_level_calls_in_expr_scopes(e, f));
            stmt_level_calls(body, f);
        }
        StmtKind::Foreach {
            subject,
            key,
            value,
            body,
            ..
        } => {
            stmt_level_calls_in_expr_scopes(subject, f);
            if let Some(k) = key {
                stmt_level_calls_in_expr_scopes(k, f);
            }
            stmt_level_calls_in_expr_scopes(value, f);
            stmt_level_calls(body, f);
        }
        StmtKind::Switch { subject, cases } => {
            stmt_level_calls_in_expr_scopes(subject, f);
            for c in cases {
                if let Some(test) = &c.test {
                    stmt_level_calls_in_expr_scopes(test, f);
                }
                c.body.iter().for_each(|st| stmt_level_calls(st, f));
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter().for_each(|st| stmt_level_calls(st, f));
            for c in catches {
                c.body.iter().for_each(|st| stmt_level_calls(st, f));
            }
            if let Some(fin) = finally {
                fin.iter().for_each(|st| stmt_level_calls(st, f));
            }
        }
        StmtKind::StaticVars(vars) => {
            for v in vars {
                if let Some(default) = &v.default {
                    stmt_level_calls_in_expr_scopes(default, f);
                }
            }
        }
        StmtKind::Declare { directives, body } => {
            directives
                .iter()
                .for_each(|(_, e)| stmt_level_calls_in_expr_scopes(e, f));
            if let Some(b) = body {
                stmt_level_calls(b, f);
            }
        }
        StmtKind::ConstDecl { consts, .. } => {
            consts
                .iter()
                .for_each(|c| stmt_level_calls_in_expr_scopes(&c.value, f));
        }
        _ => {}
    }
}

fn stmt_level_calls_in_expr_scopes<F: FnMut(&Expr)>(e: &Expr, f: &mut F) {
    crate::walk::for_each_subexpr(e, &mut |sub| match &sub.kind {
        ExprKind::Closure(c) => {
            c.body.iter().for_each(|st| stmt_level_calls(st, f));
        }
        ExprKind::NewAnon { class, .. } => class_stmt_level_calls(class, f),
        _ => {}
    });
}

fn class_stmt_level_calls<F: FnMut(&Expr)>(c: &ClassDecl, f: &mut F) {
    for m in &c.members {
        match m {
            Member::Method(md) => {
                if let Some(body) = &md.body {
                    body.iter().for_each(|st| stmt_level_calls(st, f));
                }
            }
            Member::Property(pd) => {
                for elem in &pd.props {
                    if let Some(default) = &elem.default {
                        stmt_level_calls_in_expr_scopes(default, f);
                    }
                    if let Some(hooks) = &elem.hooks {
                        for h in hooks {
                            if let Some(params) = &h.params {
                                for p in params {
                                    if let Some(default) = &p.default {
                                        stmt_level_calls_in_expr_scopes(default, f);
                                    }
                                }
                            }
                            match &h.body {
                                HookBody::Block(stmts) => {
                                    stmts.iter().for_each(|st| stmt_level_calls(st, f));
                                }
                                HookBody::Short(e) => stmt_level_calls_in_expr_scopes(e, f),
                                HookBody::Abstract => {}
                            }
                        }
                    }
                }
            }
            Member::ClassConst(cd) => {
                cd.consts
                    .iter()
                    .for_each(|c| stmt_level_calls_in_expr_scopes(&c.value, f));
            }
            Member::EnumCase(ec) => {
                if let Some(value) = &ec.value {
                    stmt_level_calls_in_expr_scopes(value, f);
                }
            }
            Member::TraitUse(_) => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Useless function return value (UselessFunctionReturnValueRule, level 4)
// ---------------------------------------------------------------------------

/// `UselessFunctionReturnValueRule` — `var_export`/`print_r`/`highlight_string`
/// used in a value position (not as a bare statement) without passing `true` as
/// the 2nd argument: they print and return `null`/`true`, so the consumed value
/// is useless and the output leaks to stdout. The `$return` argument literal
/// `true` (or any non-`false`) silences it; only a literal `false`/missing 2nd
/// arg in a value position is flagged.
fn run_useless_return_value(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    // Set of spans that are calls appearing in statement position (first-level):
    // those are NOT in a value position, so they're exempt.
    let mut statement_calls: HashSet<(u32, u32)> = HashSet::new();
    for s in &fa.program.stmts {
        stmt_level_calls(s, &mut |e| {
            if matches!(&e.kind, ExprKind::Call { .. }) {
                statement_calls.insert((e.span.start, e.span.end));
            }
        });
    }
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        if statement_calls.contains(&(e.span.start, e.span.end)) {
            return; // bare statement — result isn't used.
        }
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        let Some(tail) = function_tail_lower(fa, r) else {
            return;
        };
        let always = match tail.as_str() {
            "var_export" => "null",
            "print_r" => "true",
            "highlight_string" => "true",
            _ => return,
        };
        if !is_global_function(fa, r, &tail) {
            return;
        }
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        // A 2nd argument that is not the literal `false` returns the output —
        // exempt. Only "missing 2nd arg" or "2nd arg is literal false" is useless.
        let returns_output = match args.get(1) {
            None => false,
            Some(a) => !is_literal_false(&a.value),
        };
        if returns_output {
            return;
        }
        out.push(
            Diagnostic::error(
                e.span,
                format!(
                    "Return value of function {tail}() is always {always} and the result is printed \
                     instead of being returned. Pass in true as parameter #2 to return the output instead."
                ),
            )
            .with_code("function.uselessReturnValue"),
        );
    });
    out
}

fn is_literal_false(e: &Expr) -> bool {
    match &e.kind {
        // `true`/`false`/`null` are not keywords — they parse as bare names.
        ExprKind::Name(n) => n.fq == php_ast::NameFq::NotFq && n.text.eq_ignore_ascii_case("false"),
        ExprKind::Paren(inner) => is_literal_false(inner),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// array_values on a list (ArrayValuesRule, level 5)
// ---------------------------------------------------------------------------

/// `ArrayValuesRule` (the `arrayValues.list` half). `array_values($x)` where `$x`
/// is *already* a list — the call has no effect. We only fire for a concretely
/// inferred `list<…>` argument; the `arrayValues.empty` case needs non-emptiness
/// tracking we don't model, so it is deferred.
fn run_array_values(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        if function_tail_lower(fa, r).as_deref() != Some("array_values")
            || !is_global_function(fa, r, "array_values")
        {
            return;
        }
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        let Some(first) = args.first() else { return };
        let arr_ty = fa.type_of(&first.value);
        if matches!(arr_ty, php_types::Type::List(_)) {
            out.push(
                Diagnostic::error(
                    e.span,
                    format!(
                        "Parameter #1 $array ({arr_ty}) of array_values is already a list, call has no effect."
                    ),
                )
                .with_code("arrayValues.list"),
            );
        }
    });
    out
}

// ---------------------------------------------------------------------------
// array_filter on literal arrays (ArrayFilterRule, level 5)
// ---------------------------------------------------------------------------

/// `ArrayFilterRule` — no-callback `array_filter($array)` removes falsy values.
/// We only fire for literal arrays whose contents are syntactically constant:
/// an empty literal, all-truthy literal values, or all-falsy literal values.
/// Any dynamic value/spread/by-ref item is skipped so inferred imprecision cannot
/// create false positives.
fn run_array_filter(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        if function_tail_lower(fa, r).as_deref() != Some("array_filter")
            || !is_global_function(fa, r, "array_filter")
        {
            return;
        }
        if args.len() != 1
            || args
                .iter()
                .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        let Some(kind) = literal_array_filter_kind(&args[0].value) else {
            return;
        };
        let array_desc = literal_array_desc(fa, &args[0].value);
        let (message, code) = match kind {
            ArrayFilterKind::Empty => (
                format!(
                    "Parameter #1 $array ({array_desc}) to function array_filter is empty, call has no effect."
                ),
                "arrayFilter.empty",
            ),
            ArrayFilterKind::AllTruthy => (
                format!(
                    "Parameter #1 $array ({array_desc}) to function array_filter does not contain falsy values, the array will always stay the same."
                ),
                "arrayFilter.same",
            ),
            ArrayFilterKind::AllFalsy => (
                format!(
                    "Parameter #1 $array ({array_desc}) to function array_filter contains falsy values only, the result will always be an empty array."
                ),
                "arrayFilter.alwaysEmpty",
            ),
        };
        out.push(Diagnostic::error(e.span, message).with_code(code));
    });
    out
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ArrayFilterKind {
    Empty,
    AllTruthy,
    AllFalsy,
}

fn literal_array_filter_kind(e: &Expr) -> Option<ArrayFilterKind> {
    let ExprKind::Array { items, .. } = &strip_parens(e).kind else {
        return None;
    };
    if items.is_empty() {
        return Some(ArrayFilterKind::Empty);
    }
    let mut saw_value = false;
    let mut all_truthy = true;
    let mut all_falsy = true;
    for item in items {
        if item.spread || item.by_ref {
            return None;
        }
        let value = item.value.as_ref()?;
        saw_value = true;
        let v = php_infer::eval_const(value)?;
        if v.truthy() {
            all_falsy = false;
        } else {
            all_truthy = false;
        }
    }
    if !saw_value {
        return None;
    }
    if all_truthy {
        Some(ArrayFilterKind::AllTruthy)
    } else if all_falsy {
        Some(ArrayFilterKind::AllFalsy)
    } else {
        None
    }
}

fn strip_parens(mut e: &Expr) -> &Expr {
    while let ExprKind::Paren(inner) = &e.kind {
        e = inner;
    }
    e
}

fn literal_array_desc(fa: &FileAnalysis, e: &Expr) -> String {
    if matches!(
        &strip_parens(e).kind,
        ExprKind::Array { items, .. } if items.is_empty()
    ) {
        "array{}".to_string()
    } else {
        fa.type_of(e).to_string()
    }
}

// ---------------------------------------------------------------------------
// Castable-to-string array arguments (ParameterCastableToStringRule, level 5)
// ---------------------------------------------------------------------------

/// The element type of a concretely-typed array/list expression, or `None` when
/// the argument's element type is unknown (so we stay false-positive-free).
fn array_element_type(t: &php_types::Type) -> Option<php_types::Type> {
    match t {
        php_types::Type::Array(Some(kv)) => Some(kv.1.clone()),
        php_types::Type::List(v) => Some((**v).clone()),
        _ => None,
    }
}

/// `ParameterCastableToStringRule` — functions that compare/key array elements as
/// strings require every element to be castable to string. The all-args functions
/// (`array_diff`/`array_intersect`/…) check every array argument; the first-arg
/// functions (`array_combine`/`natsort`/…) check only argument #1. Only fires when
/// an array argument's element type is concrete and definitely not stringable.
fn run_parameter_castable_to_string(fa: &FileAnalysis) -> Vec<Diagnostic> {
    const ALL_ARGS: &[&str] = &[
        "array_intersect",
        "array_intersect_assoc",
        "array_diff",
        "array_diff_assoc",
    ];
    const FIRST_ARG: &[&str] = &[
        "array_combine",
        "natcasesort",
        "natsort",
        "array_count_values",
        "array_fill_keys",
    ];
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        let Some(tail) = function_tail_lower(fa, r) else {
            return;
        };
        let name = tail.as_str();
        let all_args = ALL_ARGS.contains(&name);
        if (!all_args && !FIRST_ARG.contains(&name)) || !is_global_function(fa, r, name) {
            return;
        }
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        let indices: Vec<usize> = if all_args {
            (0..args.len()).collect()
        } else {
            vec![0]
        };
        for idx in indices {
            let Some(arg) = args.get(idx) else { continue };
            let arr_ty = fa.type_of(&arg.value);
            let Some(elem) = array_element_type(&arr_ty) else {
                continue;
            };
            if !crate::is_castable_to_string(fa.reflection, &elem) {
                out.push(
                    Diagnostic::error(
                        arg.value.span,
                        format!(
                            "Parameter #{} $array of function {name} expects an array of values \
                             castable to string, {arr_ty} given.",
                            idx + 1
                        ),
                    )
                    .with_code("argument.type"),
                );
            }
        }
    });
    out
}

/// `SortParameterCastableToStringRule` (the no-flags `array_unique` subset).
/// `array_unique($a)` defaults to `SORT_STRING`, so its elements must be castable
/// to string. We only handle `array_unique` with a single argument (no explicit
/// flags) to avoid resolving `SORT_*` flag constants we don't expose. Only fires
/// for a concrete, definitely-non-stringable element type.
fn run_sort_castable_to_string(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        if function_tail_lower(fa, r).as_deref() != Some("array_unique")
            || !is_global_function(fa, r, "array_unique")
        {
            return;
        }
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        // Only the implicit-SORT_STRING form (a single argument).
        if args.len() != 1 {
            return;
        }
        let arr_ty = fa.type_of(&args[0].value);
        let Some(elem) = array_element_type(&arr_ty) else {
            return;
        };
        if !crate::is_castable_to_string(fa.reflection, &elem) {
            out.push(
                Diagnostic::error(
                    args[0].value.span,
                    format!(
                        "Parameter #1 $array of function array_unique expects an array of values \
                         castable to string, {arr_ty} given."
                    ),
                )
                .with_code("argument.type"),
            );
        }
    });
    out
}

// ---------------------------------------------------------------------------
// Castable-to-number array arguments (ParameterCastableToNumberRule, level 5)
// ---------------------------------------------------------------------------

/// Whether a value of `ty` is definitely NOT castable to a number (`int`/`float`).
/// Conservative inverse of PHP's `toNumber`: arrays/iterables/shapes/callables/
/// `void` never cast; everything else (scalars/null/objects/mixed/templates/
/// unknown) is treated as castable to stay false-positive-free.
fn is_definitely_not_numeric(ty: &php_types::Type) -> bool {
    use php_types::Type::*;
    match ty {
        Array(_) | List(_) | Iterable(_) | Shape { .. } | Callable(_) | Void => true,
        // A union is not-numeric only if *every* member is (e.g. `list<1>|list<2>`).
        Union(parts) => parts.iter().all(is_definitely_not_numeric),
        _ => false,
    }
}

/// `ParameterCastableToNumberRule` — `array_sum`/`array_product` reduce an array
/// by numeric addition/multiplication, so every element must cast to a number.
/// Only fires for a concrete element type that is definitely non-numeric.
fn run_parameter_castable_to_number(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        let Some(tail) = function_tail_lower(fa, r) else {
            return;
        };
        let name = tail.as_str();
        if !matches!(name, "array_sum" | "array_product") || !is_global_function(fa, r, name) {
            return;
        }
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        if args.len() != 1 {
            return;
        }
        let arr_ty = fa.type_of(&args[0].value);
        let Some(elem) = array_element_type(&arr_ty) else {
            return;
        };
        if is_definitely_not_numeric(&elem) {
            out.push(
                Diagnostic::error(
                    args[0].value.span,
                    format!(
                        "Parameter #1 $array of function {name} expects an array of values castable \
                         to number, {arr_ty} given."
                    ),
                )
                .with_code("argument.type"),
            );
        }
    });
    out
}

// ---------------------------------------------------------------------------
// random_int($min, $max) bound order (RandomIntParametersRule, level 5)
// ---------------------------------------------------------------------------

fn run_random_int_parameters(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        if function_tail_lower(fa, r).as_deref() != Some("random_int")
            || !is_global_function(fa, r, "random_int")
        {
            return;
        }
        if args.len() < 2
            || args
                .iter()
                .take(2)
                .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        let min = fa.type_of(&args[0].value);
        let max = fa.type_of(&args[1].value);
        let Some((min_low, _)) = int_bounds(&min) else {
            return;
        };
        let Some((_, max_high)) = int_bounds(&max) else {
            return;
        };
        if min_low <= max_high {
            return;
        }
        out.push(
            Diagnostic::error(
                args[0].value.span,
                format!(
                    "Parameter #1 $min ({min}) of function random_int expects lower number than parameter #2 $max ({max})."
                ),
            )
            .with_code("argument.type"),
        );
    });
    out
}

fn int_bounds(ty: &Type) -> Option<(i64, i64)> {
    match ty {
        Type::LiteralInt(n) => Some((*n, *n)),
        Type::IntRange {
            min: Some(min),
            max: Some(max),
        } => Some((*min, *max)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Incompatible default parameter value (IncompatibleDefaultParameterTypeRule, L2)
// ---------------------------------------------------------------------------

/// Map a parameter's native type hint to a semantic scalar type for the
/// default-value check. Returns `None` for class/callable/object/union/etc. —
/// those can't have a non-null constant default anyway, so skipping is safe.
fn ast_default_target(ty: &php_ast::Type) -> Option<php_types::Type> {
    use php_ast::TypeKind;
    use php_types::Type;
    match &ty.kind {
        TypeKind::Simple(n) => {
            let last = n
                .text
                .rsplit('\\')
                .next()
                .unwrap_or(&n.text)
                .to_ascii_lowercase();
            Some(match last.as_str() {
                "int" => Type::Int,
                "float" => Type::Float,
                "string" => Type::String,
                "bool" => Type::Bool,
                "array" => Type::Array(None),
                "iterable" => Type::Iterable(None),
                _ => return None,
            })
        }
        TypeKind::Nullable(inner) => ast_default_target(inner),
        _ => None,
    }
}

/// `IncompatibleClosure/ArrowFunctionDefaultParameterTypeRule` — a closure or
/// arrow-fn parameter whose constant default value is incompatible with its
/// native type hint. Closures aren't reflected, so we resolve the declared scalar
/// type from the AST and fold the default value.
fn run_incompatible_closure_default(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let params = match &e.kind {
            ExprKind::Closure(c) => &c.params,
            ExprKind::ArrowFn(a) => &a.params,
            _ => return,
        };
        for (i, p) in params.iter().enumerate() {
            let Some(default) = &p.default else { continue };
            let Some(ty) = &p.ty else { continue };
            let Some(target) = ast_default_target(ty) else {
                continue;
            };
            let Some(dty) = const_default_type(default) else {
                continue;
            };
            if dty == php_types::Type::Null {
                continue;
            }
            if compat::value_mismatch(fa, &dty, Some(&dty), &target, &target) {
                out.push(
                    Diagnostic::error(
                        default.span,
                        format!(
                            "Default value of the parameter #{} ${} ({dty}) of anonymous function is incompatible with type {target}.",
                            i + 1,
                            fa.interner.resolve(p.name)
                        ),
                    )
                    .with_code("parameter.defaultValue"),
                );
            }
        }
    });
    out
}

/// `IncompatibleDefaultParameterTypeRule` — a named function parameter whose
/// default value's type is incompatible with its declared type
/// (`function f(int $x = 'no')`). We type the default via the file's type map
/// (`fa.type_of`) and check it against the *reflected* parameter type with
/// assignability. Conservative: skips when the default type or the parameter type
/// is unknown/mixed; the special PHP rule that allows `null` defaults to widen the
/// type to nullable means we only flag a clearly-incompatible non-null default.
fn run_incompatible_default_parameter(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_stmt(fa.program, &mut |s| {
        let StmtKind::Function(fd) = &s.kind else {
            return;
        };
        let name = fa.interner.resolve(fd.name).to_string();
        // Resolve the function's reflected signature for native parameter types.
        // A bare name resolves global-namespace functions (reflection keys are
        // case-folded with the leading `\` stripped); namespaced declarations are
        // skipped here (conservative — no false positive).
        let Some(func) = fa.reflection.function(&name) else {
            return;
        };
        for (i, p) in fd.params.iter().enumerate() {
            let Some(default) = &p.default else { continue };
            // Only check params with a native type hint (PHPDoc-only is M-T leniency).
            if p.ty.is_none() {
                continue;
            }
            let Some(param) = func.params.get(i) else {
                continue;
            };
            // The default's type. Param-list defaults aren't in the body type map,
            // so fold the (constant) default directly; only a literal default
            // gives a concrete type. A non-constant/array default is skipped.
            let Some(dty) = const_default_type(default) else {
                continue;
            };
            // A literal `null` default is always allowed (it implicitly widens the
            // type to nullable) — never flag it.
            if dty == php_types::Type::Null {
                continue;
            }
            // An array-literal default (`[]`, `[…]`) is compatible with any
            // array/iterable parameter — an empty array fits any `array<K,V>`, and
            // we don't type literal elements here (under-report, never false-flag).
            if matches!(dty, php_types::Type::Array(_)) && is_array_or_iterable(&param.ty) {
                continue;
            }
            if compat::value_mismatch(fa, &dty, Some(&dty), &param.ty, &param.native_ty) {
                out.push(
                    Diagnostic::error(
                        default.span,
                        format!(
                            "Default value of the parameter #{} ${} ({dty}) of function {name}() \
                             is incompatible with type {}.",
                            i + 1,
                            param.name,
                            param.ty
                        ),
                    )
                    .with_code("parameter.defaultValue"),
                );
            }
        }
    });
    out
}

/// The concrete type of a parameter *default value* iff it is a literal we can
/// fold (scalars/`null` via `eval_const`, or an array literal → `array`).
/// `None` for non-constant defaults (a constant reference, `new`, etc.), which we
/// then skip to stay false-positive-free.
/// Whether `t` (under one level of nullable) is an array/iterable-like type — an
/// array-literal default is always compatible with such a parameter.
fn is_array_or_iterable(t: &php_types::Type) -> bool {
    use php_types::Type;
    match t {
        Type::Array(_) | Type::Iterable(_) | Type::List(_) | Type::Shape { .. } => true,
        Type::Nullable(inner) => is_array_or_iterable(inner),
        _ => false,
    }
}

fn const_default_type(e: &Expr) -> Option<php_types::Type> {
    use php_types::Type;
    if let ExprKind::Array { .. } = &e.kind {
        return Some(Type::Array(None));
    }
    if let ExprKind::Paren(inner) = &e.kind {
        return const_default_type(inner);
    }
    match php_infer::eval_const(e)? {
        php_infer::ConstVal::Int(_) => Some(Type::Int),
        php_infer::ConstVal::Float(_) => Some(Type::Float),
        php_infer::ConstVal::Bool(b) => Some(if b { Type::True } else { Type::False }),
        php_infer::ConstVal::Str(_) => Some(Type::String),
        php_infer::ConstVal::Null => Some(Type::Null),
    }
}

// ---------------------------------------------------------------------------
// filter_var conflicting flags (FilterVarRule, level 0)
// ---------------------------------------------------------------------------

/// `FilterVarRule` — `filter_var($v, $f, FILTER_NULL_ON_FAILURE | FILTER_THROW_ON_FAILURE)`
/// passes two mutually-exclusive flags. Detected purely syntactically: the 3rd
/// argument's expression mentions *both* constant names anywhere in a `|`/`+`
/// flag composition. Conservative — only the literal constant-name form is flagged.
fn run_filter_var(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        if function_tail_lower(fa, r).as_deref() != Some("filter_var")
            || !is_global_function(fa, r, "filter_var")
        {
            return;
        }
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        let Some(flags) = args.get(2) else { return };
        let mut names: HashSet<String> = HashSet::new();
        collect_const_names(&flags.value, &mut names);
        if names.contains("FILTER_NULL_ON_FAILURE") && names.contains("FILTER_THROW_ON_FAILURE") {
            out.push(
                Diagnostic::error(
                    e.span,
                    "Cannot use both FILTER_NULL_ON_FAILURE and FILTER_THROW_ON_FAILURE."
                        .to_string(),
                )
                .with_code("filterVar.nullOnFailureAndThrowOnFailure"),
            );
        }
    });
    out
}

/// Collect bare constant names mentioned in a (possibly `|`/`+`-composed) flag
/// expression, so the filter_var rule can see both flag constants.
fn collect_const_names(e: &Expr, out: &mut HashSet<String>) {
    match &e.kind {
        ExprKind::Name(n) => {
            out.insert(n.text.trim_start_matches('\\').to_string());
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_const_names(lhs, out);
            collect_const_names(rhs, out);
        }
        ExprKind::Paren(inner) => collect_const_names(inner, out),
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// call_user_func with a non-callable first argument (CallUserFuncRule, level 5)
// ---------------------------------------------------------------------------

/// `CallUserFuncRule` (the non-callable subset). `call_user_func($x, …)` /
/// `call_user_func_array($x, …)` where the first argument is definitely not a
/// callable (a concrete non-callable scalar). Strings/arrays/objects can be
/// callables, so they're never flagged; `mixed`/unknown is skipped.
fn run_call_user_func(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = members::function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else {
            return;
        };
        let Some(r) = members::resolved_callee(callee, &fmap) else {
            return;
        };
        let Some(tail) = function_tail_lower(fa, r) else {
            return;
        };
        let name = match tail.as_str() {
            "call_user_func" => "call_user_func",
            "call_user_func_array" => "call_user_func_array",
            _ => return,
        };
        if !is_global_function(fa, r, name) {
            return;
        }
        if args
            .iter()
            .any(|a| a.spread || a.placeholder || a.name.is_some())
        {
            return;
        }
        let Some(first) = args.first() else { return };
        let t = fa.type_of(&first.value);
        if is_definitely_not_callable(&t) {
            out.push(
                Diagnostic::error(
                    first.value.span,
                    format!(
                        "Parameter #1 $callback of function {name} expects callable, {t} given."
                    ),
                )
                .with_code("argument.type"),
            );
        }
    });
    out
}

/// Whether a resolved call refers to the named *global* built-in (no namespaced
/// user override). Shared by the call-site built-in rules above.
fn is_global_function(fa: &FileAnalysis, r: &ResolvedRef, name: &str) -> bool {
    known_function_target(fa, r).is_some_and(|fqn| fqn.eq_ignore_ascii_case(name))
}

// ---------------------------------------------------------------------------
// Registration
// ---------------------------------------------------------------------------

pub(crate) static RULES: &[RuleEntry] = &[
    // Pre-existing: checks each `return <expr>` against the declared return type.
    RuleEntry {
        name: "return-type",
        level: 3,
        run: run_return_type,
    },
    RuleEntry {
        name: "closure.returnType",
        level: 3,
        run: run_closure_return_type,
    },
    RuleEntry {
        name: "arrowFunction.returnType",
        level: 3,
        run: run_arrow_function_return_type,
    },
    // Level 0 — purely syntactic / name-based.
    RuleEntry {
        name: "parameter.duplicate",
        level: 0,
        run: run_redefined_parameters,
    },
    RuleEntry {
        name: "parameter.name",
        level: 0,
        run: run_invalid_parameter_name,
    },
    RuleEntry {
        name: "parameter.variadicNotLast",
        level: 0,
        run: run_variadic_parameters,
    },
    RuleEntry {
        name: "function.inner",
        level: 0,
        run: run_inner_function,
    },
    RuleEntry {
        name: "closure.invalidUse",
        level: 0,
        run: run_invalid_lexical_use,
    },
    RuleEntry {
        name: "function.notFound",
        level: 0,
        run: run_call_to_non_existent_function,
    },
    RuleEntry {
        name: "function.nameCase",
        level: 0,
        run: run_function_name_case,
    },
    RuleEntry {
        name: "function.callable",
        level: 0,
        run: run_function_callable,
    },
    RuleEntry {
        name: "callable.notSupported",
        level: 0,
        run: run_first_class_callable_version,
    },
    RuleEntry {
        name: "argument.printf",
        level: 0,
        run: run_printf_parameters,
    },
    RuleEntry {
        name: "argument.printfArray",
        level: 0,
        run: run_printf_array_parameters,
    },
    RuleEntry {
        name: "argument.define",
        level: 0,
        run: run_define_parameters,
    },
    RuleEntry {
        name: "function.duplicate",
        level: 0,
        run: run_duplicate_function,
    },
    RuleEntry {
        name: "nullsafe.byRef",
        level: 0,
        run: run_return_nullsafe_by_ref,
    },
    RuleEntry {
        name: "arrow.nullsafe.byRef",
        level: 0,
        run: run_arrow_nullsafe_by_ref,
    },
    // Level 1 — closure use analysis.
    RuleEntry {
        name: "closure.unusedUse",
        level: 1,
        run: run_unused_closure_uses,
    },
    // Level 4 — dead/useless statement-level calls.
    RuleEntry {
        name: "function.resultUnused",
        level: 4,
        run: run_call_statement_no_side_effects,
    },
    RuleEntry {
        name: "function.uselessReturnValue",
        level: 4,
        run: run_useless_return_value,
    },
    RuleEntry {
        name: "function.noDiscard",
        level: 0,
        run: run_call_statement_no_discard,
    },
    // Level 5 — arguments: count + types.
    RuleEntry {
        name: "arguments.count",
        level: 5,
        run: run_argument_count,
    },
    RuleEntry {
        name: "argument.type",
        level: 5,
        run: run_argument_types,
    },
    RuleEntry {
        name: "argument.implodeCastable",
        level: 5,
        run: run_implode_castable,
    },
    RuleEntry {
        name: "arrayValues.list",
        level: 5,
        run: run_array_values,
    },
    RuleEntry {
        name: "arrayFilter.literal",
        level: 5,
        run: run_array_filter,
    },
    RuleEntry {
        name: "argument.castableToString",
        level: 5,
        run: run_parameter_castable_to_string,
    },
    RuleEntry {
        name: "argument.sortCastableToString",
        level: 5,
        run: run_sort_castable_to_string,
    },
    RuleEntry {
        name: "argument.castableToNumber",
        level: 5,
        run: run_parameter_castable_to_number,
    },
    RuleEntry {
        name: "argument.randomInt",
        level: 5,
        run: run_random_int_parameters,
    },
    RuleEntry {
        name: "argument.callUserFunc",
        level: 5,
        run: run_call_user_func,
    },
    // Level 2 — invoking a non-callable value; incompatible default values.
    RuleEntry {
        name: "callable.nonCallable",
        level: 2,
        run: run_invoke_non_callable,
    },
    RuleEntry {
        name: "callable.maybeNonCallable",
        level: 7,
        run: run_invoke_maybe_non_callable,
    },
    RuleEntry {
        name: "parameter.defaultValue",
        level: 2,
        run: run_incompatible_default_parameter,
    },
    RuleEntry {
        name: "closure.defaultValue",
        level: 2,
        run: run_incompatible_closure_default,
    },
    // Level 0 — filter_var conflicting flags.
    RuleEntry {
        name: "filterVar.flags",
        level: 0,
        run: run_filter_var,
    },
    // Level 6 — missing typehints.
    RuleEntry {
        name: "missingType.return",
        level: 6,
        run: run_missing_function_return_type,
    },
    RuleEntry {
        name: "missingType.parameter",
        level: 6,
        run: run_missing_function_parameter_type,
    },
    RuleEntry {
        name: "missingType.iterableValue",
        level: 6,
        run: run_missing_function_iterable_value,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{codes, codes_version, fixes, replace_fixes, run, run_fixes};

    #[test]
    fn use_referenced_by_nested_arrow_fn_is_not_unused() {
        // Arrow fns auto-capture from the closure's scope: the `use` IS used.
        let src = "<?php\n$id = 1;\n$f = function () use ($id) { return array_map(fn($x) => [$x, $id], [1]); };\n";
        assert!(codes(src, run_unused_closure_uses).is_empty());
    }

    #[test]
    fn fix_removes_sole_unused_closure_use() {
        let src = "<?php\n$a = 1;\n$f = function (int $x) use ($a) { return $x; };\n";
        let fx = replace_fixes(src, run_unused_closure_uses);
        assert_eq!(fx.len(), 1, "{fx:?}");
        let (span, replacement) = &fx[0];
        assert_eq!(replacement, "");
        assert_eq!(&src[span.range()], " use ($a)");
    }

    #[test]
    fn fix_removes_one_of_several_closure_uses() {
        let src = "<?php\n$a = 1;\n$b = 2;\n$f = function () use ($a, $b) { return $b; };\n";
        let fx = replace_fixes(src, run_unused_closure_uses);
        assert_eq!(fx.len(), 1, "{fx:?}");
        assert_eq!(&src[fx[0].0.range()], "$a, ");
        // And the last-item case absorbs the preceding comma.
        let src2 = "<?php\n$a = 1;\n$b = 2;\n$f = function () use ($a, $b) { return $a; };\n";
        let fx2 = replace_fixes(src2, run_unused_closure_uses);
        assert_eq!(fx2.len(), 1, "{fx2:?}");
        assert_eq!(&src2[fx2[0].0.range()], ", $b");
    }

    #[test]
    fn all_unused_closure_uses_share_one_whole_clause_fix() {
        let src = "<?php\n$a = 1;\n$b = 2;\n$f = function () use ($a, $b) { return 1; };\n";
        let fx = replace_fixes(src, run_unused_closure_uses);
        assert_eq!(fx.len(), 2, "{fx:?}");
        assert_eq!(fx[0], fx[1], "identical whole-clause edits must dedup");
        assert_eq!(&src[fx[0].0.range()], " use ($a, $b)");
    }

    #[test]
    fn no_use_removal_fix_when_clause_is_ambiguous() {
        // A string constant containing a lookalike clause: two candidates.
        let src =
            "<?php\n$a = 1;\n$f = function (string $x = 'use ($a)') use ($a) { return $x; };\n";
        for d in run_fixes(src, run_unused_closure_uses) {
            assert!(d.fix.is_none(), "ambiguous clause must not be edited");
        }
    }

    #[test]
    fn fix_deletes_wrong_doc_narrowing_restating_native() {
        // The generated `@return true` on a `: bool` body returning bool: the
        // narrowing is provably wrong and the tag would just restate the
        // native hint — its line is deleted.
        let src = "<?php\nclass C {\n    /**\n     * Authorized?\n     *\n     * @return true\n     */\n    public function authorize(): bool {\n        return $this->x() === true;\n    }\n    private function x(): bool { return true; }\n}\n";
        let fx = replace_fixes(src, run_return_type);
        assert_eq!(fx.len(), 1, "{fx:?}");
        let (span, replacement) = &fx[0];
        assert_eq!(replacement, "");
        // The dangling blank separator line above the tag is absorbed too.
        assert_eq!(&src[span.range()], "     *\n     * @return true\n");
    }

    #[test]
    fn fix_rewrites_doc_narrowing_to_body_union() {
        // Doc narrows `int|string` to `int`; the body returns string only.
        let src = "<?php\n/** @return int */\nfunction f(bool $b): int|string {\n    return $b ? 'a' : 'b';\n}\n";
        let fx = replace_fixes(src, run_return_type);
        assert_eq!(fx.len(), 1, "{fx:?}");
        let (span, replacement) = &fx[0];
        assert_eq!(replacement, "string");
        assert_eq!(&src[span.range()], "int");
    }

    #[test]
    fn no_narrowing_fix_when_doc_is_the_only_contract() {
        // No native hint: the doc IS the contract; the body violating it may
        // be the bug — never rewrite it.
        let src = "<?php\nclass C {\n    /** @return array */\n    public function get() {\n        return null;\n    }\n}\n";
        assert!(replace_fixes(src, run_return_type).is_empty());
    }

    #[test]
    fn no_narrowing_fix_when_body_violates_native() {
        // Body doesn't even fit the native hint — a real bug, don't touch docs.
        let src = "<?php\n/** @return true */\nfunction f(): bool {\n    return 'nope';\n}\n";
        assert!(replace_fixes(src, run_return_type).is_empty());
    }
    use crate::PhpVersion;

    // --- first-class-callable version gate (callable.notSupported) --------

    #[test]
    fn fcc_flagged_below_php81() {
        let v74 = PhpVersion::parse("7.4").unwrap();
        assert_eq!(
            codes_version("<?php strlen(...);", run_first_class_callable_version, v74),
            ["callable.notSupported"]
        );
        assert_eq!(
            codes_version("<?php $o->m(...);", run_first_class_callable_version, v74),
            ["callable.notSupported"]
        );
        assert_eq!(
            codes_version("<?php C::m(...);", run_first_class_callable_version, v74),
            ["callable.notSupported"]
        );
    }

    #[test]
    fn fcc_ok_on_php81_plus() {
        assert!(codes("<?php strlen(...);", run_first_class_callable_version).is_empty()); // default 8.4
                                                                                           // A normal call (no placeholder) is never flagged, even below 8.1.
        let v74 = PhpVersion::parse("7.4").unwrap();
        assert!(
            codes_version("<?php strlen($x);", run_first_class_callable_version, v74).is_empty()
        );
    }

    // --- closure/arrow default parameter type ----------------------------

    #[test]
    fn closure_bad_default_flagged() {
        let src = "<?php $f = function (int $x = 'no') { return $x; };";
        assert_eq!(
            codes(src, run_incompatible_closure_default),
            ["parameter.defaultValue"]
        );
    }

    #[test]
    fn arrow_bad_default_flagged() {
        let src = "<?php $f = fn (int $x = 'no') => $x;";
        assert_eq!(
            codes(src, run_incompatible_closure_default),
            ["parameter.defaultValue"]
        );
    }

    #[test]
    fn closure_good_default_clean() {
        let src = "<?php $f = function (int $x = 5) { return $x; };";
        assert!(codes(src, run_incompatible_closure_default).is_empty());
    }

    #[test]
    fn closure_null_default_clean() {
        let src = "<?php $f = function (int $x = null) { return $x; };";
        assert!(codes(src, run_incompatible_closure_default).is_empty());
    }

    #[test]
    fn closure_untyped_default_clean() {
        let src = "<?php $f = function ($x = 'no') { return $x; };";
        assert!(codes(src, run_incompatible_closure_default).is_empty());
    }

    // --- closure/arrow return type ----------------------------------------

    #[test]
    fn closure_literal_return_type_mismatch_is_flagged() {
        let src = "<?php $f = function (): int { return 'nope'; };";
        let diags = run(src, run_closure_return_type);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["return.type"]
        );
        assert_eq!(
            diags[0].message,
            "Anonymous function should return int but returns 'nope'."
        );
    }

    #[test]
    fn arrow_literal_return_type_mismatch_is_flagged() {
        let src = "<?php $f = fn (): int => 'nope';";
        assert_eq!(codes(src, run_arrow_function_return_type), ["return.type"]);
    }

    #[test]
    fn closure_empty_return_type_mismatch_is_flagged() {
        let src = "<?php $f = function (): int { return; };";
        assert_eq!(codes(src, run_closure_return_type), ["return.empty"]);
    }

    #[test]
    fn closure_void_return_value_is_flagged() {
        let src = "<?php $f = function (): void { return 1; };";
        assert_eq!(codes(src, run_closure_return_type), ["return.void"]);
    }

    #[test]
    fn arrow_void_return_value_is_flagged() {
        let src = "<?php $f = fn (): void => 1;";
        assert_eq!(codes(src, run_arrow_function_return_type), ["return.void"]);
    }

    #[test]
    fn arrow_never_literal_return_is_flagged() {
        let src = "<?php $f = fn (): never => 1;";
        assert_eq!(codes(src, run_arrow_function_return_type), ["return.never"]);
    }

    #[test]
    fn arrow_never_throw_expression_is_clean() {
        let src = "<?php $f = fn (): never => throw new \\Exception();";
        assert!(codes(src, run_arrow_function_return_type).is_empty());
    }

    #[test]
    fn anonymous_return_type_dynamic_expr_is_skipped() {
        let src = "<?php $f = function ($x): int { return $x; }; $g = fn ($x): int => $x;";
        assert!(codes(src, run_closure_return_type).is_empty());
        assert!(codes(src, run_arrow_function_return_type).is_empty());
    }

    #[test]
    fn anonymous_without_native_return_type_is_clean() {
        let src = "<?php $f = function () { return 'nope'; }; $g = fn () => 'nope';";
        assert!(codes(src, run_closure_return_type).is_empty());
        assert!(codes(src, run_arrow_function_return_type).is_empty());
    }

    #[test]
    fn closure_generator_body_is_skipped() {
        let src = "<?php $f = function (): int { yield 1; return 'nope'; };";
        assert!(codes(src, run_closure_return_type).is_empty());
    }

    #[test]
    fn anonymous_named_class_return_type_is_skipped() {
        let src = "<?php class C {} $f = function (): C { return 1; }; $g = fn (): C => 1;";
        assert!(codes(src, run_closure_return_type).is_empty());
        assert!(codes(src, run_arrow_function_return_type).is_empty());
    }

    // --- callable.nonCallable --------------------------------------------

    #[test]
    fn invoking_int_is_flagged() {
        let src = "<?php function f() { $n = 5; return $n(); }";
        assert_eq!(
            codes(src, run_invoke_non_callable),
            ["callable.nonCallable"]
        );
    }

    #[test]
    fn invoking_closure_is_clean() {
        let src = "<?php function f() { $g = fn() => 1; return $g(); }";
        assert!(codes(src, run_invoke_non_callable).is_empty());
    }

    #[test]
    fn invoking_string_is_clean() {
        // A string may be a function name -> not flagged.
        let src = "<?php function f() { $s = 'strlen'; return $s('x'); }";
        assert!(codes(src, run_invoke_non_callable).is_empty());
    }

    #[test]
    fn invoking_callable_or_int_is_maybe_non_callable() {
        let src = "<?php /** @param callable|int $f */ function g($f) { $f(); }";
        assert!(codes(src, run_invoke_non_callable).is_empty());
        assert_eq!(
            codes(src, run_invoke_maybe_non_callable),
            ["callable.nonCallable"]
        );
    }

    #[test]
    fn invoking_string_or_int_is_not_a_safe_maybe_callable_report() {
        let src = "<?php /** @param string|int $f */ function g($f) { $f(); }";
        assert!(codes(src, run_invoke_maybe_non_callable).is_empty());
    }

    #[test]
    fn named_call_is_not_invocation() {
        assert!(codes("<?php strlen('x');", run_invoke_non_callable).is_empty());
    }

    // --- implode castable-to-string --------------------------------------

    #[test]
    fn implode_array_of_arrays_is_flagged() {
        // $x is array<int, array<...>> -> elements not castable to string.
        let src = "<?php $x = [[1], [2]]; echo implode(',', $x);";
        assert_eq!(codes(src, run_implode_castable), ["argument.type"]);
    }

    #[test]
    fn implode_array_of_strings_is_clean() {
        let src = "<?php $x = ['a', 'b']; echo implode(',', $x);";
        assert!(codes(src, run_implode_castable).is_empty());
    }

    #[test]
    fn implode_array_of_ints_is_clean() {
        let src = "<?php $x = [1, 2]; echo implode(',', $x);";
        assert!(codes(src, run_implode_castable).is_empty());
    }

    #[test]
    fn implode_single_arg_array_of_arrays_is_flagged() {
        let src = "<?php $x = [[1]]; echo implode($x);";
        assert_eq!(codes(src, run_implode_castable), ["argument.type"]);
    }

    #[test]
    fn implode_untyped_array_is_clean() {
        let src = "<?php function f(array $a) { return implode(',', $a); }";
        assert!(codes(src, run_implode_castable).is_empty());
    }

    // --- parameter name rules --------------------------------------------

    #[test]
    fn redefined_parameter_is_flagged() {
        assert_eq!(
            codes("<?php function f($a, $a) {}", run_redefined_parameters),
            ["parameter.duplicate"]
        );
    }

    #[test]
    fn distinct_parameters_are_clean() {
        assert!(codes("<?php function f($a, $b) {}", run_redefined_parameters).is_empty());
    }

    #[test]
    fn redefined_parameter_in_closure_is_flagged() {
        assert_eq!(
            codes("<?php $f = function ($x, $x) {};", run_redefined_parameters),
            ["parameter.duplicate"]
        );
    }

    #[test]
    fn this_as_parameter_is_flagged() {
        assert_eq!(
            codes("<?php function f($this) {}", run_invalid_parameter_name),
            ["parameter.this"]
        );
    }

    #[test]
    fn superglobal_as_parameter_is_flagged() {
        assert_eq!(
            codes("<?php function f($_GET) {}", run_invalid_parameter_name),
            ["parameter.superglobal"]
        );
    }

    #[test]
    fn ordinary_parameter_name_is_clean() {
        assert!(codes("<?php function f($data) {}", run_invalid_parameter_name).is_empty());
    }

    #[test]
    fn variadic_not_last_is_flagged() {
        assert_eq!(
            codes("<?php function f(...$a, $b) {}", run_variadic_parameters),
            ["parameter.variadicNotLast"]
        );
    }

    #[test]
    fn variadic_last_is_clean() {
        assert!(codes("<?php function f($a, ...$b) {}", run_variadic_parameters).is_empty());
    }

    // --- inner functions -------------------------------------------------

    #[test]
    fn inner_function_is_flagged() {
        assert_eq!(
            codes(
                "<?php function outer() { function inner() {} }",
                run_inner_function
            ),
            ["function.inner"]
        );
    }

    #[test]
    fn top_level_function_is_clean() {
        assert!(codes("<?php function a() {} function b() {}", run_inner_function).is_empty());
    }

    #[test]
    fn inner_function_in_method_is_flagged() {
        let src = "<?php class C { function m() { function inner() {} } }";
        assert_eq!(codes(src, run_inner_function), ["function.inner"]);
    }

    #[test]
    fn function_inside_closure_is_flagged() {
        let src = "<?php $f = function () { function inner() {} };";
        assert_eq!(codes(src, run_inner_function), ["function.inner"]);
    }

    // --- closure use rules -----------------------------------------------

    #[test]
    fn closure_use_this_is_flagged() {
        assert_eq!(
            codes(
                "<?php $f = function () use ($this) {};",
                run_invalid_lexical_use
            ),
            ["closure.useThis"]
        );
    }

    #[test]
    fn closure_use_superglobal_is_flagged() {
        assert_eq!(
            codes(
                "<?php $f = function () use ($_GET) {};",
                run_invalid_lexical_use
            ),
            ["closure.useSuperGlobal"]
        );
    }

    #[test]
    fn closure_use_duplicate_param_is_flagged() {
        assert_eq!(
            codes(
                "<?php $f = function ($x) use ($x) {};",
                run_invalid_lexical_use
            ),
            ["closure.useDuplicate"]
        );
    }

    #[test]
    fn closure_use_normal_is_clean() {
        assert!(codes(
            "<?php $y = 1; $f = function () use ($y) { echo $y; };",
            run_invalid_lexical_use
        )
        .is_empty());
    }

    #[test]
    fn unused_closure_use_is_flagged() {
        assert_eq!(
            codes(
                "<?php $y = 1; $f = function () use ($y) {};",
                run_unused_closure_uses
            ),
            ["closure.unusedUse"]
        );
    }

    #[test]
    fn used_closure_use_is_clean() {
        assert!(codes(
            "<?php $y = 1; $f = function () use ($y) { return $y; };",
            run_unused_closure_uses
        )
        .is_empty());
    }

    #[test]
    fn by_ref_closure_use_is_never_unused() {
        assert!(codes(
            "<?php $y = 1; $f = function () use (&$y) {};",
            run_unused_closure_uses
        )
        .is_empty());
    }

    #[test]
    fn outer_use_is_not_used_by_uncaptured_inner_closure_body() {
        let src = r#"<?php
            $f = function () use ($x) {
                $g = function () {
                    echo $x;
                };
            };
        "#;
        assert_eq!(codes(src, run_unused_closure_uses), ["closure.unusedUse"]);
    }

    #[test]
    fn outer_use_forwarded_to_inner_closure_use_is_clean() {
        let src = r#"<?php
            $f = function () use ($x) {
                $g = function () use ($x) {
                    echo $x;
                };
            };
        "#;
        assert!(codes(src, run_unused_closure_uses).is_empty());
    }

    // --- call to non-existent function -----------------------------------

    #[test]
    fn call_to_unknown_function_is_flagged() {
        assert_eq!(
            codes(
                "<?php totally_made_up_fn();",
                run_call_to_non_existent_function
            ),
            ["function.notFound"]
        );
    }

    #[test]
    fn call_to_builtin_is_clean() {
        assert!(codes("<?php strlen('x');", run_call_to_non_existent_function).is_empty());
    }

    #[test]
    fn call_to_user_function_is_clean() {
        let src = "<?php function my_helper() {} my_helper();";
        assert!(codes(src, run_call_to_non_existent_function).is_empty());
    }

    // --- function name case ----------------------------------------------

    #[test]
    fn function_name_case_mismatch_is_flagged() {
        let src = "<?php function MyHelper() {} myhelper();";
        assert_eq!(codes(src, run_function_name_case), ["function.nameCase"]);
    }

    #[test]
    fn function_name_correct_case_is_clean() {
        let src = "<?php function MyHelper() {} MyHelper();";
        assert!(codes(src, run_function_name_case).is_empty());
    }

    // --- printf parameters -----------------------------------------------

    #[test]
    fn printf_too_few_values_is_flagged() {
        assert_eq!(
            codes("<?php sprintf('%s %d', 'x');", run_printf_parameters),
            ["argument.sprintf"]
        );
    }

    #[test]
    fn printf_correct_values_is_clean() {
        assert!(codes("<?php sprintf('%s %d', 'x', 1);", run_printf_parameters).is_empty());
    }

    #[test]
    fn printf_literal_percent_is_not_a_placeholder() {
        assert!(codes("<?php sprintf('100%% done');", run_printf_parameters).is_empty());
    }

    #[test]
    fn printf_positional_placeholder_is_counted() {
        // Two distinct positions → 2 values needed.
        assert!(codes(
            "<?php sprintf('%1$s %2$s', 'a', 'b');",
            run_printf_parameters
        )
        .is_empty());
        assert_eq!(
            codes("<?php sprintf('%1$s %2$s', 'a');", run_printf_parameters),
            ["argument.sprintf"]
        );
    }

    #[test]
    fn printf_non_literal_format_is_skipped() {
        assert!(codes(
            "<?php $f = '%s'; sprintf($f, 'a', 'b', 'c');",
            run_printf_parameters
        )
        .is_empty());
    }

    #[test]
    fn namespaced_user_sprintf_shadowing_builtin_is_clean() {
        let src = r#"<?php
            namespace App;
            function sprintf($format): string { return $format; }
            sprintf('%s %d', 'x');
        "#;
        assert!(codes(src, run_printf_parameters).is_empty());
    }

    // --- define parameters -----------------------------------------------

    #[test]
    fn define_with_third_arg_is_flagged() {
        assert_eq!(
            codes("<?php define('X', 1, true);", run_define_parameters),
            ["argument.unused"]
        );
    }

    #[test]
    fn define_with_two_args_is_clean() {
        assert!(codes("<?php define('X', 1);", run_define_parameters).is_empty());
    }

    #[test]
    fn namespaced_user_define_shadowing_builtin_is_clean() {
        let src = r#"<?php
            namespace App;
            function define($name, $value, $caseInsensitive): void {}
            define('X', 1, true);
        "#;
        assert!(codes(src, run_define_parameters).is_empty());
    }

    // --- argument count --------------------------------------------------

    #[test]
    fn too_few_arguments_is_flagged() {
        let src = "<?php function f($a, $b) {} f(1);";
        assert_eq!(codes(src, run_argument_count), ["arguments.count"]);
    }

    #[test]
    fn too_many_arguments_is_flagged() {
        let src = "<?php function f($a) {} f(1, 2);";
        assert_eq!(codes(src, run_argument_count), ["arguments.count"]);
    }

    /// Regression: the message used to pluralize "required" ("2 requireds") and
    /// the too-many branch reported `{max} required` even when some parameters
    /// were optional. phpstan never pluralizes "required" and uses `R-M required`
    /// for a range, `at least R required` for a variadic.
    #[test]
    fn argument_count_messages_match_phpstan() {
        let msg = |src: &str| run(src, run_argument_count)[0].message.clone();
        assert_eq!(
            msg("<?php function needsTwo($a, $b) {} needsTwo(1);"),
            "Function needsTwo invoked with 1 parameter, 2 required."
        );
        assert_eq!(
            msg("<?php function needsTwo($a, $b) {} needsTwo();"),
            "Function needsTwo invoked with 0 parameters, 2 required."
        );
        assert_eq!(
            msg("<?php function range1($a, $b = 1) {} range1(1, 2, 3);"),
            "Function range1 invoked with 3 parameters, 1-2 required."
        );
        assert_eq!(
            msg("<?php function vari($a, $b, ...$rest) {} vari(1);"),
            "Function vari invoked with 1 parameter, at least 2 required."
        );
    }

    /// Regression: methods reading `func_get_args()` were exempt from
    /// too-many-args but the function twin had no such guard.
    #[test]
    fn function_reading_func_get_args_accepts_extras() {
        let src = "<?php function extras() { return func_get_args(); } extras(1, 2, 3);";
        assert!(codes(src, run_argument_count).is_empty());
        let src = "<?php function nums() { return func_num_args(); } nums(1, 2);";
        assert!(codes(src, run_argument_count).is_empty());
        // Too FEW arguments is still reported — the exemption is one-sided.
        let src = "<?php function needs($a, $b) { return func_get_args(); } needs(1);";
        assert_eq!(codes(src, run_argument_count), ["arguments.count"]);
    }

    #[test]
    fn correct_argument_count_is_clean() {
        let src = "<?php function f($a, $b = 2) {} f(1); f(1, 2);";
        assert!(codes(src, run_argument_count).is_empty());
    }

    #[test]
    fn variadic_accepts_extra_arguments() {
        let src = "<?php function f($a, ...$rest) {} f(1, 2, 3, 4);";
        assert!(codes(src, run_argument_count).is_empty());
    }

    // --- first-class-callable on non-existent function -------------------

    #[test]
    fn first_class_callable_unknown_is_flagged() {
        assert_eq!(
            codes("<?php $f = totally_made_up_fn(...);", run_function_callable),
            ["function.notFound"]
        );
    }

    #[test]
    fn first_class_callable_builtin_is_clean() {
        assert!(codes("<?php $f = strlen(...);", run_function_callable).is_empty());
    }

    // --- argument types --------------------------------------------------

    #[test]
    fn wrong_argument_type_is_flagged() {
        assert_eq!(
            codes("<?php function f(int $x) {} f('nope');", run_argument_types),
            ["argument.type"]
        );
    }

    #[test]
    fn correct_argument_type_is_clean() {
        assert!(codes("<?php function f(int $x) {} f(42);", run_argument_types).is_empty());
        // int widens to float.
        assert!(codes("<?php function f(float $x) {} f(1);", run_argument_types).is_empty());
    }

    #[test]
    fn argument_type_from_local_flow() {
        let src = "<?php function f(int $x) {} $v = 'str'; f($v);";
        assert_eq!(codes(src, run_argument_types), ["argument.type"]);
    }

    #[test]
    fn argument_type_inside_arrow_body_is_flagged() {
        let src = "<?php function takes_int(int $x): void {} function f(): void { $cb = fn(string $s) => takes_int($s); }";
        assert_eq!(codes(src, run_argument_types), ["argument.type"]);
    }

    #[test]
    fn argument_type_inside_array_filter_callback_is_flagged() {
        let src = r#"<?php
        function takes_int(int $x): void {}
        /** @param array<string, string> $items */
        function f(array $items): void {
            array_filter($items, fn($v) => takes_int($v));
        }
        "#;
        assert_eq!(codes(src, run_argument_types), ["argument.type"]);
    }

    #[test]
    fn argument_type_from_generator_foreach_key_is_flagged() {
        let src = r#"<?php
        class User {}
        function takes_string(string $x): void {}
        /** @return \Generator<int, User, void, void> */
        function users(): \Generator { yield new User(); }
        function f(): void {
            foreach (users() as $i => $u) {
                takes_string($i);
            }
        }
        "#;
        assert_eq!(codes(src, run_argument_types), ["argument.type"]);
    }

    #[test]
    fn argument_type_inside_preg_replace_callback_is_flagged() {
        let src = r#"<?php
        function takes_string(string $x): void {}
        function f(string $s): void {
            preg_replace_callback('/x/', fn($matches) => takes_string($matches), $s);
        }
        "#;
        assert_eq!(codes(src, run_argument_types), ["argument.type"]);
    }

    #[test]
    fn argument_type_from_precise_array_keys_result_is_flagged() {
        let src = r#"<?php
        function takes_int(int $x): void {}
        /** @param array<string, string> $items */
        function f(array $items): void {
            takes_int(array_keys($items)[0]);
        }
        "#;
        assert_eq!(codes(src, run_argument_types), ["argument.type"]);
    }

    #[test]
    fn argument_type_from_precise_array_column_result_is_flagged() {
        let src = r#"<?php
        function takes_int(int $x): void {}
        /** @param list<array{name: string}> $rows */
        function f(array $rows): void {
            takes_int(array_column($rows, 'name')[0]);
        }
        "#;
        assert_eq!(codes(src, run_argument_types), ["argument.type"]);
    }

    #[test]
    fn argument_type_from_callable_variable_array_map_result_is_flagged() {
        let src = r#"<?php
        class User { public function name(): string {} }
        function takes_int(int $x): void {}
        /** @param list<User> $users */
        function f(array $users): void {
            $cb = fn(User $u): string => $u->name();
            takes_int(array_map($cb, $users)[0]);
        }
        "#;
        assert_eq!(codes(src, run_argument_types), ["argument.type"]);
    }

    #[test]
    fn argument_type_from_collection_map_result_is_flagged() {
        let src = r#"<?php
        class User { public function name(): string {} }
        function takes_int(int $x): void {}
        /** @template T */
        class Collection {
            /** @return T */
            public function first() {}
            public function map(callable $callback) {}
        }
        /** @param Collection<User> $users */
        function f(Collection $users): void {
            takes_int($users->map(fn($u) => $u->name())->first());
        }
        "#;
        assert_eq!(codes(src, run_argument_types), ["argument.type"]);
    }

    #[test]
    fn unknown_arg_type_is_lenient() {
        // $u is never assigned -> mixed -> no diagnostic.
        assert!(codes("<?php function f(int $x) {} f($u);", run_argument_types).is_empty());
        // mixed parameter accepts anything.
        assert!(codes("<?php function f($x) {} f('s');", run_argument_types).is_empty());
    }

    // --- vprintf / vsprintf array parameters -----------------------------

    #[test]
    fn vsprintf_too_few_array_values_is_flagged() {
        assert_eq!(
            codes(
                "<?php vsprintf('%s %d', ['x']);",
                run_printf_array_parameters
            ),
            ["argument.vsprintf"]
        );
    }

    #[test]
    fn vsprintf_correct_array_values_is_clean() {
        assert!(codes(
            "<?php vsprintf('%s %d', ['x', 1]);",
            run_printf_array_parameters
        )
        .is_empty());
    }

    #[test]
    fn vprintf_too_few_array_values_is_flagged() {
        assert_eq!(
            codes(
                "<?php vprintf('%s %s %s', ['a', 'b']);",
                run_printf_array_parameters
            ),
            ["argument.vprintf"]
        );
    }

    #[test]
    fn vsprintf_non_literal_array_is_skipped() {
        assert!(codes(
            "<?php $a = []; vsprintf('%s', $a);",
            run_printf_array_parameters
        )
        .is_empty());
    }

    #[test]
    fn vsprintf_spread_array_is_skipped() {
        assert!(codes(
            "<?php vsprintf('%s %s', [...$xs]);",
            run_printf_array_parameters
        )
        .is_empty());
    }

    // --- duplicate function declaration ----------------------------------

    #[test]
    fn duplicate_function_is_flagged() {
        assert_eq!(
            codes(
                "<?php function f() {} function f() {}",
                run_duplicate_function
            ),
            ["function.duplicate"]
        );
    }

    #[test]
    fn duplicate_function_case_insensitive() {
        assert_eq!(
            codes(
                "<?php function Foo() {} function foo() {}",
                run_duplicate_function
            ),
            ["function.duplicate"]
        );
    }

    #[test]
    fn same_short_function_name_in_different_namespaces_is_clean() {
        assert!(codes(
            "<?php namespace A { function f() {} } namespace B { function f() {} }",
            run_duplicate_function
        )
        .is_empty());
        assert!(codes(
            "<?php namespace A; function f() {} namespace B; function f() {}",
            run_duplicate_function
        )
        .is_empty());
    }

    #[test]
    fn duplicate_function_in_same_namespace_is_flagged() {
        assert_eq!(
            codes(
                "<?php namespace A { function f() {} } namespace A { function F() {} }",
                run_duplicate_function
            ),
            ["function.duplicate"]
        );
    }

    #[test]
    fn distinct_functions_are_clean() {
        assert!(codes(
            "<?php function a() {} function b() {}",
            run_duplicate_function
        )
        .is_empty());
    }

    #[test]
    fn inner_function_does_not_count_as_duplicate() {
        // The inner `f` is conditional (handled by function.inner), not a top-level
        // redeclaration of the outer `f`.
        let src = "<?php function outer() { function f() {} } function f() {}";
        assert!(codes(src, run_duplicate_function).is_empty());
    }

    // --- nullsafe returned by reference ----------------------------------

    #[test]
    fn return_nullsafe_by_ref_is_flagged() {
        assert_eq!(
            codes(
                "<?php function &f($o) { return $o?->bar; }",
                run_return_nullsafe_by_ref
            ),
            ["nullsafe.byRef"]
        );
    }

    #[test]
    fn return_nullsafe_by_ref_through_index_is_flagged() {
        assert_eq!(
            codes(
                "<?php function &f($o) { return $o?->bar[0]; }",
                run_return_nullsafe_by_ref
            ),
            ["nullsafe.byRef"]
        );
    }

    #[test]
    fn return_plain_by_ref_is_clean() {
        assert!(codes(
            "<?php function &f($o) { return $o->bar; }",
            run_return_nullsafe_by_ref
        )
        .is_empty());
    }

    #[test]
    fn return_nullsafe_not_by_ref_is_clean() {
        assert!(codes(
            "<?php function f($o) { return $o?->bar; }",
            run_return_nullsafe_by_ref
        )
        .is_empty());
    }

    #[test]
    fn return_nullsafe_by_ref_method_is_flagged() {
        let src = "<?php class C { function &m($o) { return $o?->bar; } }";
        assert_eq!(codes(src, run_return_nullsafe_by_ref), ["nullsafe.byRef"]);
    }

    #[test]
    fn arrow_fn_nullsafe_by_ref_is_flagged() {
        assert_eq!(
            codes(
                "<?php $f = fn &($o) => $o?->bar;",
                run_arrow_nullsafe_by_ref
            ),
            ["nullsafe.byRef"]
        );
    }

    #[test]
    fn arrow_fn_nullsafe_not_by_ref_is_clean() {
        assert!(codes("<?php $f = fn ($o) => $o?->bar;", run_arrow_nullsafe_by_ref).is_empty());
    }

    // --- missing return typehint -----------------------------------------

    #[test]
    fn missing_return_type_is_flagged() {
        assert_eq!(
            codes(
                "<?php function f() { return 1; }",
                run_missing_function_return_type
            ),
            ["missingType.return"]
        );
    }

    #[test]
    fn native_return_type_is_clean() {
        assert!(codes(
            "<?php function f(): int { return 1; }",
            run_missing_function_return_type
        )
        .is_empty());
    }

    #[test]
    fn phpdoc_return_type_is_clean() {
        let src = "<?php /** @return int */ function f() { return 1; }";
        assert!(codes(src, run_missing_function_return_type).is_empty());
    }

    // --- missing parameter typehint --------------------------------------

    #[test]
    fn missing_parameter_type_is_flagged() {
        assert_eq!(
            codes(
                "<?php function f($a): void {}",
                run_missing_function_parameter_type
            ),
            ["missingType.parameter"]
        );
    }

    #[test]
    fn native_parameter_type_is_clean() {
        assert!(codes(
            "<?php function f(int $a): void {}",
            run_missing_function_parameter_type
        )
        .is_empty());
    }

    #[test]
    fn phpdoc_parameter_type_is_clean() {
        let src = "<?php /** @param int $a */ function f($a): void {}";
        assert!(codes(src, run_missing_function_parameter_type).is_empty());
    }

    #[test]
    fn phpdoc_param_does_not_match_different_name() {
        // `@param` is for `$b`, not `$a` -> `$a` still untyped.
        let src = "<?php /** @param int $b */ function f($a): void {}";
        assert_eq!(
            codes(src, run_missing_function_parameter_type),
            ["missingType.parameter"]
        );
    }

    #[test]
    fn conditional_nested_function_still_flagged() {
        // Coverage check for the region-based traversal: a conditionally
        // declared function is still visited.
        let src = "<?php if (true) { function nested() { return 1; } }";
        assert_eq!(
            codes(src, run_missing_function_return_type),
            ["missingType.return"]
        );
    }

    // --- `--fix` repairs for the missing-typehint rules -------------------

    #[test]
    fn fix_attached_for_inferred_function_return() {
        let src = "<?php\nfunction f() {\n    return 'x';\n}\n";
        let fx = fixes(src, run_missing_function_return_type);
        let line_start = src.find("function f").unwrap() as u32;
        assert_eq!(
            fx,
            [(
                "@return string".to_string(),
                php_diagnostics::FixAnchor::NewDocAt(line_start),
                String::new()
            )]
        );
    }

    #[test]
    fn fix_function_param_from_call_sites() {
        let src = "<?php\nfunction g($x): void {}\ng(1);\ng(2);\n";
        let fx = fixes(src, run_missing_function_parameter_type);
        assert_eq!(fx.len(), 1);
        assert_eq!(fx[0].0, "@param int $x");
    }

    #[test]
    fn fix_function_return_in_namespace_uses_short_class_name() {
        let src =
            "<?php\nnamespace App;\nclass User {}\nfunction u() {\n    return new User();\n}\n";
        let fx = fixes(src, run_missing_function_return_type);
        assert_eq!(fx.len(), 1);
        assert_eq!(fx[0].0, "@return User");
    }

    #[test]
    fn fix_function_return_void_for_valueless_body() {
        let src = "<?php\nfunction side(int $x) { echo $x; }\n";
        let fx = fixes(src, run_missing_function_return_type);
        assert_eq!(fx.len(), 1, "{fx:?}");
        assert_eq!(fx[0].0, "@return void");
    }

    #[test]
    fn no_void_fix_for_generator_function() {
        let src = "<?php\nfunction g() { yield 1; }\n";
        for d in run_fixes(src, run_missing_function_return_type) {
            assert!(d.fix.is_none());
        }
    }

    #[test]
    fn fix_param_iterable_value_from_call_sites() {
        // Explicitly-`array`-typed param refined from observed arguments.
        let src = "<?php\nfunction f(array $rows): void {}\nf(['a', 'b']);\nf(['c']);\n";
        let fx = fixes(src, run_missing_function_iterable_value);
        assert_eq!(fx.len(), 1, "{fx:?}");
        assert_eq!(fx[0].0, "@param list<string> $rows");
    }

    #[test]
    fn no_param_iterable_fix_without_refining_call_sites() {
        for src in [
            // Never called: no evidence.
            "<?php function f(array $rows): void {}",
            // Called with an unrefined array: doesn't refine.
            "<?php function g(): array { return []; } function f(array $rows): void {} f(g());",
        ] {
            for d in run_fixes(src, run_missing_function_iterable_value) {
                assert!(d.fix.is_none(), "{src}");
            }
        }
    }

    #[test]
    fn fix_return_iterable_value_from_body() {
        let src = "<?php\nfunction f(): array {\n    return ['a' => 1];\n}\n";
        let fx = fixes(src, run_missing_function_iterable_value);
        assert_eq!(fx.len(), 1, "{fx:?}");
        assert_eq!(fx[0].0, "@return array{a: int}");
    }

    #[test]
    fn no_iterable_fix_for_generator_or_unrefined_body() {
        for src in [
            // The helper's own return is bare `array`: no refinement.
            "<?php function h(): array { return one(); } function one(): array { return []; }",
            // A bare `return;` leaves a path untyped.
            "<?php function f(): array { if (true) { return; } return [1]; }",
        ] {
            for d in run_fixes(src, run_missing_function_iterable_value) {
                assert!(d.fix.is_none(), "{src}");
            }
        }
    }

    #[test]
    fn no_function_fix_without_evidence() {
        let src = "<?php function f($x) {}";
        for d in run_fixes(src, run_missing_function_parameter_type)
            .into_iter()
            .chain(run_fixes(src, run_missing_function_return_type))
        {
            assert!(d.fix.is_none(), "{:?}", d.message);
        }
    }

    // --- call statement with no side effects -----------------------------

    #[test]
    fn pure_builtin_statement_is_flagged() {
        assert_eq!(
            codes("<?php strlen('x');", run_call_statement_no_side_effects),
            ["function.resultUnused"]
        );
    }

    #[test]
    fn pure_builtin_value_used_is_clean() {
        assert!(codes(
            "<?php $n = strlen('x');",
            run_call_statement_no_side_effects
        )
        .is_empty());
    }

    #[test]
    fn pure_builtin_echoed_is_clean() {
        assert!(codes(
            "<?php echo strlen('x');",
            run_call_statement_no_side_effects
        )
        .is_empty());
    }

    #[test]
    fn impure_builtin_statement_is_clean() {
        // `printf` has a side effect (output) -> not flagged.
        assert!(codes("<?php printf('x');", run_call_statement_no_side_effects).is_empty());
    }

    #[test]
    fn user_function_statement_is_clean() {
        let src = "<?php function f() {} f();";
        assert!(codes(src, run_call_statement_no_side_effects).is_empty());
    }

    #[test]
    fn namespaced_user_strlen_shadowing_builtin_is_clean() {
        let src = r#"<?php
            namespace App;
            function strlen($s): void { echo $s; }
            strlen('x');
        "#;
        assert!(codes(src, run_call_statement_no_side_effects).is_empty());
    }

    #[test]
    fn pure_builtin_statement_inside_closure_is_flagged() {
        let src = "<?php $f = function (): void { strlen('x'); };";
        assert_eq!(
            codes(src, run_call_statement_no_side_effects),
            ["function.resultUnused"]
        );
    }

    #[test]
    fn nodiscard_function_statement_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = "<?php #[NoDiscard] function f(): int { return 1; } f();";
        assert_eq!(
            codes_version(src, run_call_statement_no_discard, v85),
            ["function.resultDiscarded"]
        );
    }

    #[test]
    fn nodiscard_function_statement_is_version_gated() {
        let src = "<?php #[NoDiscard] function f(): int { return 1; } f();";
        assert!(codes(src, run_call_statement_no_discard).is_empty());
    }

    #[test]
    fn nodiscard_function_statement_inside_closure_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src =
            "<?php #[NoDiscard] function f(): int { return 1; } $c = function (): void { f(); };";
        assert_eq!(
            codes_version(src, run_call_statement_no_discard, v85),
            ["function.resultDiscarded"]
        );
    }

    #[test]
    fn void_cast_plain_function_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = "<?php function f(): int { return 1; } (void) f();";
        assert_eq!(
            codes_version(src, run_call_statement_no_discard, v85),
            ["function.inVoidCast"]
        );
    }

    #[test]
    fn void_cast_nodiscard_function_is_clean_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = "<?php #[NoDiscard] function f(): int { return 1; } (void) f();";
        assert!(codes_version(src, run_call_statement_no_discard, v85).is_empty());
    }

    #[test]
    fn standalone_first_class_callable_nodiscard_function_is_clean_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = "<?php #[NoDiscard] function f(): int { return 1; } f(...);";
        assert!(codes_version(src, run_call_statement_no_discard, v85).is_empty());
    }

    #[test]
    fn nodiscard_dynamic_string_callable_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = "<?php #[NoDiscard] function f(): int { return 1; } $cb = 'f'; $cb();";
        assert_eq!(
            codes_version(src, run_call_statement_no_discard, v85),
            ["callable.resultDiscarded"]
        );
    }

    #[test]
    fn void_cast_dynamic_string_callable_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = "<?php function f(): int { return 1; } $cb = 'f'; (void) $cb();";
        assert_eq!(
            codes_version(src, run_call_statement_no_discard, v85),
            ["callable.inVoidCast"]
        );
    }

    #[test]
    fn pipe_into_nodiscard_function_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = "<?php #[NoDiscard] function f(int $i): int { return $i; } 5 |> f(...);";
        assert_eq!(
            codes_version(src, run_call_statement_no_discard, v85),
            ["function.resultDiscarded"]
        );
    }

    #[test]
    fn void_cast_pipe_into_plain_function_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = "<?php function f(int $i): int { return $i; } (void) (5 |> f(...));";
        assert_eq!(
            codes_version(src, run_call_statement_no_discard, v85),
            ["function.inVoidCast"]
        );
    }

    #[test]
    fn pipe_arrow_into_nodiscard_function_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src =
            "<?php #[NoDiscard] function f(int $i): int { return $i; } 5 |> (fn($x) => f($x));";
        assert_eq!(
            codes_version(src, run_call_statement_no_discard, v85),
            ["function.resultDiscarded"]
        );
    }

    // --- useless function return value -----------------------------------

    #[test]
    fn print_r_value_without_true_is_flagged() {
        assert_eq!(
            codes("<?php $s = print_r($x);", run_useless_return_value),
            ["function.uselessReturnValue"]
        );
    }

    #[test]
    fn print_r_with_true_is_clean() {
        assert!(codes("<?php $s = print_r($x, true);", run_useless_return_value).is_empty());
    }

    #[test]
    fn print_r_with_false_is_flagged() {
        assert_eq!(
            codes("<?php $s = print_r($x, false);", run_useless_return_value),
            ["function.uselessReturnValue"]
        );
    }

    #[test]
    fn print_r_as_statement_is_clean() {
        // Bare statement -> result not used -> not this rule's concern.
        assert!(codes("<?php print_r($x);", run_useless_return_value).is_empty());
    }

    #[test]
    fn var_export_value_without_true_is_flagged() {
        assert_eq!(
            codes("<?php $s = var_export($x);", run_useless_return_value),
            ["function.uselessReturnValue"]
        );
    }

    // --- array_values on a list ------------------------------------------

    #[test]
    fn array_values_of_list_is_flagged() {
        // A `list<int>`-typed value: array_values() is a no-op. (An array literal
        // infers as array<int,int>, not list, so we use a typed param.)
        let src = "<?php /** @param list<int> $x */ function f(array $x) { array_values($x); }";
        assert_eq!(codes(src, run_array_values), ["arrayValues.list"]);
    }

    #[test]
    fn array_values_of_map_is_clean() {
        // A keyed array is not a list -> array_values is meaningful.
        let src = "<?php function f(array $a) { return array_values($a); }";
        assert!(codes(src, run_array_values).is_empty());
    }

    #[test]
    fn array_values_named_arg_is_skipped() {
        let src = "<?php $x = [1, 2]; array_values(array: $x);";
        assert!(codes(src, run_array_values).is_empty());
    }

    #[test]
    fn array_values_after_key_dropping_functions_is_meaningful() {
        // array_filter/array_unique/array_diff preserve keys while dropping
        // entries, so their result is NOT a list even when the input was —
        // re-indexing with array_values() is exactly what you do next.
        let src = r#"<?php
/** @param list<string> $x */
function f(array $x): void {
    array_values(array_filter($x, fn ($v) => $v !== ''));
    array_values(array_unique($x));
    array_values(array_diff($x, ['a']));
}
"#;
        assert!(codes(src, run_array_values).is_empty());
    }

    #[test]
    fn array_values_after_array_map_over_filtered_input_is_meaningful() {
        // array_map over ONE array preserves that array's keys: mapping a
        // filtered (holey) array yields a holey array, not a list.
        let src = r#"<?php
/** @param list<string> $x */
function f(array $x): void {
    array_values(array_map(fn ($v) => (string) $v, array_filter($x)));
}
"#;
        assert!(codes(src, run_array_values).is_empty());
    }

    #[test]
    fn array_values_after_array_map_over_list_is_flagged() {
        // Mapping a true list yields a list — array_values() is a no-op there.
        let src = r#"<?php
/** @param list<string> $x */
function f(array $x): void {
    array_values(array_map(fn ($v) => (string) $v, $x));
}
"#;
        assert_eq!(codes(src, run_array_values), ["arrayValues.list"]);
    }

    // --- array_filter literal arrays --------------------------------------

    #[test]
    fn array_filter_empty_literal_is_flagged() {
        assert_eq!(
            codes("<?php array_filter([]);", run_array_filter),
            ["arrayFilter.empty"]
        );
    }

    #[test]
    fn array_filter_all_truthy_literal_is_flagged() {
        assert_eq!(
            codes("<?php array_filter([1, 'x', true]);", run_array_filter),
            ["arrayFilter.same"]
        );
    }

    #[test]
    fn array_filter_all_falsy_literal_is_flagged() {
        assert_eq!(
            codes(
                "<?php array_filter([0, '', '0', false, null]);",
                run_array_filter
            ),
            ["arrayFilter.alwaysEmpty"]
        );
    }

    #[test]
    fn array_filter_mixed_literal_truthiness_is_clean() {
        assert!(codes("<?php array_filter([0, 1]);", run_array_filter).is_empty());
    }

    #[test]
    fn array_filter_dynamic_literal_value_is_clean() {
        assert!(codes("<?php array_filter([0, $x]);", run_array_filter).is_empty());
    }

    #[test]
    fn array_filter_with_callback_is_skipped() {
        assert!(codes("<?php array_filter([0], 'strlen');", run_array_filter).is_empty());
    }

    // --- castable to string array args -----------------------------------

    #[test]
    fn array_diff_of_arrays_is_flagged() {
        let src = "<?php $a = [[1]]; $b = [[2]]; array_diff($a, $b);";
        // Both args have non-stringable element types.
        assert_eq!(
            codes(src, run_parameter_castable_to_string),
            ["argument.type", "argument.type"]
        );
    }

    #[test]
    fn array_combine_first_arg_of_arrays_is_flagged() {
        let src = "<?php $a = [[1]]; $b = ['x']; array_combine($a, $b);";
        // Only the first argument is checked for array_combine.
        assert_eq!(
            codes(src, run_parameter_castable_to_string),
            ["argument.type"]
        );
    }

    #[test]
    fn array_diff_of_strings_is_clean() {
        let src = "<?php $a = ['x']; $b = ['y']; array_diff($a, $b);";
        assert!(codes(src, run_parameter_castable_to_string).is_empty());
    }

    #[test]
    fn array_diff_of_ints_is_clean() {
        let src = "<?php $a = [1]; $b = [2]; array_diff($a, $b);";
        assert!(codes(src, run_parameter_castable_to_string).is_empty());
    }

    #[test]
    fn array_diff_untyped_is_clean() {
        let src = "<?php function f(array $a, array $b) { return array_diff($a, $b); }";
        assert!(codes(src, run_parameter_castable_to_string).is_empty());
    }

    // --- array_unique sort-castable --------------------------------------

    #[test]
    fn array_unique_of_arrays_is_flagged() {
        let src = "<?php $a = [[1], [2]]; array_unique($a);";
        assert_eq!(codes(src, run_sort_castable_to_string), ["argument.type"]);
    }

    #[test]
    fn array_unique_of_strings_is_clean() {
        let src = "<?php $a = ['x', 'y']; array_unique($a);";
        assert!(codes(src, run_sort_castable_to_string).is_empty());
    }

    #[test]
    fn array_unique_with_flags_is_skipped() {
        // Two args -> explicit flags -> we don't resolve SORT_* -> skip.
        let src = "<?php $a = [[1]]; array_unique($a, SORT_REGULAR);";
        assert!(codes(src, run_sort_castable_to_string).is_empty());
    }

    // --- castable to number array args -----------------------------------

    #[test]
    fn array_sum_of_arrays_is_flagged() {
        let src = "<?php $a = [[1], [2]]; array_sum($a);";
        assert_eq!(
            codes(src, run_parameter_castable_to_number),
            ["argument.type"]
        );
    }

    #[test]
    fn array_sum_of_ints_is_clean() {
        let src = "<?php $a = [1, 2]; array_sum($a);";
        assert!(codes(src, run_parameter_castable_to_number).is_empty());
    }

    #[test]
    fn array_product_of_strings_is_clean() {
        // strings cast to number (PHP coerces) -> not flagged.
        let src = "<?php $a = ['1', '2']; array_product($a);";
        assert!(codes(src, run_parameter_castable_to_number).is_empty());
    }

    #[test]
    fn array_sum_untyped_is_clean() {
        let src = "<?php function f(array $a) { return array_sum($a); }";
        assert!(codes(src, run_parameter_castable_to_number).is_empty());
    }

    // --- random_int bounds ----------------------------------------------

    #[test]
    fn random_int_min_greater_than_max_is_flagged() {
        assert_eq!(
            codes("<?php random_int(10, 1);", run_random_int_parameters),
            ["argument.type"]
        );
    }

    #[test]
    fn random_int_ordered_bounds_are_clean() {
        assert!(codes("<?php random_int(1, 10);", run_random_int_parameters).is_empty());
    }

    #[test]
    fn random_int_dynamic_bounds_are_clean() {
        assert!(codes("<?php random_int($min, $max);", run_random_int_parameters).is_empty());
    }

    #[test]
    fn random_int_named_args_are_skipped() {
        assert!(codes(
            "<?php random_int(max: 1, min: 10);",
            run_random_int_parameters
        )
        .is_empty());
    }

    // --- incompatible default parameter type -----------------------------

    #[test]
    fn string_default_for_int_param_is_flagged() {
        assert_eq!(
            codes(
                "<?php function f(int $x = 'no') {}",
                run_incompatible_default_parameter
            ),
            ["parameter.defaultValue"]
        );
    }

    #[test]
    fn int_default_for_int_param_is_clean() {
        assert!(codes(
            "<?php function f(int $x = 5) {}",
            run_incompatible_default_parameter
        )
        .is_empty());
    }

    #[test]
    fn null_default_is_always_clean() {
        // A null default implicitly widens the type — never flagged.
        assert!(codes(
            "<?php function f(int $x = null) {}",
            run_incompatible_default_parameter
        )
        .is_empty());
    }

    #[test]
    fn int_default_for_float_param_widens() {
        assert!(codes(
            "<?php function f(float $x = 1) {}",
            run_incompatible_default_parameter
        )
        .is_empty());
    }

    #[test]
    fn int_default_for_bool_param_is_flagged() {
        assert_eq!(
            codes(
                "<?php function f(bool $x = 1) {}",
                run_incompatible_default_parameter
            ),
            ["parameter.defaultValue"]
        );
    }

    #[test]
    fn untyped_param_default_is_clean() {
        assert!(codes(
            "<?php function f($x = 'whatever') {}",
            run_incompatible_default_parameter
        )
        .is_empty());
    }

    #[test]
    fn non_constant_default_is_skipped() {
        // An array default for a string param: array literal -> array type ->
        // is_assignable(array, string) is false BUT it is constant; check it.
        // A constant-reference default cannot be folded -> skipped.
        assert!(codes(
            "<?php function f(int $x = PHP_INT_MAX) {}",
            run_incompatible_default_parameter
        )
        .is_empty());
    }

    // --- filter_var conflicting flags ------------------------------------

    #[test]
    fn filter_var_conflicting_flags_is_flagged() {
        let src = "<?php filter_var($v, FILTER_VALIDATE_INT, FILTER_NULL_ON_FAILURE | FILTER_THROW_ON_FAILURE);";
        assert_eq!(
            codes(src, run_filter_var),
            ["filterVar.nullOnFailureAndThrowOnFailure"]
        );
    }

    #[test]
    fn filter_var_single_flag_is_clean() {
        let src = "<?php filter_var($v, FILTER_VALIDATE_INT, FILTER_NULL_ON_FAILURE);";
        assert!(codes(src, run_filter_var).is_empty());
    }

    #[test]
    fn filter_var_two_args_is_clean() {
        let src = "<?php filter_var($v, FILTER_VALIDATE_INT);";
        assert!(codes(src, run_filter_var).is_empty());
    }

    // --- call_user_func non-callable -------------------------------------

    #[test]
    fn call_user_func_with_int_is_flagged() {
        let src = "<?php $n = 5; call_user_func($n);";
        assert_eq!(codes(src, run_call_user_func), ["argument.type"]);
    }

    #[test]
    fn call_user_func_with_string_is_clean() {
        let src = "<?php call_user_func('strlen', 'x');";
        assert!(codes(src, run_call_user_func).is_empty());
    }

    #[test]
    fn call_user_func_array_with_bool_is_flagged() {
        let src = "<?php $b = true; call_user_func_array($b, []);";
        assert_eq!(codes(src, run_call_user_func), ["argument.type"]);
    }

    #[test]
    fn call_user_func_with_closure_is_clean() {
        let src = "<?php $f = fn() => 1; call_user_func($f);";
        assert!(codes(src, run_call_user_func).is_empty());
    }
}
