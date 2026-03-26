//! phpstan category **Functions** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Functions/` — 41 rule(s) at level(s) 0–6.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to `RULES`
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
//!   `CallToFunctionStatementWithoutSideEffectsRule`, `ReturnNullsafeByRefRule`,
//!   `MissingFunctionParameter/ReturnTypehintRule`, `ExistingClassesIn*Typehints`
//!   (latter handled by unknown-symbol resolution) — all need the type system.

use crate::{return_type_errors, FileAnalysis, RuleEntry};
use php_ast::{ClosureExpr, Expr, ExprKind, Member, Param, Stmt, StmtKind};
use php_diagnostics::Diagnostic;
use php_intern::{Interner, Symbol};
use php_resolve::{Resolution, ResolvedRef};
use std::collections::{HashMap, HashSet};

/// PHP superglobal variable names (without the leading `$`).
/// Mirrors `PHPStan\Analyser\Scope::SUPERGLOBAL_VARIABLES`.
const SUPERGLOBALS: &[&str] = &[
    "GLOBALS", "_SERVER", "_GET", "_POST", "_FILES", "_COOKIE", "_SESSION", "_REQUEST", "_ENV",
];

fn run_return_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    return_type_errors(fa.reflection, fa.program, fa.interner)
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
                    Diagnostic::error(
                        p_span(p),
                        format!("Redefinition of parameter ${name}."),
                    )
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
            if SUPERGLOBALS.contains(&name) {
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
                    Diagnostic::error(p_span(p), "Only the last parameter can be variadic.".to_string())
                        .with_code("parameter.variadicNotLast"),
                );
            }
        }
    });
    out
}

/// The span of a parameter — fall back to its default's span when the param has
/// no span field (it doesn't), so we use the default/attr spans if available,
/// else a zero-length span at the function. Param has no `span`, so synthesize
/// from its name via the surrounding nodes is not possible; use the default or
/// the attr group span when present, otherwise an empty span.
fn p_span(p: &Param) -> php_span::Span {
    if let Some(d) = &p.default {
        return d.span;
    }
    if let Some(t) = &p.ty {
        return t.span;
    }
    php_span::Span::new(0, 0)
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
        StmtKind::If { cond, then, elseifs, els } => {
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
        StmtKind::For { init, cond, update, body } => {
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
        StmtKind::Try { body, catches, finally } => {
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
            parts.iter().for_each(|p| collect_outermost_scopes(p, found));
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
            args.iter().for_each(|a| collect_outermost_scopes(&a.value, found));
        }
        MethodCall { recv, args, .. } => {
            collect_outermost_scopes(recv, found);
            args.iter().for_each(|a| collect_outermost_scopes(&a.value, found));
        }
        StaticCall { class, args, .. } => {
            collect_outermost_scopes(class, found);
            args.iter().for_each(|a| collect_outermost_scopes(&a.value, found));
        }
        New { class, args } => {
            collect_outermost_scopes(class, found);
            args.iter().for_each(|a| collect_outermost_scopes(&a.value, found));
        }
        Index { base, index } => {
            collect_outermost_scopes(base, found);
            if let Some(i) = index {
                collect_outermost_scopes(i, found);
            }
        }
        Prop { base, .. } => collect_outermost_scopes(base, found),
        StaticProp { class, .. } | ClassConst { class, .. } => collect_outermost_scopes(class, found),
        Unary { expr, .. } | Cast { expr, .. } => collect_outermost_scopes(expr, found),
        Binary { lhs, rhs, .. }
        | Assign { target: lhs, rhs }
        | AssignOp { target: lhs, rhs, .. }
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
                    conds.iter().for_each(|c| collect_outermost_scopes(c, found));
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
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Closure(c) = &e.kind else { return };
        let param_names: HashSet<&str> = c.params.iter().map(|p| fa.interner.resolve(p.name)).collect();
        for u in &c.uses {
            let name = fa.interner.resolve(u.name);
            if name == "this" {
                out.push(
                    Diagnostic::error(e.span, "Cannot use $this as lexical variable.".to_string())
                        .with_code("closure.useThis"),
                );
            } else if SUPERGLOBALS.contains(&name) {
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
    });
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
        let ExprKind::Closure(c) = &e.kind else { return };
        if c.uses.is_empty() {
            return;
        }
        let used = collect_used_variables(c, fa.interner);
        for u in &c.uses {
            if u.by_ref {
                continue; // by-ref use is never "unused" — it exports a value.
            }
            let name = fa.interner.resolve(u.name);
            if !used.contains(name) {
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!("Anonymous function has an unused use ${name}."),
                    )
                    .with_code("closure.unusedUse"),
                );
            }
        }
    });
    out
}

/// Every variable name referenced inside a closure's body (and nested closures'
/// own `use` lists / bodies, since a captured var can be passed down).
fn collect_used_variables(c: &ClosureExpr, interner: &Interner) -> HashSet<String> {
    let mut names: HashSet<String> = HashSet::new();
    let body_prog = php_ast::Program { stmts: c.body.clone() };
    crate::walk::for_each_expr(&body_prog, &mut |e| match &e.kind {
        ExprKind::Variable(sym) => {
            names.insert(interner.resolve(*sym).to_string());
        }
        // Nested closures forward captures via their own `use` list.
        ExprKind::Closure(inner) => {
            for u in &inner.uses {
                names.insert(interner.resolve(u.name).to_string());
            }
        }
        _ => {}
    });
    names
}

// ---------------------------------------------------------------------------
// Call-site rules (resolve the callee name via resolved_refs)
// ---------------------------------------------------------------------------

/// Build a span→resolution map for function references so call-site rules can
/// look up the resolved FQN of a callee `Name`.
fn function_refs(refs: &[ResolvedRef]) -> HashMap<(u32, u32), &ResolvedRef> {
    refs.iter()
        .filter(|r| r.kind == php_resolve::RefKind::Function)
        .map(|r| ((r.span.start, r.span.end), r))
        .collect()
}

/// The resolved canonical function name for a call's callee, if it's a plain
/// name reference we resolved. Returns the FQN candidate (namespaced for the
/// fallback case).
fn resolved_callee<'a>(
    callee: &Expr,
    fmap: &HashMap<(u32, u32), &'a ResolvedRef>,
) -> Option<&'a ResolvedRef> {
    if let ExprKind::Name(n) = &callee.kind {
        return fmap.get(&(n.span.start, n.span.end)).copied();
    }
    None
}

/// Look up a function in the project/builtins honouring the global fallback, and
/// return its canonical (declared) name if found.
fn lookup_function_name(fa: &FileAnalysis, r: &ResolvedRef) -> Option<String> {
    match &r.resolution {
        Resolution::Fqn(fqn) => fa.project.function(fqn).map(|e| e.fqn.clone()),
        Resolution::Fallback { namespaced, global } => fa
            .project
            .function(namespaced)
            .or_else(|| fa.project.function(global))
            .map(|e| e.fqn.clone()),
        _ => None,
    }
}

/// `CallToNonExistentFunctionRule` (the `function.notFound` half — `nameCase` is
/// a separate rule below). A call `foo(...)` where `foo` resolves to neither a
/// project function nor a built-in.
fn run_call_to_non_existent_function(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, .. } = &e.kind else { return };
        let Some(r) = resolved_callee(callee, &fmap) else { return };
        let known = match &r.resolution {
            Resolution::Fqn(fqn) => fa.project.has_function(fqn),
            Resolution::Fallback { namespaced, global } => {
                fa.project.has_function(namespaced) || fa.project.has_function(global)
            }
            _ => true,
        };
        if !known {
            let display = primary_name(r);
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
    let fmap = function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, .. } = &e.kind else { return };
        let Some(r) = resolved_callee(callee, &fmap) else { return };
        let Some(canonical) = lookup_function_name(fa, r) else { return };
        // The name the caller used (the resolution's chosen FQN candidate).
        let called = match &r.resolution {
            Resolution::Fqn(fqn) => fqn.clone(),
            Resolution::Fallback { namespaced, global } => {
                if fa.project.has_function(namespaced) {
                    namespaced.clone()
                } else {
                    global.clone()
                }
            }
            _ => return,
        };
        if canonical.eq_ignore_ascii_case(&called) && canonical != called {
            out.push(
                Diagnostic::error(
                    r.span,
                    format!("Call to function {canonical}() with incorrect case: {}", primary_name(r)),
                )
                .with_code("function.nameCase"),
            );
        }
    });
    out
}

/// The function name as written for a message (`\Foo\bar` → `Foo\bar`).
fn primary_name(r: &ResolvedRef) -> String {
    r.name.trim_start_matches('\\').to_string()
}

/// The unqualified lowercase tail of a resolved function (for matching built-in
/// names like `sprintf`, `define`). Returns the global candidate's last segment.
fn global_tail_lower(r: &ResolvedRef) -> Option<String> {
    let candidate = match &r.resolution {
        Resolution::Fqn(fqn) => fqn.as_str(),
        Resolution::Fallback { global, .. } => global.as_str(),
        _ => return None,
    };
    let tail = candidate.rsplit('\\').next().unwrap_or(candidate);
    Some(tail.to_ascii_lowercase())
}

/// `DefineParametersRule` — `define('X', $v, true)` passes the removed 3rd
/// `$case_insensitive` argument (case-insensitive constants gone since PHP 8.0).
fn run_define_parameters(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else { return };
        let Some(r) = resolved_callee(callee, &fmap) else { return };
        // `define` is a global function with no namespace; only match the global.
        if global_tail_lower(r).as_deref() != Some("define") {
            return;
        }
        // Must resolve to the global `define` (not a namespaced user function).
        let is_global = match &r.resolution {
            Resolution::Fqn(fqn) => fqn.eq_ignore_ascii_case("define"),
            Resolution::Fallback { global, .. } => global.eq_ignore_ascii_case("define"),
            _ => false,
        };
        if !is_global {
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

/// `PrintfParametersRule` (count subset). For `printf`/`sprintf` with a constant
/// (single literal) format string, count the conversion specifiers and compare
/// to the number of value args. We only handle a literal format operand (no type
/// inference), and `printf`/`sprintf` (not `sscanf`/`fscanf`, which need runtime
/// `sscanf`).
fn run_printf_parameters(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else { return };
        let Some(r) = resolved_callee(callee, &fmap) else { return };
        let Some(tail) = global_tail_lower(r) else { return };
        let (name, code): (&str, &'static str) = match tail.as_str() {
            "printf" => ("printf", "argument.printf"),
            "sprintf" => ("sprintf", "argument.sprintf"),
            _ => return,
        };
        // Only the global function (no namespaced user override).
        let is_global = match &r.resolution {
            Resolution::Fqn(fqn) => fqn.eq_ignore_ascii_case(name),
            Resolution::Fallback { global, .. } => global.eq_ignore_ascii_case(name),
            _ => false,
        };
        if !is_global {
            return;
        }
        if args.iter().any(|a| a.spread || a.placeholder || a.name.is_some()) {
            return; // unpacking / named args: count is indeterminate.
        }
        // Format is the first argument; need at least it.
        if args.is_empty() {
            return; // too few — caught by the arg-count rule.
        }
        let Some(fmt) = literal_string(&args[0].value) else { return };
        let Some(placeholders) = printf_placeholder_count(&fmt) else {
            out.push(
                Diagnostic::error(e.span, format!("Call to {name} contains an invalid placeholder."))
                    .with_code(code),
            );
            return;
        };
        // Values supplied (all args after the format).
        let values = args.len() - 1;
        if values != placeholders {
            let ph_word = if placeholders == 1 { "placeholder" } else { "placeholders" };
            let val_word = if values == 1 { "value given" } else { "values given" };
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
    let fmap = function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else { return };
        let Some(r) = resolved_callee(callee, &fmap) else { return };
        // Spread/first-class-callable/named args: count is indeterminate or N/A.
        if args.iter().any(|a| a.spread || a.placeholder || a.name.is_some()) {
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
        let Some(func) = fa.reflection.function(&fqn) else { return };
        let supplied = args.len();
        let variadic = func.params.iter().any(|p| p.variadic);
        let required = func.params.iter().filter(|p| !p.optional && !p.variadic).count();
        let max = func.params.len();
        let display = primary_name(r);

        if supplied < required {
            let (s_word, want_word) =
                (plural(supplied, "parameter"), plural(required, "required"));
            out.push(
                Diagnostic::error(
                    e.span,
                    format!(
                        "Function {display} invoked with {supplied} {s_word}, {required} {want_word}."
                    ),
                )
                .with_code("arguments.count"),
            );
        } else if !variadic && supplied > max {
            let s_word = plural(supplied, "parameter");
            out.push(
                Diagnostic::error(
                    e.span,
                    format!(
                        "Function {display} invoked with {supplied} {s_word}, {max} required."
                    ),
                )
                .with_code("arguments.count"),
            );
        }
    });
    out
}

fn plural(n: usize, word: &str) -> String {
    if n == 1 {
        word.to_string()
    } else {
        format!("{word}s")
    }
}

// ---------------------------------------------------------------------------
// First-class-callable on a non-existent function
// ---------------------------------------------------------------------------

/// `FunctionCallableRule` (the `function.notFound` subset for `foo(...)`). A
/// first-class-callable `foo(...)` where `foo` doesn't exist. Type-based
/// callable checks are deferred.
fn run_function_callable(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else { return };
        // First-class-callable form: a single `...` placeholder argument.
        if args.len() != 1 || !args[0].placeholder {
            return;
        }
        let Some(r) = resolved_callee(callee, &fmap) else { return };
        let known = match &r.resolution {
            Resolution::Fqn(fqn) => fa.project.has_function(fqn),
            Resolution::Fallback { namespaced, global } => {
                fa.project.has_function(namespaced) || fa.project.has_function(global)
            }
            _ => true,
        };
        if !known {
            out.push(
                Diagnostic::error(r.span, format!("Function {} not found.", primary_name(r)))
                    .with_code("function.notFound"),
            );
        }
    });
    out
}

// ---------------------------------------------------------------------------
// Registration
// ---------------------------------------------------------------------------

pub(crate) static RULES: &[RuleEntry] = &[
    // Pre-existing: checks each `return <expr>` against the declared return type.
    RuleEntry { name: "return-type", level: 3, run: run_return_type },
    // Level 0 — purely syntactic / name-based.
    RuleEntry { name: "parameter.duplicate", level: 0, run: run_redefined_parameters },
    RuleEntry { name: "parameter.name", level: 0, run: run_invalid_parameter_name },
    RuleEntry { name: "parameter.variadicNotLast", level: 0, run: run_variadic_parameters },
    RuleEntry { name: "function.inner", level: 0, run: run_inner_function },
    RuleEntry { name: "closure.invalidUse", level: 0, run: run_invalid_lexical_use },
    RuleEntry { name: "function.notFound", level: 0, run: run_call_to_non_existent_function },
    RuleEntry { name: "function.nameCase", level: 0, run: run_function_name_case },
    RuleEntry { name: "function.callable", level: 0, run: run_function_callable },
    RuleEntry { name: "argument.printf", level: 0, run: run_printf_parameters },
    RuleEntry { name: "argument.define", level: 0, run: run_define_parameters },
    // Level 1 — closure use analysis.
    RuleEntry { name: "closure.unusedUse", level: 1, run: run_unused_closure_uses },
    // Level 5 — argument count (no type inference).
    RuleEntry { name: "arguments.count", level: 5, run: run_argument_count },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

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
            codes("<?php function outer() { function inner() {} }", run_inner_function),
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
            codes("<?php $f = function () use ($this) {};", run_invalid_lexical_use),
            ["closure.useThis"]
        );
    }

    #[test]
    fn closure_use_superglobal_is_flagged() {
        assert_eq!(
            codes("<?php $f = function () use ($_GET) {};", run_invalid_lexical_use),
            ["closure.useSuperGlobal"]
        );
    }

    #[test]
    fn closure_use_duplicate_param_is_flagged() {
        assert_eq!(
            codes("<?php $f = function ($x) use ($x) {};", run_invalid_lexical_use),
            ["closure.useDuplicate"]
        );
    }

    #[test]
    fn closure_use_normal_is_clean() {
        assert!(codes("<?php $y = 1; $f = function () use ($y) { echo $y; };", run_invalid_lexical_use).is_empty());
    }

    #[test]
    fn unused_closure_use_is_flagged() {
        assert_eq!(
            codes("<?php $y = 1; $f = function () use ($y) {};", run_unused_closure_uses),
            ["closure.unusedUse"]
        );
    }

    #[test]
    fn used_closure_use_is_clean() {
        assert!(codes("<?php $y = 1; $f = function () use ($y) { return $y; };", run_unused_closure_uses).is_empty());
    }

    #[test]
    fn by_ref_closure_use_is_never_unused() {
        assert!(codes("<?php $y = 1; $f = function () use (&$y) {};", run_unused_closure_uses).is_empty());
    }

    // --- call to non-existent function -----------------------------------

    #[test]
    fn call_to_unknown_function_is_flagged() {
        assert_eq!(
            codes("<?php totally_made_up_fn();", run_call_to_non_existent_function),
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
        assert_eq!(codes("<?php sprintf('%s %d', 'x');", run_printf_parameters), ["argument.sprintf"]);
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
        assert!(codes("<?php sprintf('%1$s %2$s', 'a', 'b');", run_printf_parameters).is_empty());
        assert_eq!(
            codes("<?php sprintf('%1$s %2$s', 'a');", run_printf_parameters),
            ["argument.sprintf"]
        );
    }

    #[test]
    fn printf_non_literal_format_is_skipped() {
        assert!(codes("<?php $f = '%s'; sprintf($f, 'a', 'b', 'c');", run_printf_parameters).is_empty());
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
}
