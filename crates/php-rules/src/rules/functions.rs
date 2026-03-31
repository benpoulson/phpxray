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

/// `ImplodeParameterCastableToStringRule` — `implode`/`join`'s array argument
/// must have elements castable to string. Uses the type map (`fa.type_of`) +
/// `is_castable_to_string`; only fires when the element type is concrete and
/// definitely not stringable (arrays of arrays, etc.) — false-positive-safe.
fn run_implode_castable(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else { return };
        let Some(r) = resolved_callee(callee, &fmap) else { return };
        if !matches!(global_tail_lower(r).as_deref(), Some("implode") | Some("join")) {
            return;
        }
        if args.iter().any(|a| a.spread || a.placeholder || a.name.is_some()) {
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
                        global_tail_lower(r).unwrap_or_default()
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
        // Built-in stub arity is unreliable (phpstorm-stubs omits defaults on some
        // optional params and mis-counts variadics — phpstan uses a curated
        // functionMap instead). Only check user-defined functions for arity.
        if func.builtin {
            return;
        }
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

/// `CallToFunctionParametersRule` (the argument-**type** half). Each positional
/// argument is checked against the matching parameter's type via the type map +
/// assignability. Lenient: unknown callee, `mixed`/unresolved arg or param types
/// produce no diagnostic.
fn run_argument_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else { return };
        let Some(r) = resolved_callee(callee, &fmap) else { return };
        // Positional, fully-spelled-out calls only (named/spread/first-class break
        // positional pairing).
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
        let display = primary_name(r);
        for (i, arg) in args.iter().enumerate() {
            let Some(param) = func.params.get(i) else { break };
            if param.variadic {
                break; // variadic absorbs the rest; element-type checking is later
            }
            let given = fa.type_of(&arg.value);
            if !crate::is_assignable(fa.reflection, &given, &param.ty) {
                out.push(
                    Diagnostic::error(
                        arg.value.span,
                        format!(
                            "Parameter #{} ${} of function {display} expects {}, {given} given.",
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
// vprintf / vsprintf — array placeholder count (PrintfArrayParametersRule)
// ---------------------------------------------------------------------------

/// `PrintfArrayParametersRule` — for `vprintf`/`vsprintf` with a constant format
/// string and a constant array of values, check the placeholder count against the
/// array's size. We only handle a literal format and a literal `array(...)` of
/// values (no spread/named); otherwise the size is indeterminate and we skip.
fn run_printf_array_parameters(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Call { callee, args } = &e.kind else { return };
        let Some(r) = resolved_callee(callee, &fmap) else { return };
        let Some(tail) = global_tail_lower(r) else { return };
        let name = match tail.as_str() {
            "vprintf" => "vprintf",
            "vsprintf" => "vsprintf",
            _ => return,
        };
        let is_global = match &r.resolution {
            Resolution::Fqn(fqn) => fqn.eq_ignore_ascii_case(name),
            Resolution::Fallback { global, .. } => global.eq_ignore_ascii_case(name),
            _ => false,
        };
        if !is_global {
            return;
        }
        let code = if name == "vprintf" { "argument.vprintf" } else { "argument.vsprintf" };
        if args.iter().any(|a| a.spread || a.placeholder || a.name.is_some()) {
            return;
        }
        if args.is_empty() {
            return; // too few — caught by arg-count.
        }
        let Some(fmt) = literal_string(&args[0].value) else { return };
        let Some(placeholders) = printf_placeholder_count(&fmt) else {
            out.push(
                Diagnostic::error(e.span, format!("Call to {name} contains an invalid placeholder."))
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
        let Some(size) = literal_array_size(&values_arg.value) else { return };
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
    let ph_word = if placeholders == 1 { "placeholder" } else { "placeholders" };
    let val_word = if values == 1 { "value given" } else { "values given" };
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
    for s in &fa.program.stmts {
        collect_top_functions(s, &mut seen, fa, &mut out);
    }
    out
}

fn collect_top_functions(
    s: &Stmt,
    seen: &mut HashSet<String>,
    fa: &FileAnalysis,
    out: &mut Vec<Diagnostic>,
) {
    match &s.kind {
        StmtKind::Function(fd) => {
            let name = fa.interner.resolve(fd.name).to_ascii_lowercase();
            if !seen.insert(name) {
                let display = fa.interner.resolve(fd.name);
                out.push(
                    Diagnostic::error(s.span, format!("Function {display}() declared multiple times."))
                        .with_code("function.duplicate"),
                );
            }
        }
        StmtKind::Namespace { body: Some(b), .. } => {
            for st in b {
                collect_top_functions(st, seen, fa, out);
            }
        }
        StmtKind::Block(b) => {
            for st in b {
                collect_top_functions(st, seen, fa, out);
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
        ExprKind::Prop { base, nullsafe: false, .. } => contains_nullsafe(base),
        ExprKind::MethodCall { recv, nullsafe: false, .. } => contains_nullsafe(recv),
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
                    Diagnostic::error(e.span, "Nullsafe cannot be returned by reference.".to_string())
                        .with_code("nullsafe.byRef"),
                );
            }
        }
        StmtKind::Block(b) => b.iter().for_each(|st| returns_in_stmt(st, out)),
        StmtKind::Namespace { body: Some(b), .. } => b.iter().for_each(|st| returns_in_stmt(st, out)),
        StmtKind::If { then, elseifs, els, .. } => {
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
        StmtKind::Try { body, catches, finally } => {
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
        let ExprKind::ArrowFn(a) = &e.kind else { return };
        if a.by_ref && contains_nullsafe(&a.body) {
            out.push(
                Diagnostic::error(a.body.span, "Nullsafe cannot be returned by reference.".to_string())
                    .with_code("nullsafe.byRef"),
            );
        }
    });
    out
}

// ---------------------------------------------------------------------------
// Missing typehints (MissingFunctionReturn/ParameterTypehintRule, level 6)
// ---------------------------------------------------------------------------

/// `MissingFunctionReturnTypehintRule` — a named function with neither a native
/// return type nor an `@return` PHPDoc tag. (Only top-level/namespace functions;
/// closures/arrow-fns/methods belong to other categories.)
fn run_missing_function_return_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_stmt(fa.program, &mut |s| {
        let StmtKind::Function(fd) = &s.kind else { return };
        if fd.return_type.is_some() {
            return;
        }
        if doc_has_tag(fd.doc.as_deref(), "@return") {
            return;
        }
        let name = fa.interner.resolve(fd.name);
        out.push(
            Diagnostic::error(s.span, format!("Function {name}() has no return type specified."))
                .with_code("missingType.return"),
        );
    });
    out
}

/// `MissingFunctionParameterTypehintRule` — a named function parameter with no
/// native type and no `@param $name` PHPDoc tag.
fn run_missing_function_parameter_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_stmt(fa.program, &mut |s| {
        let StmtKind::Function(fd) = &s.kind else { return };
        let name = fa.interner.resolve(fd.name);
        for p in &fd.params {
            if p.ty.is_some() {
                continue;
            }
            let pname = fa.interner.resolve(p.name);
            if doc_has_param(fd.doc.as_deref(), pname) {
                continue;
            }
            out.push(
                Diagnostic::error(
                    p_span(p),
                    format!("Function {name}() has parameter ${pname} with no type specified."),
                )
                .with_code("missingType.parameter"),
            );
        }
    });
    out
}

/// Conservative scan of a raw docblock for a tag (e.g. `@return`). Any occurrence
/// of the tag — even partial — counts as "specified", to avoid false positives.
fn doc_has_tag(doc: Option<&str>, tag: &str) -> bool {
    doc.is_some_and(|d| d.contains(tag))
}

/// Conservative scan for an `@param ... $name` tag. We accept any `@param` tag
/// that mentions `$name` as a whole word (or a bare `@param`, treating the doc as
/// possibly-complete to stay false-positive-free).
fn doc_has_param(doc: Option<&str>, name: &str) -> bool {
    let Some(d) = doc else { return false };
    // Scan every `@param` occurrence (anywhere — single-line `/** @param int $a */`
    // or a multi-line block) and accept if `$name` appears as a whole variable
    // token before the next `@` tag. `@param-out` etc. count too (any `@param`
    // prefix satisfies the native-type requirement). Conservative: over-matching
    // only suppresses a diagnostic, keeping us false-positive-free.
    let mut search = d;
    while let Some(off) = search.find("@param") {
        let after = &search[off + "@param".len()..];
        let segment = after.split('@').next().unwrap_or(after);
        if word_boundary_var(segment, name) {
            return true;
        }
        search = after;
    }
    false
}

/// Does `rest` mention `$name` as a complete variable token (so `$id` does not
/// match `$identifier`)? Used by `doc_has_param`.
fn word_boundary_var(rest: &str, name: &str) -> bool {
    let needle = format!("${name}");
    let bytes = rest.as_bytes();
    let nlen = needle.len();
    let mut i = 0;
    while let Some(off) = rest[i..].find(&needle) {
        let start = i + off;
        let end = start + nlen;
        let after_ok = end >= bytes.len()
            || !(bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_');
        if after_ok {
            return true;
        }
        i = end;
    }
    false
}

// ---------------------------------------------------------------------------
// Call-as-statement with no side effects (CallToFunctionStatementWithoutSideEffectsRule)
// ---------------------------------------------------------------------------

/// Built-in functions known to be pure / side-effect-free. A conservative subset
/// of phpstan's `@phpstan-pure` stub annotations — chosen so a statement-level
/// call to one is unambiguously a mistake. (We intentionally omit functions whose
/// purity is version- or argument-dependent.)
const PURE_BUILTINS: &[&str] = &[
    "strlen", "count", "sizeof", "array_keys", "array_values", "array_merge", "array_map",
    "array_filter", "array_search", "in_array", "array_key_exists", "implode", "explode",
    "str_repeat", "str_replace", "substr", "strpos", "stripos", "strrpos", "trim", "ltrim",
    "rtrim", "strtolower", "strtoupper", "ucfirst", "ucwords", "lcfirst", "sprintf", "number_format",
    "abs", "ceil", "floor", "round", "max", "min", "intval", "floatval", "strval", "boolval",
    "is_int", "is_string", "is_array", "is_bool", "is_float", "is_null", "is_numeric", "is_object",
    "is_callable", "gettype", "json_encode", "base64_encode", "base64_decode", "urlencode",
    "urldecode", "htmlspecialchars", "htmlentities", "nl2br", "wordwrap", "str_pad", "str_split",
    "array_slice", "array_reverse", "array_unique", "array_flip", "array_sum", "array_product",
    "array_column", "array_combine", "array_fill", "array_pad", "range", "compact",
];

/// `CallToFunctionStatementWithoutSideEffectsRule` — a call to a known pure
/// built-in whose result is thrown away (the call *is* the whole statement). The
/// return value is the only effect, so the statement is dead. Conservative: only
/// flagged for the curated `PURE_BUILTINS` set, and never for a user function
/// (whose purity we can't determine).
fn run_call_statement_no_side_effects(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let fmap = function_refs(fa.resolved_refs);
    let mut out = Vec::new();
    let mut visit = |e: &Expr| {
        let ExprKind::Call { callee, args } = &e.kind else { return };
        // First-class-callable `foo(...)` produces a Closure — that *is* a value
        // worth keeping, so skip.
        if args.len() == 1 && args[0].placeholder {
            return;
        }
        let Some(r) = resolved_callee(callee, &fmap) else { return };
        let Some(tail) = global_tail_lower(r) else { return };
        if !PURE_BUILTINS.contains(&tail.as_str()) {
            return;
        }
        // Only the global function (a namespaced user override is not pure-known).
        let is_global = match &r.resolution {
            Resolution::Fqn(fqn) => fqn.eq_ignore_ascii_case(&tail),
            Resolution::Fallback { global, .. } => global.eq_ignore_ascii_case(&tail),
            _ => false,
        };
        if !is_global {
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

/// Invoke `f` on every expression that appears in *statement position* (the whole
/// value of an `Expr` statement). Descends through blocks/control flow and into
/// function-like bodies (their statement lists), but not into sub-expressions.
fn stmt_level_calls<F: FnMut(&Expr)>(s: &Stmt, f: &mut F) {
    match &s.kind {
        StmtKind::Expr(e) => f(e),
        StmtKind::Block(b) => b.iter().for_each(|st| stmt_level_calls(st, f)),
        StmtKind::Namespace { body: Some(b), .. } => b.iter().for_each(|st| stmt_level_calls(st, f)),
        StmtKind::Function(fd) => fd.body.iter().for_each(|st| stmt_level_calls(st, f)),
        StmtKind::Class(c) => {
            for m in &c.members {
                if let Member::Method(md) = m {
                    if let Some(body) = &md.body {
                        body.iter().for_each(|st| stmt_level_calls(st, f));
                    }
                }
            }
        }
        StmtKind::If { then, elseifs, els, .. } => {
            stmt_level_calls(then, f);
            for ei in elseifs {
                stmt_level_calls(&ei.body, f);
            }
            if let Some(e) = els {
                stmt_level_calls(e, f);
            }
        }
        StmtKind::While { body, .. } | StmtKind::DoWhile { body, .. } => stmt_level_calls(body, f),
        StmtKind::For { body, .. } | StmtKind::Foreach { body, .. } => stmt_level_calls(body, f),
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                c.body.iter().for_each(|st| stmt_level_calls(st, f));
            }
        }
        StmtKind::Try { body, catches, finally } => {
            body.iter().for_each(|st| stmt_level_calls(st, f));
            for c in catches {
                c.body.iter().for_each(|st| stmt_level_calls(st, f));
            }
            if let Some(fin) = finally {
                fin.iter().for_each(|st| stmt_level_calls(st, f));
            }
        }
        StmtKind::Declare { body: Some(b), .. } => stmt_level_calls(b, f),
        _ => {}
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
    let fmap = function_refs(fa.resolved_refs);
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
        let ExprKind::Call { callee, args } = &e.kind else { return };
        if statement_calls.contains(&(e.span.start, e.span.end)) {
            return; // bare statement — result isn't used.
        }
        let Some(r) = resolved_callee(callee, &fmap) else { return };
        let Some(tail) = global_tail_lower(r) else { return };
        let always = match tail.as_str() {
            "var_export" => "null",
            "print_r" => "true",
            "highlight_string" => "true",
            _ => return,
        };
        let is_global = match &r.resolution {
            Resolution::Fqn(fqn) => fqn.eq_ignore_ascii_case(&tail),
            Resolution::Fallback { global, .. } => global.eq_ignore_ascii_case(&tail),
            _ => false,
        };
        if !is_global {
            return;
        }
        if args.iter().any(|a| a.spread || a.placeholder || a.name.is_some()) {
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
        ExprKind::Name(n) => {
            n.fq == php_ast::NameFq::NotFq && n.text.eq_ignore_ascii_case("false")
        }
        ExprKind::Paren(inner) => is_literal_false(inner),
        _ => false,
    }
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
    RuleEntry { name: "argument.printfArray", level: 0, run: run_printf_array_parameters },
    RuleEntry { name: "argument.define", level: 0, run: run_define_parameters },
    RuleEntry { name: "function.duplicate", level: 0, run: run_duplicate_function },
    RuleEntry { name: "nullsafe.byRef", level: 0, run: run_return_nullsafe_by_ref },
    RuleEntry { name: "arrow.nullsafe.byRef", level: 0, run: run_arrow_nullsafe_by_ref },
    // Level 1 — closure use analysis.
    RuleEntry { name: "closure.unusedUse", level: 1, run: run_unused_closure_uses },
    // Level 4 — dead/useless statement-level calls.
    RuleEntry { name: "function.resultUnused", level: 4, run: run_call_statement_no_side_effects },
    RuleEntry { name: "function.uselessReturnValue", level: 4, run: run_useless_return_value },
    // Level 5 — arguments: count + types.
    RuleEntry { name: "arguments.count", level: 5, run: run_argument_count },
    RuleEntry { name: "argument.type", level: 5, run: run_argument_types },
    RuleEntry { name: "argument.implodeCastable", level: 5, run: run_implode_castable },
    // Level 6 — missing typehints.
    RuleEntry { name: "missingType.return", level: 6, run: run_missing_function_return_type },
    RuleEntry { name: "missingType.parameter", level: 6, run: run_missing_function_parameter_type },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

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
            codes("<?php vsprintf('%s %d', ['x']);", run_printf_array_parameters),
            ["argument.vsprintf"]
        );
    }

    #[test]
    fn vsprintf_correct_array_values_is_clean() {
        assert!(
            codes("<?php vsprintf('%s %d', ['x', 1]);", run_printf_array_parameters).is_empty()
        );
    }

    #[test]
    fn vprintf_too_few_array_values_is_flagged() {
        assert_eq!(
            codes("<?php vprintf('%s %s %s', ['a', 'b']);", run_printf_array_parameters),
            ["argument.vprintf"]
        );
    }

    #[test]
    fn vsprintf_non_literal_array_is_skipped() {
        assert!(
            codes("<?php $a = []; vsprintf('%s', $a);", run_printf_array_parameters).is_empty()
        );
    }

    #[test]
    fn vsprintf_spread_array_is_skipped() {
        assert!(
            codes("<?php vsprintf('%s %s', [...$xs]);", run_printf_array_parameters).is_empty()
        );
    }

    // --- duplicate function declaration ----------------------------------

    #[test]
    fn duplicate_function_is_flagged() {
        assert_eq!(
            codes("<?php function f() {} function f() {}", run_duplicate_function),
            ["function.duplicate"]
        );
    }

    #[test]
    fn duplicate_function_case_insensitive() {
        assert_eq!(
            codes("<?php function Foo() {} function foo() {}", run_duplicate_function),
            ["function.duplicate"]
        );
    }

    #[test]
    fn distinct_functions_are_clean() {
        assert!(codes("<?php function a() {} function b() {}", run_duplicate_function).is_empty());
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
            codes("<?php function &f($o) { return $o?->bar; }", run_return_nullsafe_by_ref),
            ["nullsafe.byRef"]
        );
    }

    #[test]
    fn return_nullsafe_by_ref_through_index_is_flagged() {
        assert_eq!(
            codes("<?php function &f($o) { return $o?->bar[0]; }", run_return_nullsafe_by_ref),
            ["nullsafe.byRef"]
        );
    }

    #[test]
    fn return_plain_by_ref_is_clean() {
        assert!(
            codes("<?php function &f($o) { return $o->bar; }", run_return_nullsafe_by_ref).is_empty()
        );
    }

    #[test]
    fn return_nullsafe_not_by_ref_is_clean() {
        assert!(
            codes("<?php function f($o) { return $o?->bar; }", run_return_nullsafe_by_ref).is_empty()
        );
    }

    #[test]
    fn return_nullsafe_by_ref_method_is_flagged() {
        let src = "<?php class C { function &m($o) { return $o?->bar; } }";
        assert_eq!(codes(src, run_return_nullsafe_by_ref), ["nullsafe.byRef"]);
    }

    #[test]
    fn arrow_fn_nullsafe_by_ref_is_flagged() {
        assert_eq!(
            codes("<?php $f = fn &($o) => $o?->bar;", run_arrow_nullsafe_by_ref),
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
            codes("<?php function f() { return 1; }", run_missing_function_return_type),
            ["missingType.return"]
        );
    }

    #[test]
    fn native_return_type_is_clean() {
        assert!(codes("<?php function f(): int { return 1; }", run_missing_function_return_type).is_empty());
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
            codes("<?php function f($a): void {}", run_missing_function_parameter_type),
            ["missingType.parameter"]
        );
    }

    #[test]
    fn native_parameter_type_is_clean() {
        assert!(
            codes("<?php function f(int $a): void {}", run_missing_function_parameter_type).is_empty()
        );
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
        assert!(
            codes("<?php $n = strlen('x');", run_call_statement_no_side_effects).is_empty()
        );
    }

    #[test]
    fn pure_builtin_echoed_is_clean() {
        assert!(
            codes("<?php echo strlen('x');", run_call_statement_no_side_effects).is_empty()
        );
    }

    #[test]
    fn impure_builtin_statement_is_clean() {
        // `printf` has a side effect (output) -> not flagged.
        assert!(
            codes("<?php printf('x');", run_call_statement_no_side_effects).is_empty()
        );
    }

    #[test]
    fn user_function_statement_is_clean() {
        let src = "<?php function f() {} f();";
        assert!(codes(src, run_call_statement_no_side_effects).is_empty());
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
}
