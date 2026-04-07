//! phpstan category **Variables** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Variables/` — 12 rule(s) at level(s) 0,1,3.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented here:
//! - **ThisInGlobalStatementRule** (`global.this`, level 0) — `global $this;`.
//! - **ThisInStaticStatementRule** (`static.this`, level 0) — `static $this;`.
//! - **InvalidVariableAssignRule** (`assign.this`, level 0) — re-assigning
//!   `$this` (`$this = …`, `$this op= …`, `$this =& …`); skipped when the
//!   enclosing class implements `ArrayAccess` (matching phpstan).
//! - **VariableCloningRule** (`clone.nonObject`, level 3) — `clone $x` where the
//!   inferred type is a concrete non-object (scalar/array/null). Lenient: only
//!   fires when the type is *known* non-cloneable.
//!
//! - **DefinedVariableRule** (`variable.undefined`, level 0) — a variable read
//!   that is undefined (or, flow-sensitively, possibly undefined) on the path to
//!   its use. Backed by the Cap #5 definedness lattice (`php_infer`), which bails
//!   conservatively on scopes using `extract`/`$$x`/`eval`/… so it under-reports
//!   rather than false-positives.
//!
//! - **CompactVariablesRule** (`variable.undefined`, level 0) — a constant-string
//!   argument to `compact()` (directly, or nested in an array literal) that names
//!   a variable never bound anywhere in the enclosing scope. We answer at *scope*
//!   granularity (never-assigned ⇒ definitely undefined), not flow-position
//!   granularity: this under-reports (misses use-before-assign) but cannot false-
//!   positive. The scope is skipped entirely when it uses an escape hatch
//!   (`extract`/`$$x`/`eval`/…) that could define arbitrary variables.
//!
//! Deferred (need real flow / definedness tracking we don't expose):
//! - `IssetRule` / `NullCoalesceRule` / `EmptyRule` / `UnsetRule` — need the
//!   "always-set / never-set" certainty of an expression (flow + offsets).
//! - **AssignToByRefExprFromForeachRule** (`assign.byRefForeachExpr`, level 0) —
//!   assigning to a dangling by-ref `foreach` variable after the loop (Cap #6).

#![allow(unused_imports)]
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{
    Arg, ArrowFn, ClassDecl, ClosureExpr, Expr, ExprKind, FunctionDecl, Member, MethodDecl, Param,
    Program, Stmt, StmtKind,
};
use php_diagnostics::Diagnostic;
use php_intern::Interner;
use php_resolve::for_each_region;
use php_types::Type;
use std::collections::HashSet;

// ---------------------------------------------------------------------------
// ThisInGlobalStatementRule — `global $this;`
// ---------------------------------------------------------------------------

/// `global $this;` — `$this` cannot be a global variable.
///
/// Mirrors phpstan's `ThisInGlobalStatementRule`.
fn run_this_in_global(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        let StmtKind::Global(vars) = &s.kind else { return };
        for v in vars {
            if is_this_variable(&v.kind, fa) {
                out.push(
                    Diagnostic::error(v.span, "Cannot use $this as global variable.")
                        .with_code("global.this"),
                );
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// ThisInStaticStatementRule — `static $this;`
// ---------------------------------------------------------------------------

/// `static $this;` — `$this` cannot be a static variable.
///
/// Mirrors phpstan's `ThisInStaticStatementRule`.
fn run_this_in_static(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        let StmtKind::StaticVars(vars) = &s.kind else { return };
        for v in vars {
            if fa.interner.resolve(v.name) == "this" {
                out.push(
                    Diagnostic::error(s.span, "Cannot use $this as static variable.")
                        .with_code("static.this"),
                );
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// InvalidVariableAssignRule — re-assigning `$this`
// ---------------------------------------------------------------------------

/// Re-assigning `$this` (`$this = …`, `$this op= …`, `$this =& …`).
///
/// Mirrors phpstan's `InvalidVariableAssignRule`. The one exception phpstan
/// makes is a class implementing `ArrayAccess` (where `$this[...] = …` desugars
/// differently) — we honour that by skipping when the enclosing class is known
/// to implement `ArrayAccess`.
fn run_invalid_this_assign(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    // Class regions: walk each class body and skip ArrayAccess implementers.
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            visit_for_this_assign(st, fa, scope, None, &mut out);
        }
    });
    out
}

/// `enclosing_class` = the FQN of the class whose body we're inside, if any.
fn visit_for_this_assign(
    st: &Stmt,
    fa: &FileAnalysis,
    scope: &php_resolve::Scope,
    enclosing_class: Option<&str>,
    out: &mut Vec<Diagnostic>,
) {
    // Enter class bodies to learn the enclosing-class FQN (for ArrayAccess).
    if let StmtKind::Class(c) = &st.kind {
        let fqn = c.name.map(|n| scope.qualify(fa.interner.resolve(n)));
        for m in &c.members {
            let Member::Method(md) = m else { continue };
            let Some(body) = &md.body else { continue };
            for s in body {
                scan_stmt_exprs_for_this_assign(s, fa, fqn.as_deref(), out);
            }
        }
        return;
    }
    // Outside a class, descend into control-flow / functions to reach assignments.
    scan_stmt_exprs_for_this_assign(st, fa, enclosing_class, out);
}

fn scan_stmt_exprs_for_this_assign(
    st: &Stmt,
    fa: &FileAnalysis,
    enclosing_class: Option<&str>,
    out: &mut Vec<Diagnostic>,
) {
    let implements_array_access = enclosing_class
        .is_some_and(|c| fa.project.is_subclass_of(c, "ArrayAccess"));
    if implements_array_access {
        return;
    }
    walk::for_each_expr(&php_ast::Program { stmts: vec![st.clone()] }, &mut |e| {
        let target = match &e.kind {
            ExprKind::Assign { target, .. }
            | ExprKind::AssignOp { target, .. }
            | ExprKind::AssignRef { target, .. } => target,
            _ => return,
        };
        if is_this_variable(&target.kind, fa) {
            out.push(
                Diagnostic::error(target.span, "Cannot re-assign $this.").with_code("assign.this"),
            );
        }
    });
}

/// Whether an expression kind is the bare `$this` variable.
fn is_this_variable(kind: &ExprKind, fa: &FileAnalysis) -> bool {
    matches!(kind, ExprKind::Variable(s) if fa.interner.resolve(*s) == "this")
}

// ---------------------------------------------------------------------------
// VariableCloningRule — `clone <non-object>`
// ---------------------------------------------------------------------------

/// `clone $x` where `$x` has a concrete non-object type.
///
/// Mirrors phpstan's `VariableCloningRule` (`clone.nonObject`). Lenient: we only
/// fire when the inferred type is *definitely* non-cloneable (a scalar, array, or
/// null). `mixed`/`object`/class types / unknowns are left alone to avoid false
/// positives.
fn run_variable_cloning(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Clone(inner) = &e.kind else { return };
        let ty = fa.type_of(inner);
        if !is_definitely_non_object(&ty) {
            return;
        }
        // Match phpstan's two message shapes (variable vs. arbitrary expression).
        if let ExprKind::Variable(s) = &inner.kind {
            let name = fa.interner.resolve(*s);
            out.push(
                Diagnostic::error(
                    e.span,
                    format!("Cannot clone non-object variable ${name} of type {ty}."),
                )
                .with_code("clone.nonObject"),
            );
        } else {
            out.push(
                Diagnostic::error(e.span, format!("Cannot clone {ty}."))
                    .with_code("clone.nonObject"),
            );
        }
    });
    out
}

/// A type that is definitely not an object (and thus not cloneable). Conservative:
/// anything composite, generic, templated, or unknown returns `false`.
fn is_definitely_non_object(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Null
            | Type::Bool
            | Type::True
            | Type::False
            | Type::Int
            | Type::Float
            | Type::String
            | Type::Array(_)
            | Type::List(_)
            | Type::LiteralInt(_)
            | Type::LiteralString(_)
    )
}

// ---------------------------------------------------------------------------
// DefinedVariableRule — `variable.undefined`
// ---------------------------------------------------------------------------

/// `variable.undefined` (level 0): a variable read that is *definitely* undefined
/// on the path to its use (phpstan's `Undefined variable:` case). Backed by the
/// Cap #5 definedness lattice.
fn run_defined_variable(fa: &FileAnalysis) -> Vec<Diagnostic> {
    crate::undefined_variables(fa.program, fa.interner)
        .into_iter()
        .filter(|u| u.definite)
        .map(|u| {
            Diagnostic::error(u.span, format!("Undefined variable: ${}", u.name))
                .with_code("variable.undefined")
        })
        .collect()
}

/// `variable.undefined` (level 1): a variable read that is *possibly* undefined
/// (assigned on only some paths). phpstan gates this behind
/// `checkMaybeUndefinedVariables`, enabled from level 1.
fn run_maybe_undefined_variable(fa: &FileAnalysis) -> Vec<Diagnostic> {
    crate::undefined_variables(fa.program, fa.interner)
        .into_iter()
        .filter(|u| !u.definite)
        .map(|u| {
            Diagnostic::error(u.span, format!("Variable ${} might not be defined.", u.name))
                .with_code("variable.undefined")
        })
        .collect()
}

// ---------------------------------------------------------------------------
// AssignToByRefExprFromForeachRule — `assign.byRefForeachExpr`
// ---------------------------------------------------------------------------

/// After `foreach ($arr as &$v) { … }`, `$v` is a dangling reference to the last
/// element; assigning to `$v` afterwards (without `unset($v)`) silently
/// overwrites that element. We track, in execution order within each scope, the
/// set of "dangling" by-ref foreach variables and flag a later plain assignment
/// to one. `unset`/re-binding clears it. Conservative (direct `$v = …` only).
fn run_byref_foreach(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut dangling = HashSet::new();
    byref_seq(&fa.program.stmts, fa, &mut dangling, &mut out);
    out
}

fn byref_seq(stmts: &[Stmt], fa: &FileAnalysis, dangling: &mut HashSet<String>, out: &mut Vec<Diagnostic>) {
    for s in stmts {
        byref_stmt(s, fa, dangling, out);
    }
}

/// Process one branch of a conditional from a clone of the entry dangling set,
/// then shrink `keep` to the variables this branch left dangling (so a variable
/// survives past the conditional only if *no* branch cleared it).
fn byref_branch(
    body: &Stmt,
    fa: &FileAnalysis,
    entry: &HashSet<String>,
    keep: &mut HashSet<String>,
    out: &mut Vec<Diagnostic>,
) {
    let mut d = entry.clone();
    byref_stmt(body, fa, &mut d, out);
    keep.retain(|v| d.contains(v));
}

fn byref_stmt(s: &Stmt, fa: &FileAnalysis, dangling: &mut HashSet<String>, out: &mut Vec<Diagnostic>) {
    let var_name = |e: &Expr| match &e.kind {
        ExprKind::Variable(sym) => Some(fa.interner.resolve(*sym).to_string()),
        _ => None,
    };
    match &s.kind {
        StmtKind::Foreach { key, value, by_ref, body, .. } => {
            // The foreach *header* rebinds key/value to fresh references at the
            // start of the loop, so any prior dangling status for them is cleared
            // before the body runs — assigning to the by-ref variable *inside* its
            // own loop is the legitimate in-place-edit idiom, never a dangling write.
            if let Some(name) = var_name(value) {
                dangling.remove(&name);
            }
            if let Some(k) = key {
                if let Some(name) = var_name(k) {
                    dangling.remove(&name);
                }
            }
            byref_stmt(body, fa, dangling, out);
            // After the loop, a by-ref value variable dangles (it still references
            // the last element); a by-value foreach leaves it rebound (cleared).
            if let Some(name) = var_name(value) {
                if *by_ref {
                    dangling.insert(name);
                } else {
                    dangling.remove(&name);
                }
            }
        }
        StmtKind::Expr(e) => {
            if let ExprKind::Assign { target, .. } = &e.kind {
                if let Some(name) = var_name(target) {
                    if dangling.remove(&name) {
                        out.push(
                            Diagnostic::error(
                                e.span,
                                format!("Assign to ${name} overwrites the last element from array."),
                            )
                            .with_code("assign.byRefForeachExpr"),
                        );
                    }
                }
            }
        }
        StmtKind::Unset(vars) => {
            for v in vars {
                if let Some(name) = var_name(v) {
                    dangling.remove(&name);
                }
            }
        }
        StmtKind::Block(b) => byref_seq(b, fa, dangling, out),
        StmtKind::If { then, elseifs, els, .. } => {
            // Branches are mutually-exclusive paths: process each from a *clone* of
            // the entry set so a foreach arming a variable in one branch doesn't
            // leak into a sibling branch. A variable stays dangling after the `if`
            // only if no branch cleared it (FP-safe).
            let entry = dangling.clone();
            let mut keep = entry.clone();
            byref_branch(then, fa, &entry, &mut keep, out);
            for ei in elseifs {
                byref_branch(&ei.body, fa, &entry, &mut keep, out);
            }
            if let Some(e) = els {
                byref_branch(e, fa, &entry, &mut keep, out);
            }
            *dangling = keep;
        }
        StmtKind::While { body, .. } | StmtKind::DoWhile { body, .. } | StmtKind::For { body, .. } => {
            byref_stmt(body, fa, dangling, out);
        }
        StmtKind::Switch { cases, .. } => {
            let entry = dangling.clone();
            let mut keep = entry.clone();
            for c in cases {
                let mut d = entry.clone();
                byref_seq(&c.body, fa, &mut d, out);
                keep.retain(|v| d.contains(v));
            }
            *dangling = keep;
        }
        StmtKind::Try { body, catches, finally } => {
            byref_seq(body, fa, dangling, out);
            for c in catches {
                byref_seq(&c.body, fa, dangling, out);
            }
            if let Some(f) = finally {
                byref_seq(f, fa, dangling, out);
            }
        }
        // New scopes get a fresh dangling set.
        StmtKind::Function(f) => byref_seq(&f.body, fa, &mut HashSet::new(), out),
        StmtKind::Class(c) => {
            for m in &c.members {
                if let Member::Method(md) = m {
                    if let Some(b) = &md.body {
                        byref_seq(b, fa, &mut HashSet::new(), out);
                    }
                }
            }
        }
        StmtKind::Namespace { body: Some(b), .. } => byref_seq(b, fa, dangling, out),
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// CompactVariablesRule — `compact('undefinedVar')`
// ---------------------------------------------------------------------------

/// PHP superglobals + always-available variables (never "undefined").
const ALWAYS_DEFINED: &[&str] = &[
    "GLOBALS", "_SERVER", "_GET", "_POST", "_FILES", "_COOKIE", "_SESSION", "_REQUEST", "_ENV",
    "this", "http_response_header", "argc", "argv", "php_errormsg",
];

/// Functions that can introduce arbitrary variables into a scope — their presence
/// makes scope-level "never assigned" reasoning unsafe, so we skip the scope.
const ESCAPE_FUNCTIONS: &[&str] = &["extract", "parse_str", "mb_parse_str", "eval", "get_defined_vars"];

/// `compact('x')` (or `compact(['x', 'y'])`) naming a variable that is never
/// bound anywhere in the enclosing scope. Mirrors phpstan's
/// `CompactVariablesRule` for the definite-undefined case (`$scopeHasVariable->no()`).
fn run_compact_variables(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    // Each scope: collect the names it ever binds, then check its compact() calls.
    // The global region is one scope; functions/methods/closures/arrows are their
    // own scopes (a captured/param/global var bound there is "defined").
    check_scope(&fa.program.stmts, &HashSet::new(), fa, &mut out);
    out
}

/// Analyse one scope. `seed` holds names defined by the signature/captures.
fn check_scope(body: &[Stmt], seed: &HashSet<String>, fa: &FileAnalysis, out: &mut Vec<Diagnostic>) {
    // Descend into nested scopes regardless (they're checked independently).
    descend_scopes(body, fa, out);

    if scope_has_escape(body, fa.interner) {
        return; // can't reason about definedness in this scope
    }

    // All variables ever bound anywhere in this scope (flow-insensitive: a name
    // bound on *any* path means it's not "never defined").
    let mut bound: HashSet<String> = seed.clone();
    for s in body {
        collect_bound(s, fa.interner, &mut bound);
    }

    // Check every compact() call in this scope (not crossing into nested scopes).
    for s in body {
        walk::for_each_expr_in_scope(s, &mut |e| {
            let Some(args) = compact_args(e, fa) else { return };
            for arg in args {
                for (name, span) in constant_string_names(&arg.value) {
                    if ALWAYS_DEFINED.contains(&name.as_str()) || bound.contains(&name) {
                        continue;
                    }
                    out.push(
                        Diagnostic::error(
                            span,
                            format!("Call to function compact() contains undefined variable ${name}."),
                        )
                        .with_code("variable.undefined"),
                    );
                }
            }
        });
    }
}

/// Recurse into nested function/method/closure/arrow scopes, seeding each with
/// its parameter (and closure-`use`) names.
fn descend_scopes(body: &[Stmt], fa: &FileAnalysis, out: &mut Vec<Diagnostic>) {
    for s in body {
        match &s.kind {
            StmtKind::Function(f) => check_scope(&f.body, &param_names(&f.params, fa.interner), fa, out),
            StmtKind::Class(c) => {
                for m in &c.members {
                    if let Member::Method(md) = m {
                        if let Some(b) = &md.body {
                            check_scope(b, &param_names(&md.params, fa.interner), fa, out);
                        }
                    }
                }
            }
            StmtKind::Namespace { body: Some(b), .. } => descend_scopes(b, fa, out),
            _ => {}
        }
        // Closures / arrow-fns appear inside expressions; find them too.
        walk::for_each_expr_in_scope(s, &mut |e| match &e.kind {
            ExprKind::Closure(cl) => {
                let mut seed = param_names(&cl.params, fa.interner);
                for u in &cl.uses {
                    seed.insert(fa.interner.resolve(u.name).to_string());
                }
                check_scope(&cl.body, &seed, fa, out);
            }
            ExprKind::ArrowFn(_) => {} // single-expr body can't contain compact() bindings worth checking; arrow captures all outer vars by value anyway
            _ => {}
        });
    }
}

fn param_names(params: &[Param], i: &Interner) -> HashSet<String> {
    params.iter().map(|p| i.resolve(p.name).to_string()).collect()
}

/// If `e` is a call to the global `compact(...)`, return its arguments.
fn compact_args<'a>(e: &'a Expr, _fa: &FileAnalysis) -> Option<&'a [Arg]> {
    let ExprKind::Call { callee, args } = &e.kind else { return None };
    let ExprKind::Name(n) = &callee.kind else { return None };
    let last = n.text.rsplit('\\').next().unwrap_or(&n.text);
    (last.eq_ignore_ascii_case("compact")).then_some(args.as_slice())
}

/// Collect the constant-string variable names an argument denotes: a bare string
/// literal, or string literals nested in an array literal. Each with the span to
/// report at. Non-constant arguments yield nothing (we can't know the name).
fn constant_string_names(e: &Expr) -> Vec<(String, php_span::Span)> {
    let mut out = Vec::new();
    collect_const_strings(e, &mut out);
    out
}

fn collect_const_strings(e: &Expr, out: &mut Vec<(String, php_span::Span)>) {
    match &e.kind {
        ExprKind::Str(bytes) => {
            if let Ok(s) = std::str::from_utf8(bytes) {
                out.push((s.to_string(), e.span));
            }
        }
        ExprKind::Array { items, .. } => {
            for it in items {
                if let Some(v) = &it.value {
                    collect_const_strings(v, out);
                }
            }
        }
        _ => {}
    }
}

/// Whether `body` contains an escape-hatch construct in *this* scope (not
/// crossing into nested function-likes).
fn scope_has_escape(body: &[Stmt], _i: &Interner) -> bool {
    let mut found = false;
    for s in body {
        walk::for_each_expr_in_scope(s, &mut |e| {
            if found {
                return;
            }
            match &e.kind {
                ExprKind::VariableVariable(_)
                | ExprKind::DollarBrace(_)
                | ExprKind::Eval(_)
                | ExprKind::Include { .. } => found = true,
                ExprKind::Call { callee, .. } => {
                    if let ExprKind::Name(n) = &callee.kind {
                        let last = n.text.rsplit('\\').next().unwrap_or(&n.text).to_ascii_lowercase();
                        if ESCAPE_FUNCTIONS.contains(&last.as_str()) {
                            found = true;
                        }
                    }
                }
                _ => {}
            }
        });
    }
    found
}

/// Collect every variable name bound by statement `s` in this scope (assignments,
/// foreach bindings, catch vars, global/static, by-ref call args, list-destructure,
/// `&$x` array elements). Flow-insensitive: any binding on any path counts.
fn collect_bound(s: &Stmt, i: &Interner, bound: &mut HashSet<String>) {
    match &s.kind {
        StmtKind::Global(vars) | StmtKind::Unset(vars) => {
            for v in vars {
                if let ExprKind::Variable(sym) = &v.kind {
                    bound.insert(i.resolve(*sym).to_string());
                }
            }
        }
        StmtKind::StaticVars(vars) => {
            for sv in vars {
                bound.insert(i.resolve(sv.name).to_string());
            }
        }
        StmtKind::Foreach { key, value, body, .. } => {
            if let Some(k) = key {
                bind_target(k, i, bound);
            }
            bind_target(value, i, bound);
            collect_bound(body, i, bound);
        }
        StmtKind::Try { body, catches, finally } => {
            for st in body {
                collect_bound(st, i, bound);
            }
            for c in catches {
                if let Some(v) = c.var {
                    bound.insert(i.resolve(v).to_string());
                }
                for st in &c.body {
                    collect_bound(st, i, bound);
                }
            }
            if let Some(f) = finally {
                for st in f {
                    collect_bound(st, i, bound);
                }
            }
        }
        StmtKind::Block(b) => b.iter().for_each(|st| collect_bound(st, i, bound)),
        StmtKind::If { then, elseifs, els, .. } => {
            collect_bound(then, i, bound);
            for ei in elseifs {
                collect_bound(&ei.body, i, bound);
            }
            if let Some(e) = els {
                collect_bound(e, i, bound);
            }
        }
        StmtKind::While { body, .. } | StmtKind::DoWhile { body, .. } | StmtKind::For { body, .. } => {
            collect_bound(body, i, bound)
        }
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                for st in &c.body {
                    collect_bound(st, i, bound);
                }
            }
        }
        StmtKind::Namespace { body: Some(b), .. } => b.iter().for_each(|st| collect_bound(st, i, bound)),
        StmtKind::Declare { body: Some(b), .. } => collect_bound(b, i, bound),
        // Don't descend into nested function/class scopes for *this* scope's binds.
        StmtKind::Function(_) | StmtKind::Class(_) => {}
        _ => {
            // Any other statement: scan its expressions (in this scope) for the
            // variables they assign/bind.
            walk::for_each_expr_in_scope(s, &mut |e| collect_bound_expr(e, i, bound));
        }
    }
}

/// Collect variables that expression `e` binds (assignment targets, by-ref args).
fn collect_bound_expr(e: &Expr, i: &Interner, bound: &mut HashSet<String>) {
    match &e.kind {
        ExprKind::Assign { target, .. }
        | ExprKind::AssignOp { target, .. }
        | ExprKind::AssignRef { target, .. } => bind_target(target, i, bound),
        ExprKind::PreInc(t) | ExprKind::PreDec(t) | ExprKind::PostInc(t) | ExprKind::PostDec(t) => {
            bind_target(t, i, bound)
        }
        // A bare `$var` passed to a call may be a by-ref out-parameter ⇒ defines it.
        ExprKind::Call { args, .. } | ExprKind::MethodCall { args, .. } | ExprKind::StaticCall { args, .. } => {
            for a in args {
                if let ExprKind::Variable(sym) = &a.value.kind {
                    bound.insert(i.resolve(*sym).to_string());
                }
            }
        }
        _ => {}
    }
}

/// Record the variables an assignment *target* introduces (`$x`, `[$a,$b]`,
/// `$arr[…]` base, `&$x` array elements).
fn bind_target(target: &Expr, i: &Interner, bound: &mut HashSet<String>) {
    match &target.kind {
        ExprKind::Variable(sym) => {
            bound.insert(i.resolve(*sym).to_string());
        }
        ExprKind::Array { items, .. } => {
            for it in items {
                if let Some(v) = &it.value {
                    bind_target(v, i, bound);
                }
            }
        }
        ExprKind::Index { base, .. } => bind_target(base, i, bound),
        _ => {}
    }
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "global.this", level: 0, run: run_this_in_global },
    RuleEntry { name: "variable.undefined/compact", level: 0, run: run_compact_variables },
    RuleEntry { name: "assign.byRefForeachExpr", level: 0, run: run_byref_foreach },
    RuleEntry { name: "static.this", level: 0, run: run_this_in_static },
    RuleEntry { name: "assign.this", level: 0, run: run_invalid_this_assign },
    RuleEntry { name: "variable.undefined", level: 0, run: run_defined_variable },
    RuleEntry { name: "variable.maybeUndefined", level: 1, run: run_maybe_undefined_variable },
    RuleEntry { name: "clone.nonObject", level: 3, run: run_variable_cloning },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- variable.undefined ----------------------------------------------

    #[test]
    fn undefined_variable_is_flagged() {
        assert_eq!(
            codes("<?php function f() { return $x; }", run_defined_variable),
            ["variable.undefined"]
        );
    }

    #[test]
    fn assigned_variable_is_clean() {
        assert!(codes("<?php function f() { $x = 1; return $x; }", run_defined_variable).is_empty());
    }

    #[test]
    fn parameter_is_defined() {
        assert!(codes("<?php function f($x) { return $x; }", run_defined_variable).is_empty());
    }

    #[test]
    fn use_before_assign_is_flagged() {
        assert_eq!(
            codes("<?php function f() { echo $x; $x = 1; }", run_defined_variable),
            ["variable.undefined"]
        );
    }

    #[test]
    fn maybe_undefined_after_if() {
        // $x assigned only in the then-branch -> possibly undefined after.
        let src = "<?php function f($c) { if ($c) { $x = 1; } return $x; }";
        // Not a *definite* undefined, so the level-0 rule stays quiet...
        assert!(codes(src, run_defined_variable).is_empty());
        // ...but the level-1 maybe rule reports it.
        assert_eq!(codes(src, run_maybe_undefined_variable), ["variable.undefined"]);
    }

    #[test]
    fn defined_in_both_branches_is_clean() {
        let src = "<?php function f($c) { if ($c) { $x = 1; } else { $x = 2; } return $x; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn foreach_binding_is_defined_in_body() {
        let src = "<?php function f(array $a) { foreach ($a as $v) { echo $v; } }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn list_destructuring_defines() {
        let src = "<?php function f(array $a) { [$x, $y] = $a; return $x + $y; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn isset_guard_is_not_a_read() {
        let src = "<?php function f() { if (isset($x)) { return 1; } return 0; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn coalesce_left_is_not_a_read() {
        let src = "<?php function f() { return $x ?? 'default'; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn extract_bails_the_scope() {
        // extract() can define arbitrary variables -> no reports for this scope.
        let src = "<?php function f(array $a) { extract($a); return $x; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn byref_call_argument_is_not_flagged() {
        // preg_match defines $m by reference; don't flag the bare-variable arg.
        let src = "<?php function f() { preg_match('/x/', 'x', $m); return $m; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn superglobal_is_defined() {
        assert!(codes("<?php function f() { return $_GET['x']; }", run_defined_variable).is_empty());
    }

    #[test]
    fn global_statement_defines() {
        let src = "<?php function f() { global $config; return $config; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn catch_variable_is_defined() {
        let src = "<?php function f() { try { g(); } catch (\\Exception $e) { return $e; } return null; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn closure_use_is_defined_inside() {
        let src = "<?php function f() { $x = 1; return function () use ($x) { return $x; }; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    // --- variable.undefined/compact --------------------------------------

    #[test]
    fn compact_undefined_variable_is_flagged() {
        let src = "<?php function f() { $a = 1; return compact('a', 'b'); }";
        assert_eq!(codes(src, run_compact_variables), ["variable.undefined"]);
    }

    #[test]
    fn compact_all_defined_is_clean() {
        let src = "<?php function f() { $a = 1; $b = 2; return compact('a', 'b'); }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_parameter_is_defined() {
        let src = "<?php function f($a) { return compact('a'); }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_array_argument_is_checked() {
        let src = "<?php function f() { $a = 1; return compact(['a', 'b']); }";
        assert_eq!(codes(src, run_compact_variables), ["variable.undefined"]);
    }

    #[test]
    fn compact_superglobal_is_defined() {
        let src = "<?php function f() { return compact('_GET'); }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_with_extract_is_skipped() {
        // extract() can define arbitrary variables ⇒ scope skipped (no FP).
        let src = "<?php function f(array $d) { extract($d); return compact('whatever'); }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_non_constant_argument_is_ignored() {
        let src = "<?php function f(string $name) { return compact($name); }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_variable_bound_later_is_clean() {
        // Scope-granular: bound anywhere in the scope ⇒ not "never defined".
        let src = "<?php function f() { $r = compact('a'); $a = 1; return $r; }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_foreach_binding_is_defined() {
        let src = "<?php function f(array $xs) { foreach ($xs as $a) {} return compact('a'); }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_in_method_uses_method_scope() {
        let src = "<?php class C { function m() { $a = 1; return compact('a', 'b'); } }";
        assert_eq!(codes(src, run_compact_variables), ["variable.undefined"]);
    }

    #[test]
    fn compact_in_closure_use_is_defined() {
        let src = "<?php function f() { $a = 1; return function () use ($a) { return compact('a'); }; }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    // --- assign.byRefForeachExpr -----------------------------------------

    #[test]
    fn assign_to_dangling_byref_foreach_var_is_flagged() {
        let src = "<?php function f(array $a) { foreach ($a as &$v) {} $v = 1; }";
        assert_eq!(codes(src, run_byref_foreach), ["assign.byRefForeachExpr"]);
    }

    #[test]
    fn unset_after_foreach_clears_it() {
        let src = "<?php function f(array $a) { foreach ($a as &$v) {} unset($v); $v = 1; }";
        assert!(codes(src, run_byref_foreach).is_empty());
    }

    #[test]
    fn byvalue_foreach_is_clean() {
        let src = "<?php function f(array $a) { foreach ($a as $v) {} $v = 1; }";
        assert!(codes(src, run_byref_foreach).is_empty());
    }

    #[test]
    fn assign_inside_foreach_body_is_clean() {
        let src = "<?php function f(array $a) { foreach ($a as &$v) { $v = 1; } }";
        assert!(codes(src, run_byref_foreach).is_empty());
    }

    #[test]
    fn sibling_branch_foreaches_do_not_leak() {
        // The php-parser NameResolver pattern: separate `foreach (… as &$x) { $x = … }`
        // in mutually-exclusive branches must not flag (each header rebinds $x).
        let src = "<?php function f($n, array $a, array $b) { \
            if ($n === 1) { foreach ($a as &$x) { $x = 1; } } \
            elseif ($n === 2) { foreach ($b as &$x) { $x = 2; } } }";
        assert!(codes(src, run_byref_foreach).is_empty());
    }

    #[test]
    fn reuse_of_byref_var_in_second_foreach_is_clean() {
        // A second `foreach (… as &$v)` rebinds $v; its in-body assign isn't dangling.
        let src = "<?php function f(array $a, array $b) { \
            foreach ($a as &$v) {} foreach ($b as &$v) { $v = 1; } }";
        assert!(codes(src, run_byref_foreach).is_empty());
    }

    // --- global.this -----------------------------------------------------

    #[test]
    fn global_this_is_flagged() {
        assert_eq!(codes("<?php function f() { global $this; }", run_this_in_global), ["global.this"]);
    }

    #[test]
    fn global_other_variable_is_clean() {
        assert!(codes("<?php function f() { global $x, $y; }", run_this_in_global).is_empty());
    }

    // --- static.this -----------------------------------------------------

    #[test]
    fn static_this_is_flagged() {
        assert_eq!(codes("<?php function f() { static $this; }", run_this_in_static), ["static.this"]);
    }

    #[test]
    fn static_other_variable_is_clean() {
        assert!(codes("<?php function f() { static $count = 0; }", run_this_in_static).is_empty());
    }

    // --- assign.this -----------------------------------------------------

    #[test]
    fn reassign_this_is_flagged() {
        let src = "<?php class C { function m() { $this = 1; } }";
        assert_eq!(codes(src, run_invalid_this_assign), ["assign.this"]);
    }

    #[test]
    fn compound_assign_this_is_flagged() {
        let src = "<?php class C { function m() { $this += 1; } }";
        assert_eq!(codes(src, run_invalid_this_assign), ["assign.this"]);
    }

    #[test]
    fn assign_other_variable_is_clean() {
        let src = "<?php class C { function m() { $x = 1; $this->p = 2; } }";
        assert!(codes(src, run_invalid_this_assign).is_empty());
    }

    #[test]
    fn reassign_this_in_array_access_class_is_clean() {
        let src = "<?php class C implements ArrayAccess { function m() { $this = 1; } }";
        assert!(codes(src, run_invalid_this_assign).is_empty());
    }

    #[test]
    fn assign_this_outside_class_is_flagged() {
        // Even at top level / in a plain function PHP rejects re-assigning $this.
        let src = "<?php function f() { $this = 1; }";
        assert_eq!(codes(src, run_invalid_this_assign), ["assign.this"]);
    }

    // --- clone.nonObject -------------------------------------------------

    #[test]
    fn clone_int_literal_is_flagged() {
        assert_eq!(codes("<?php clone 1;", run_variable_cloning), ["clone.nonObject"]);
    }

    #[test]
    fn clone_string_variable_is_flagged() {
        let src = "<?php $x = 'hello'; clone $x;";
        assert_eq!(codes(src, run_variable_cloning), ["clone.nonObject"]);
    }

    #[test]
    fn clone_object_is_clean() {
        let src = "<?php class C {} $x = new C(); clone $x;";
        assert!(codes(src, run_variable_cloning).is_empty());
    }

    #[test]
    fn clone_unknown_type_is_clean() {
        // No inferred type ⇒ mixed ⇒ lenient (no diagnostic).
        let src = "<?php function f($x) { clone $x; }";
        assert!(codes(src, run_variable_cloning).is_empty());
    }
}
