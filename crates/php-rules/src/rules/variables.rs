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
//! Deferred (need real flow / definedness tracking we don't expose):
//! - `CompactVariablesRule` (`variable.undefined`) — needs the set of
//!   defined variables at the `compact()` call site.
//! - `IssetRule` / `NullCoalesceRule` / `EmptyRule` / `UnsetRule` — need the
//!   "always-set / never-set" certainty of an expression (flow + offsets).
//! - **AssignToByRefExprFromForeachRule** (`assign.byRefForeachExpr`, level 0) —
//!   assigning to a dangling by-ref `foreach` variable after the loop (Cap #6).

#![allow(unused_imports)]
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{ClassDecl, Expr, ExprKind, Member, Stmt, StmtKind};
use php_diagnostics::Diagnostic;
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

fn byref_stmt(s: &Stmt, fa: &FileAnalysis, dangling: &mut HashSet<String>, out: &mut Vec<Diagnostic>) {
    let var_name = |e: &Expr| match &e.kind {
        ExprKind::Variable(sym) => Some(fa.interner.resolve(*sym).to_string()),
        _ => None,
    };
    match &s.kind {
        StmtKind::Foreach { value, by_ref, body, .. } => {
            byref_stmt(body, fa, dangling, out);
            if let Some(name) = var_name(value) {
                // by-ref arms the variable; by-value rebinds (clears) it.
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
            byref_stmt(then, fa, dangling, out);
            for ei in elseifs {
                byref_stmt(&ei.body, fa, dangling, out);
            }
            if let Some(e) = els {
                byref_stmt(e, fa, dangling, out);
            }
        }
        StmtKind::While { body, .. } | StmtKind::DoWhile { body, .. } | StmtKind::For { body, .. } => {
            byref_stmt(body, fa, dangling, out);
        }
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                byref_seq(&c.body, fa, dangling, out);
            }
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

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "global.this", level: 0, run: run_this_in_global },
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
