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
//! Deferred (need real flow / definedness tracking we don't expose):
//! - `DefinedVariableRule` (`variable.undefined`) — needs per-statement
//!   definedness (phpstan's flow-sensitive scope); our flow pass doesn't track
//!   "definitely undefined", so flagging would risk false positives.
//! - `CompactVariablesRule` (`variable.undefined`) — same: needs the set of
//!   defined variables at the `compact()` call site.
//! - `IssetRule` / `NullCoalesceRule` / `EmptyRule` / `UnsetRule` — need the
//!   "always-set / never-set" certainty of an expression (flow + offsets).
//! - `AssignToByRefExprFromForeachRule`, `ParameterOut*` — need by-ref / out
//!   parameter flow modelling.

#![allow(unused_imports)]
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{ClassDecl, ExprKind, Member, Stmt, StmtKind};
use php_diagnostics::Diagnostic;
use php_resolve::for_each_region;
use php_types::Type;

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

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "global.this", level: 0, run: run_this_in_global },
    RuleEntry { name: "static.this", level: 0, run: run_this_in_static },
    RuleEntry { name: "assign.this", level: 0, run: run_invalid_this_assign },
    RuleEntry { name: "clone.nonObject", level: 3, run: run_variable_cloning },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

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
