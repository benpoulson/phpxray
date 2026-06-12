//! phpstan category **Keywords** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Keywords/` — 5 rule(s), all level 0.
//! Checklist: docs/phpstan-rules.md.
//!
//! Implemented (all purely syntactic / structural — Keywords are level 0):
//! - `continue.outOfLoop` / `break.outOfLoop` (`ContinueBreakInLoopRule`) —
//!   `continue`/`break` used outside any enclosing loop or switch, taking the
//!   numeric level (`break N;`) into account and stopping at a closure boundary.
//! - `declareStrictTypes.value` / `declareStrictTypes.notFirst`
//!   (`DeclareStrictTypesRule`) — `declare(strict_types=…)` must have `0`/`1` as
//!   its value and be the very first statement of the file.
//! - `goto.labelUndefined` (`GotoUndefinedLabelRule`) — `goto` to a label that is
//!   not defined anywhere in the file.
//! - `label.unused` (`UnusedLabelRule`) — a `label:` that no `goto` references.

use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{Expr, ExprKind, IncludeKind, Member, Param, Stmt, StmtKind};
use php_diagnostics::Diagnostic;
use php_intern::Symbol;
use std::collections::HashSet;
use std::path::Path;

/// `continue` / `break` used outside of a loop or switch.
///
/// Mirrors phpstan's `ContinueBreakInLoopRule`: track the number of enclosing
/// loop/switch statements (`depth`). `switch` `case`s and branching constructs
/// (`if`, blocks, try) are transparent; a loop/switch increments the depth; a
/// closure/arrow-fn/function/method body is a hard boundary (depth resets to 0).
/// A `break N;` / `continue N;` needs `N <= depth`, else the keyword escapes a
/// loop and is flagged. A non-integer level operand is treated as `1` (matching
/// phpstan's fallback when `num` isn't an `Int_`).
fn run_continue_break_in_loop(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    check_cb(&fa.program.stmts, 0, &mut out);
    out
}

fn check_cb(stmts: &[Stmt], depth: u32, out: &mut Vec<Diagnostic>) {
    for s in stmts {
        check_cb_stmt(s, depth, out);
    }
}

fn check_cb_stmt(s: &Stmt, depth: u32, out: &mut Vec<Diagnostic>) {
    match &s.kind {
        StmtKind::Break(level) | StmtKind::Continue(level) => {
            let is_continue = matches!(s.kind, StmtKind::Continue(_));
            let n = match level {
                Some(e) => match &e.kind {
                    ExprKind::Int(v) if *v >= 1 => *v as u32,
                    _ => 1,
                },
                None => 1,
            };
            // Also descend into the level expression (it may contain closures).
            if let Some(e) = level {
                check_cb_in_expr(e, out);
            }
            if n > depth {
                let kw = if is_continue { "continue" } else { "break" };
                out.push(
                    Diagnostic::error(
                        s.span,
                        format!("Keyword {kw} used outside of a loop or a switch statement."),
                    )
                    .with_code(if is_continue {
                        "continue.outOfLoop"
                    } else {
                        "break.outOfLoop"
                    }),
                );
            }
        }
        // Loop bodies increase the reachable depth by one.
        StmtKind::While { body, cond } => {
            check_cb_in_expr(cond, out);
            check_cb_stmt(body, depth + 1, out);
        }
        StmtKind::DoWhile { body, cond } => {
            check_cb_stmt(body, depth + 1, out);
            check_cb_in_expr(cond, out);
        }
        StmtKind::For {
            init,
            cond,
            update,
            body,
        } => {
            for e in init.iter().chain(cond).chain(update) {
                check_cb_in_expr(e, out);
            }
            check_cb_stmt(body, depth + 1, out);
        }
        StmtKind::Foreach {
            subject,
            key,
            value,
            body,
            ..
        } => {
            check_cb_in_expr(subject, out);
            if let Some(k) = key {
                check_cb_in_expr(k, out);
            }
            check_cb_in_expr(value, out);
            check_cb_stmt(body, depth + 1, out);
        }
        StmtKind::Switch { subject, cases } => {
            check_cb_in_expr(subject, out);
            for c in cases {
                if let Some(t) = &c.test {
                    check_cb_in_expr(t, out);
                }
                check_cb(&c.body, depth + 1, out);
            }
        }
        // Branching / grouping constructs are transparent: depth is unchanged.
        StmtKind::If {
            cond,
            then,
            elseifs,
            els,
        } => {
            check_cb_in_expr(cond, out);
            check_cb_stmt(then, depth, out);
            for ei in elseifs {
                check_cb_in_expr(&ei.cond, out);
                check_cb_stmt(&ei.body, depth, out);
            }
            if let Some(e) = els {
                check_cb_stmt(e, depth, out);
            }
        }
        StmtKind::Block(b) => check_cb(b, depth, out),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            check_cb(body, depth, out);
            for c in catches {
                check_cb(&c.body, depth, out);
            }
            if let Some(f) = finally {
                check_cb(f, depth, out);
            }
        }
        StmtKind::Declare { directives, body } => {
            for (_, e) in directives {
                check_cb_in_expr(e, out);
            }
            if let Some(b) = body {
                check_cb_stmt(b, depth, out);
            }
        }
        StmtKind::Namespace { body: Some(b), .. } => check_cb(b, depth, out),
        // Hard boundaries: a function/method body cannot reach an outer loop, so
        // restart the depth at 0.
        StmtKind::Function(fd) => {
            check_cb(&fd.body, 0, out);
            check_cb_param_defaults(&fd.params, out);
        }
        StmtKind::Class(c) => {
            for m in &c.members {
                if let Member::Method(md) = m {
                    if let Some(body) = &md.body {
                        check_cb(body, 0, out);
                    }
                    check_cb_param_defaults(&md.params, out);
                }
            }
        }
        StmtKind::Expr(e) => check_cb_in_expr(e, out),
        StmtKind::Echo(es) | StmtKind::Global(es) | StmtKind::Unset(es) => {
            for e in es {
                check_cb_in_expr(e, out);
            }
        }
        StmtKind::Return(Some(e)) => check_cb_in_expr(e, out),
        _ => {}
    }
}

/// Find closures/arrow-fns inside an expression (each a loop-depth boundary) and
/// re-scan their bodies starting from depth 0.
fn check_cb_in_expr(e: &Expr, out: &mut Vec<Diagnostic>) {
    let mut found: Vec<&Expr> = Vec::new();
    collect_closures(e, &mut found);
    for c in found {
        match &c.kind {
            ExprKind::Closure(cl) => {
                check_cb(&cl.body, 0, out);
                check_cb_param_defaults(&cl.params, out);
            }
            ExprKind::ArrowFn(af) => {
                check_cb_in_expr(&af.body, out);
                check_cb_param_defaults(&af.params, out);
            }
            ExprKind::NewAnon { class, .. } => {
                for m in &class.members {
                    if let Member::Method(md) = m {
                        if let Some(body) = &md.body {
                            check_cb(body, 0, out);
                        }
                        check_cb_param_defaults(&md.params, out);
                    }
                }
            }
            _ => {}
        }
    }
}

fn check_cb_param_defaults(params: &[Param], out: &mut Vec<Diagnostic>) {
    for p in params {
        if let Some(d) = &p.default {
            check_cb_in_expr(d, out);
        }
    }
}

/// Collect every closure / arrow-fn / anon-class expression reachable from `e`
/// *without* descending past one (the boundary handler re-enters its body).
fn collect_closures<'a>(e: &'a Expr, found: &mut Vec<&'a Expr>) {
    use ExprKind::*;
    match &e.kind {
        Closure(_) | ArrowFn(_) | NewAnon { .. } => found.push(e),
        Interpolated(parts) | ShellExec(parts) | Isset(parts) => {
            parts.iter().for_each(|p| collect_closures(p, found));
        }
        VariableVariable(x) | DollarBrace(x) => collect_closures(x, found),
        Array { items, .. } => {
            for it in items {
                if let Some(k) = &it.key {
                    collect_closures(k, found);
                }
                if let Some(v) = &it.value {
                    collect_closures(v, found);
                }
            }
        }
        Call { callee, args } => {
            collect_closures(callee, found);
            args.iter().for_each(|a| collect_closures(&a.value, found));
        }
        MethodCall { recv, args, .. } => {
            collect_closures(recv, found);
            args.iter().for_each(|a| collect_closures(&a.value, found));
        }
        StaticCall { class, args, .. } => {
            collect_closures(class, found);
            args.iter().for_each(|a| collect_closures(&a.value, found));
        }
        New { class, args } => {
            collect_closures(class, found);
            args.iter().for_each(|a| collect_closures(&a.value, found));
        }
        Index { base, index } => {
            collect_closures(base, found);
            if let Some(i) = index {
                collect_closures(i, found);
            }
        }
        Prop { base, .. } => collect_closures(base, found),
        StaticProp { class, .. } | ClassConst { class, .. } => collect_closures(class, found),
        Unary { expr, .. } | Cast { expr, .. } => collect_closures(expr, found),
        Binary { lhs, rhs, .. }
        | Assign { target: lhs, rhs }
        | AssignOp {
            target: lhs, rhs, ..
        }
        | AssignRef { target: lhs, rhs }
        | Coalesce { lhs, rhs } => {
            collect_closures(lhs, found);
            collect_closures(rhs, found);
        }
        Ternary { cond, then, els } => {
            collect_closures(cond, found);
            if let Some(t) = then {
                collect_closures(t, found);
            }
            collect_closures(els, found);
        }
        PreInc(x) | PreDec(x) | PostInc(x) | PostDec(x) => collect_closures(x, found),
        Instanceof { expr, class } => {
            collect_closures(expr, found);
            collect_closures(class, found);
        }
        Clone(x) | Print(x) | Throw(x) | ErrorSuppress(x) | YieldFrom(x) | Eval(x) | Empty(x) => {
            collect_closures(x, found)
        }
        Yield { key, value } => {
            if let Some(k) = key {
                collect_closures(k, found);
            }
            if let Some(v) = value {
                collect_closures(v, found);
            }
        }
        Exit(Some(x)) => collect_closures(x, found),
        Match { subject, arms } => {
            collect_closures(subject, found);
            for arm in arms {
                if let Some(conds) = &arm.conds {
                    conds.iter().for_each(|c| collect_closures(c, found));
                }
                collect_closures(&arm.body, found);
            }
        }
        Include { expr, .. } => collect_closures(expr, found),
        Paren(x) => collect_closures(x, found),
        _ => {}
    }
}

/// `declare(strict_types=…)` must have `0` or `1` as its value, and must be the
/// very first statement of the file.
///
/// Mirrors phpstan's `DeclareStrictTypesRule`. Only the top-level statement list
/// is considered for the "first statement" check (phpstan's `DeclarePositionVisitor`
/// marks the directive first only when it is the very first node).
fn run_declare_strict_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for (i, s) in fa.program.stmts.iter().enumerate() {
        let StmtKind::Declare { directives, .. } = &s.kind else {
            continue;
        };
        for (key, value) in directives {
            if fa.interner.resolve(*key) != "strict_types" {
                continue;
            }
            let is_valid = matches!(&value.kind, ExprKind::Int(v) if *v == 0 || *v == 1);
            if !is_valid {
                out.push(
                    Diagnostic::error(
                        value.span,
                        "Declare strict_types must have 0 or 1 as its value.",
                    )
                    .with_code("declareStrictTypes.value"),
                );
                return out;
            }
            if i != 0 {
                out.push(
                    Diagnostic::error(
                        s.span,
                        "Declare strict_types must be the very first statement.",
                    )
                    .with_code("declareStrictTypes.notFirst"),
                );
            }
            return out;
        }
    }
    out
}

/// `goto LABEL;` where `LABEL` is never defined anywhere in the file.
///
/// Mirrors phpstan's `GotoUndefinedLabelRule`. Gather every defined label
/// file-wide, then flag any `goto` whose target isn't among them.
fn run_goto_undefined_label(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut labels: HashSet<Symbol> = HashSet::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::Label(sym) = &s.kind {
            labels.insert(*sym);
        }
    });

    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::Goto(sym) = &s.kind {
            if !labels.contains(sym) {
                let name = fa.interner.resolve(*sym);
                out.push(
                    Diagnostic::error(s.span, format!("Goto to undefined label '{name}'."))
                        .with_code("goto.labelUndefined"),
                );
            }
        }
    });
    out
}

/// A `label:` that no `goto` ever targets. Mirrors phpstan's `UnusedLabelRule`.
fn run_unused_label(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut used: HashSet<Symbol> = HashSet::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::Goto(sym) = &s.kind {
            used.insert(*sym);
        }
    });

    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::Label(sym) = &s.kind {
            if !used.contains(sym) {
                let name = fa.interner.resolve(*sym);
                out.push(
                    Diagnostic::error(s.span, format!("Label '{name}' is unused."))
                        .with_code("label.unused"),
                );
            }
        }
    });
    out
}

/// `require`, `require_once`, `include`, and `include_once` with a literal
/// absolute path that does not name an existing file. Relative paths are left
/// alone because matching PHPStan's answer requires PHP's include_path and the
/// analyzed file's execution context.
fn run_require_file_exists(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Include { kind, expr } = &e.kind else {
            return;
        };
        let Some(path) = literal_string(expr) else {
            return;
        };
        let p = Path::new(&path);
        if !p.is_absolute() || p.is_file() {
            return;
        }
        let (name, code) = include_name_and_code(*kind);
        out.push(
            Diagnostic::error(
                e.span,
                format!("Path in {name}() \"{path}\" is not a file or it does not exist."),
            )
            .with_code(code),
        );
    });
    out
}

fn literal_string(e: &Expr) -> Option<String> {
    match &e.kind {
        ExprKind::Str(bytes) => std::str::from_utf8(bytes).ok().map(str::to_string),
        ExprKind::Paren(inner) => literal_string(inner),
        _ => None,
    }
}

fn include_name_and_code(kind: IncludeKind) -> (&'static str, &'static str) {
    match kind {
        IncludeKind::Require => ("require", "require.fileNotFound"),
        IncludeKind::RequireOnce => ("require_once", "requireOnce.fileNotFound"),
        IncludeKind::Include => ("include", "include.fileNotFound"),
        IncludeKind::IncludeOnce => ("include_once", "includeOnce.fileNotFound"),
    }
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "continue-break.outOfLoop",
        level: 0,
        run: run_continue_break_in_loop,
    },
    RuleEntry {
        name: "declareStrictTypes",
        level: 0,
        run: run_declare_strict_types,
    },
    RuleEntry {
        name: "goto.labelUndefined",
        level: 0,
        run: run_goto_undefined_label,
    },
    RuleEntry {
        name: "label.unused",
        level: 0,
        run: run_unused_label,
    },
    RuleEntry {
        name: "keyword.requireFileExists",
        level: 0,
        run: run_require_file_exists,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- continue / break out of loop ------------------------------------

    #[test]
    fn break_in_loop_is_clean() {
        assert!(codes(
            "<?php for ($i=0;$i<3;$i++) { break; }",
            run_continue_break_in_loop
        )
        .is_empty());
        assert!(codes(
            "<?php while (true) { continue; }",
            run_continue_break_in_loop
        )
        .is_empty());
        assert!(codes(
            "<?php foreach ($a as $x) { break; }",
            run_continue_break_in_loop
        )
        .is_empty());
        assert!(codes(
            "<?php do { continue; } while (true);",
            run_continue_break_in_loop
        )
        .is_empty());
    }

    #[test]
    fn break_in_switch_is_clean() {
        let src = "<?php switch ($x) { case 1: break; default: break; }";
        assert!(codes(src, run_continue_break_in_loop).is_empty());
    }

    #[test]
    fn break_outside_loop_is_flagged() {
        assert_eq!(
            codes("<?php break;", run_continue_break_in_loop),
            ["break.outOfLoop"]
        );
        assert_eq!(
            codes("<?php continue;", run_continue_break_in_loop),
            ["continue.outOfLoop"]
        );
    }

    #[test]
    fn break_in_if_outside_loop_is_flagged() {
        assert_eq!(
            codes("<?php if ($x) { break; }", run_continue_break_in_loop),
            ["break.outOfLoop"]
        );
    }

    #[test]
    fn break_too_deep_is_flagged() {
        // One loop, but `break 2;` wants two — escapes the only loop.
        assert_eq!(
            codes(
                "<?php for ($i=0;$i<3;$i++) { break 2; }",
                run_continue_break_in_loop
            ),
            ["break.outOfLoop"]
        );
    }

    #[test]
    fn break_two_in_nested_loops_is_clean() {
        let src = "<?php for ($i=0;$i<3;$i++) { for ($j=0;$j<3;$j++) { break 2; } }";
        assert!(codes(src, run_continue_break_in_loop).is_empty());
    }

    #[test]
    fn break_in_switch_inside_loop_counts_both() {
        // `break 2;` from inside a switch nested in a loop reaches the loop.
        let src = "<?php for ($i=0;$i<3;$i++) { switch ($i) { case 1: break 2; } }";
        assert!(codes(src, run_continue_break_in_loop).is_empty());
    }

    #[test]
    fn break_in_closure_inside_loop_is_flagged() {
        // The closure is a hard boundary: the inner break cannot reach the loop.
        let src = "<?php for ($i=0;$i<3;$i++) { $f = function () { break; }; }";
        assert_eq!(codes(src, run_continue_break_in_loop), ["break.outOfLoop"]);
    }

    #[test]
    fn nested_loop_inside_closure_is_clean() {
        let src = "<?php $f = function () { for ($i=0;$i<3;$i++) { break; } };";
        assert!(codes(src, run_continue_break_in_loop).is_empty());
    }

    // --- declare strict_types --------------------------------------------

    #[test]
    fn declare_strict_types_first_is_clean() {
        assert!(codes("<?php declare(strict_types=1);", run_declare_strict_types).is_empty());
        assert!(codes("<?php declare(strict_types=0);", run_declare_strict_types).is_empty());
    }

    #[test]
    fn declare_strict_types_bad_value_is_flagged() {
        assert_eq!(
            codes("<?php declare(strict_types=2);", run_declare_strict_types),
            ["declareStrictTypes.value"]
        );
    }

    #[test]
    fn declare_strict_types_not_first_is_flagged() {
        let src = "<?php $x = 1; declare(strict_types=1);";
        assert_eq!(
            codes(src, run_declare_strict_types),
            ["declareStrictTypes.notFirst"]
        );
    }

    #[test]
    fn declare_other_directive_is_ignored() {
        assert!(codes("<?php $x = 1; declare(ticks=1);", run_declare_strict_types).is_empty());
    }

    // --- goto / labels ---------------------------------------------------

    #[test]
    fn goto_to_defined_label_is_clean() {
        let src = "<?php goto end; end: echo 1;";
        assert!(codes(src, run_goto_undefined_label).is_empty());
    }

    #[test]
    fn goto_to_undefined_label_is_flagged() {
        let src = "<?php goto nowhere;";
        assert_eq!(
            codes(src, run_goto_undefined_label),
            ["goto.labelUndefined"]
        );
    }

    #[test]
    fn used_label_is_clean() {
        let src = "<?php goto end; end: echo 1;";
        assert!(codes(src, run_unused_label).is_empty());
    }

    #[test]
    fn unused_label_is_flagged() {
        let src = "<?php here: echo 1;";
        assert_eq!(codes(src, run_unused_label), ["label.unused"]);
    }

    // --- include / require file existence --------------------------------

    #[test]
    fn missing_absolute_require_path_is_flagged() {
        let src = "<?php require '/definitely/missing/phpxray-test-file.php';";
        assert_eq!(
            codes(src, run_require_file_exists),
            ["require.fileNotFound"]
        );
    }

    #[test]
    fn missing_absolute_include_once_path_uses_specific_identifier() {
        let src = "<?php include_once '/definitely/missing/phpxray-test-file.php';";
        assert_eq!(
            codes(src, run_require_file_exists),
            ["includeOnce.fileNotFound"]
        );
    }

    #[test]
    fn existing_absolute_require_path_is_clean() {
        let path = std::env::current_dir()
            .unwrap()
            .join("Cargo.toml")
            .display()
            .to_string();
        let src = format!("<?php require '{path}';");
        assert!(codes(&src, run_require_file_exists).is_empty());
    }

    #[test]
    fn relative_require_path_is_skipped() {
        let src = "<?php require 'missing-relative-file.php';";
        assert!(codes(src, run_require_file_exists).is_empty());
    }
}
