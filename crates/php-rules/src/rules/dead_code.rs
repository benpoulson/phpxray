//! phpstan category **DeadCode** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/DeadCode/` — 9 rule(s) at level(s) 4.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented here (all level 4):
//! - **UnreachableStatementRule** (`deadCode.unreachable`) — a statement that
//!   follows one which always terminates control flow (`return`/`throw`/`break`/
//!   `continue`/`goto`/`exit`).
//! - **UnusedPrivateMethodRule** (`method.unused`) — a `private` method never
//!   referenced anywhere in its class. Conservative: bails (reports nothing) if
//!   the class performs any dynamic method dispatch.
//! - **UnusedPrivateConstantRule** (`classConstant.unused`) — a `private` class
//!   constant never fetched within its class.
//! - **UnusedPrivatePropertyRule** (`property.unused`) — a `private` property
//!   never accessed within its class. Conservative: only the fully-unused case is
//!   reported; the read/write-asymmetry identifiers (`property.onlyRead`,
//!   `property.onlyWritten`, `property.neverRead`, `property.neverWritten`) need
//!   read-vs-write flow tracking and are deferred.
//! - **NoopRule** (`logicalAnd.resultUnused`/`logicalOr.resultUnused`/
//!   `logicalXor.resultUnused`/`ternary.resultUnused`) — a statement-level
//!   expression whose result is discarded for these always-pure operator forms.
//!
//! - **NoopRule** (`expr.resultUnused` / `booleanAnd.resultUnused` /
//!   `booleanOr.resultUnused`) — a statement-level expression whose result is
//!   discarded *and* whose whole subtree is side-effect-free (no call, `new`,
//!   assignment, `++`/`--`, `yield`, `throw`, `exit`, `print`, `include`, `eval`,
//!   `match`, `@`, `clone`, shell-exec). The side-effect guard keeps this
//!   FP-safe — the common `$cond && doThing()` idiom (where the right side has an
//!   effect) is *not* flagged.
//!
//! Deferred:
//! - `CallTo*StatementWithoutImpurePointsRule` (and their purity collectors) —
//!   need cross-function purity analysis (impure-point collection) we don't have.

#![allow(unused_imports)]
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{
    BinOp, ClassConstDecl, ClassDecl, ClassKind, Expr, ExprKind, Member, MemberName, MethodDecl,
    PropertyDecl, Stmt, StmtKind, Visibility,
};
use php_diagnostics::Diagnostic;
use php_intern::Interner;
use php_resolve::for_each_region;
use std::collections::HashSet;

// ---------------------------------------------------------------------------
// UnreachableStatementRule — `deadCode.unreachable`
// ---------------------------------------------------------------------------

/// A statement directly following one that always terminates control flow.
///
/// Mirrors phpstan's `UnreachableStatementRule`. We scan every statement *list*
/// in the file: once a statement is an unconditional terminator (`return`,
/// `throw`, `break`, `continue`, `goto`, `exit`/`die`), the next non-trivial
/// statement in that list is unreachable. Only the first unreachable statement of
/// a list is reported (phpstan reports the unreachable node once per block).
fn run_unreachable(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |_scope, region| {
        check_stmt_list(region, &mut out);
    });
    out
}

/// Walk a statement list, reporting the first statement after a terminator, then
/// recurse into every nested block/body (so each block is checked independently).
fn check_stmt_list(stmts: &[Stmt], out: &mut Vec<Diagnostic>) {
    let mut terminated = false;
    for s in stmts {
        if terminated && !is_ignorable_after_terminator(&s.kind) {
            out.push(
                Diagnostic::error(s.span, "Unreachable statement - code above always terminates.")
                    .with_code("deadCode.unreachable"),
            );
            terminated = false; // report only the first; keep scanning nested blocks
        }
        if terminates(&s.kind) {
            terminated = true;
        }
        recurse_into_blocks(s, out);
    }
}

/// Statements that don't count as "unreachable code" when they trail a
/// terminator: declarations are hoisted by PHP and a bare `;` is a no-op.
fn is_ignorable_after_terminator(kind: &StmtKind) -> bool {
    matches!(
        kind,
        StmtKind::Nop
            | StmtKind::Function(_)
            | StmtKind::Class(_)
            | StmtKind::Label(_)
            | StmtKind::HaltCompiler(_)
            | StmtKind::InlineHtml(_)
    )
}

/// Whether a statement unconditionally ends control flow of its enclosing block.
fn terminates(kind: &StmtKind) -> bool {
    match kind {
        StmtKind::Return(_)
        | StmtKind::Break(_)
        | StmtKind::Continue(_)
        | StmtKind::Goto(_) => true,
        StmtKind::Expr(e) => matches!(e.kind, ExprKind::Throw(_) | ExprKind::Exit(_)),
        _ => false,
    }
}

/// Recurse the reachability check into nested statement lists of `s` so each
/// block (then/else, loop body, case body, try/catch/finally, …) is checked.
fn recurse_into_blocks(s: &Stmt, out: &mut Vec<Diagnostic>) {
    match &s.kind {
        StmtKind::Block(b) => check_stmt_list(b, out),
        StmtKind::If { then, elseifs, els, .. } => {
            check_one(then, out);
            for ei in elseifs {
                check_one(&ei.body, out);
            }
            if let Some(e) = els {
                check_one(e, out);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => check_one(body, out),
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                check_stmt_list(&c.body, out);
            }
        }
        StmtKind::Try { body, catches, finally } => {
            check_stmt_list(body, out);
            for c in catches {
                check_stmt_list(&c.body, out);
            }
            if let Some(fin) = finally {
                check_stmt_list(fin, out);
            }
        }
        StmtKind::Declare { body: Some(b), .. } => check_one(b, out),
        StmtKind::Namespace { body: Some(b), .. } => check_stmt_list(b, out),
        StmtKind::Function(fd) => check_stmt_list(&fd.body, out),
        StmtKind::Class(c) => {
            for m in &c.members {
                if let Member::Method(md) = m {
                    if let Some(body) = &md.body {
                        check_stmt_list(body, out);
                    }
                }
            }
        }
        _ => {}
    }
}

/// Treat a single (possibly non-block) statement as a one-element list so a
/// `if (...) return; unreachable;` written without braces is still checked, and
/// nested blocks inside it are recursed.
fn check_one(s: &Stmt, out: &mut Vec<Diagnostic>) {
    match &s.kind {
        StmtKind::Block(b) => check_stmt_list(b, out),
        _ => recurse_into_blocks(s, out),
    }
}

// ---------------------------------------------------------------------------
// Unused private member rules — shared scanning
// ---------------------------------------------------------------------------

/// What member-name references appear inside a class body, used to decide whether
/// a private member is unused. Conservative by design.
struct MemberRefs {
    /// Identifiers used as a method name (`->m()`, `::m()`) — lowercased.
    method_names: HashSet<String>,
    /// Identifiers used as a class-constant name (`::C`).
    const_names: HashSet<String>,
    /// Identifiers used as a property name (`->p`, `::$p` without `$`).
    prop_names: HashSet<String>,
    /// Every string-literal value in the class (covers callable arrays,
    /// `method_exists`, magic dispatch). A private member whose name appears as a
    /// string literal is treated as used.
    string_literals: HashSet<String>,
    /// The class performs at least one *dynamic* member access (computed member
    /// name). When set, we cannot prove any member unused → bail.
    has_dynamic_member: bool,
}

/// Collect member-name references over a whole class declaration (all member
/// bodies, property/const defaults, attributes, etc.).
fn collect_member_refs(c: &ClassDecl, interner: &Interner) -> MemberRefs {
    let mut refs = MemberRefs {
        method_names: HashSet::new(),
        const_names: HashSet::new(),
        prop_names: HashSet::new(),
        string_literals: HashSet::new(),
        has_dynamic_member: false,
    };
    // Wrap the class in a one-statement program so the shared walker (which
    // crosses scopes) visits every nested expression, including closures.
    let prog = php_ast::Program {
        stmts: vec![Stmt::new(php_span::Span::new(0, 0), StmtKind::Class(c.clone()))],
    };
    walk::for_each_expr(&prog, &mut |e| match &e.kind {
        ExprKind::MethodCall { method, .. } => record_member(method, &mut refs.method_names, interner, &mut refs.has_dynamic_member, true),
        ExprKind::StaticCall { method, .. } => record_member(method, &mut refs.method_names, interner, &mut refs.has_dynamic_member, false),
        ExprKind::Prop { name, .. } => record_member(name, &mut refs.prop_names, interner, &mut refs.has_dynamic_member, true),
        ExprKind::StaticProp { name, .. } => record_member(name, &mut refs.prop_names, interner, &mut refs.has_dynamic_member, false),
        ExprKind::ClassConst { name, .. } => record_member(name, &mut refs.const_names, interner, &mut refs.has_dynamic_member, false),
        ExprKind::Str(bytes) => {
            if let Ok(s) = std::str::from_utf8(bytes) {
                refs.string_literals.insert(s.to_string());
            }
        }
        _ => {}
    });
    refs
}

/// Record a member name into `set` (lowercasing not applied here except by the
/// caller's set semantics), or flag a dynamic access. `::$p` (`MemberName::Var`)
/// is a *static* property reference by its literal name `p`, but `$o->$p`
/// (`var_is_dynamic`) names the member by the *value* of `$p` — a dynamic access
/// — so it bails the rule instead of recording `p`.
fn record_member(
    m: &MemberName,
    set: &mut HashSet<String>,
    interner: &Interner,
    dynamic: &mut bool,
    var_is_dynamic: bool,
) {
    match m {
        MemberName::Var(_) if var_is_dynamic => *dynamic = true,
        MemberName::Ident(s) | MemberName::Var(s) => {
            set.insert(interner.resolve(*s).to_string());
        }
        MemberName::Expr(_) => *dynamic = true,
    }
}

/// The display name phpstan uses for a class in dead-code messages.
fn class_display(c: &ClassDecl, scope: &php_resolve::Scope, interner: &Interner) -> String {
    c.name.map(|n| scope.qualify(interner.resolve(n))).unwrap_or_default()
}

/// Visit each top-level class/enum declaration with its region scope. Unused
/// private member rules apply only to `class`/`enum` (phpstan excludes traits,
/// whose members may be used by the using class, and interfaces have no privates).
fn for_each_concrete_class(fa: &FileAnalysis, mut f: impl FnMut(&php_resolve::Scope, &ClassDecl)) {
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            collect_classes(st, scope, &mut f);
        }
    });
}

fn collect_classes(st: &Stmt, scope: &php_resolve::Scope, f: &mut impl FnMut(&php_resolve::Scope, &ClassDecl)) {
    match &st.kind {
        StmtKind::Class(c) if matches!(c.kind, ClassKind::Class | ClassKind::Enum) => f(scope, c),
        StmtKind::Namespace { body: Some(b), .. } => b.iter().for_each(|s| collect_classes(s, scope, f)),
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// UnusedPrivateMethodRule — `method.unused`
// ---------------------------------------------------------------------------

/// A `private` method never referenced anywhere in its class.
///
/// Mirrors phpstan's `UnusedPrivateMethodRule`. Skips the constructor and
/// `__clone` (phpstan's exclusions), all magic methods (the engine may call
/// them), and bails entirely if the class does any dynamic method dispatch.
fn run_unused_private_method(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_concrete_class(fa, |scope, c| {
        let refs = collect_member_refs(c, fa.interner);
        if refs.has_dynamic_member {
            return; // can't prove anything unused
        }
        let used: HashSet<String> = refs.method_names.iter().map(|s| s.to_ascii_lowercase()).collect();
        let display = class_display(c, scope, fa.interner);
        for m in &c.members {
            let Member::Method(md) = m else { continue };
            if md.modifiers.visibility != Some(Visibility::Private) {
                continue;
            }
            let name = fa.interner.resolve(md.name).to_string();
            let lower = name.to_ascii_lowercase();
            // Excluded: constructor, __clone, and any magic method (the engine
            // may call them implicitly, so they're never "unused").
            if is_magic_method(&lower) {
                continue;
            }
            if used.contains(&lower) || refs.string_literals.contains(&name) {
                continue;
            }
            let kind = if md.modifiers.is_static { "Static method" } else { "Method" };
            out.push(
                Diagnostic::error(
                    method_span(md),
                    format!("{kind} {display}::{name}() is unused."),
                )
                .with_code("method.unused"),
            );
        }
    });
    out
}

/// A magic method (lowercased) — these are invoked implicitly by the engine, so
/// they never count as "unused". Includes `__construct`/`__destruct`.
fn is_magic_method(lower: &str) -> bool {
    matches!(
        lower,
        "__construct"
            | "__destruct"
            | "__call"
            | "__callstatic"
            | "__get"
            | "__set"
            | "__isset"
            | "__unset"
            | "__sleep"
            | "__wakeup"
            | "__serialize"
            | "__unserialize"
            | "__tostring"
            | "__invoke"
            | "__set_state"
            | "__clone"
            | "__debuginfo"
    )
}

/// Best-effort span for a method (its body's first statement, else a zero span;
/// `MethodDecl` carries no span of its own).
fn method_span(md: &MethodDecl) -> php_span::Span {
    md.body.as_ref().and_then(|b| b.first()).map(|s| s.span).unwrap_or(php_span::Span::new(0, 0))
}

// ---------------------------------------------------------------------------
// UnusedPrivateConstantRule — `classConstant.unused`
// ---------------------------------------------------------------------------

/// A `private` class constant never fetched within its class.
///
/// Mirrors phpstan's `UnusedPrivateConstantRule`. Bails if the class performs a
/// dynamic class-constant fetch (`::{$x}`).
fn run_unused_private_constant(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_concrete_class(fa, |scope, c| {
        let refs = collect_member_refs(c, fa.interner);
        if refs.has_dynamic_member {
            return;
        }
        let display = class_display(c, scope, fa.interner);
        for m in &c.members {
            let Member::ClassConst(cd) = m else { continue };
            if cd.modifiers.visibility != Some(Visibility::Private) {
                continue;
            }
            for ce in &cd.consts {
                let name = fa.interner.resolve(ce.name).to_string();
                if refs.const_names.contains(&name) || refs.string_literals.contains(&name) {
                    continue;
                }
                out.push(
                    Diagnostic::error(
                        ce.value.span,
                        format!("Constant {display}::{name} is unused."),
                    )
                    .with_code("classConstant.unused"),
                );
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// UnusedPrivatePropertyRule — `property.unused`
// ---------------------------------------------------------------------------

/// A `private` property never accessed within its class.
///
/// Mirrors the fully-unused subset of phpstan's `UnusedPrivatePropertyRule`
/// (`property.unused`). The read/write-asymmetry identifiers need read-vs-write
/// flow tracking and are deferred. Bails on any dynamic property access.
fn run_unused_private_property(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_concrete_class(fa, |scope, c| {
        // Only plain classes (phpstan restricts this rule to `Class_`).
        if c.kind != ClassKind::Class {
            return;
        }
        let refs = collect_member_refs(c, fa.interner);
        if refs.has_dynamic_member {
            return;
        }
        let display = class_display(c, scope, fa.interner);
        for m in &c.members {
            let Member::Property(pd) = m else { continue };
            if pd.modifiers.visibility != Some(Visibility::Private) {
                continue;
            }
            for pe in &pd.props {
                let name = fa.interner.resolve(pe.name).to_string();
                if refs.prop_names.contains(&name) || refs.string_literals.contains(&name) {
                    continue;
                }
                let kind = if pd.modifiers.is_static { "Static property" } else { "Property" };
                let span = pe.default.as_ref().map(|d| d.span).unwrap_or(php_span::Span::new(0, 0));
                out.push(
                    Diagnostic::error(span, format!("{kind} {display}::${name} is unused."))
                        .with_code("property.unused"),
                );
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// NoopRule — `<op>.resultUnused` (the always-pure operator forms)
// ---------------------------------------------------------------------------

/// A statement-level expression whose result is discarded, for operator forms
/// that are always pure (logical `and`/`or`/`xor`, ternary).
///
/// Mirrors the side-effect-free subset of phpstan's `NoopRule`. The bare
/// `expr.resultUnused` and `booleanAnd/Or` cases need "has side effect" /
/// "hasAssign" analysis and are deferred.
fn run_noop(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        let StmtKind::Expr(e) = &s.kind else { return };
        match &e.kind {
            ExprKind::Binary { op: BinOp::LogicalXor, .. } => out.push(
                Diagnostic::error(e.span, "Unused result of \"xor\" operator.")
                    .with_code("logicalXor.resultUnused"),
            ),
            ExprKind::Binary { op: BinOp::LogicalAnd, .. } => out.push(
                Diagnostic::error(e.span, "Unused result of \"and\" operator.")
                    .with_code("logicalAnd.resultUnused"),
            ),
            ExprKind::Binary { op: BinOp::LogicalOr, .. } => out.push(
                Diagnostic::error(e.span, "Unused result of \"or\" operator.")
                    .with_code("logicalOr.resultUnused"),
            ),
            ExprKind::Ternary { .. } if !contains_assign(e) => out.push(
                Diagnostic::error(e.span, "Unused result of ternary operator.")
                    .with_code("ternary.resultUnused"),
            ),
            // `&&` / `||` whose result is discarded and which has no side effect
            // (the short-circuit idiom `$x && f()` has an effect → not flagged).
            ExprKind::Binary { op: BinOp::BoolAnd, .. } if !has_side_effect(e) => out.push(
                Diagnostic::error(e.span, "Unused result of \"&&\" operator.")
                    .with_code("booleanAnd.resultUnused"),
            ),
            ExprKind::Binary { op: BinOp::BoolOr, .. } if !has_side_effect(e) => out.push(
                Diagnostic::error(e.span, "Unused result of \"||\" operator.")
                    .with_code("booleanOr.resultUnused"),
            ),
            // Any other pure value expression on its own line does nothing.
            _ if is_pure_value_noop(e) => out.push(
                Diagnostic::error(e.span, "Expression on a separate line does not do anything.")
                    .with_code("expr.resultUnused"),
            ),
            _ => {}
        }
    });
    out
}

/// Whether a statement-level expression is a "pure value" with no effect — a
/// candidate for `expr.resultUnused`. We *only* report a small, clearly-safe set
/// of expression heads (variables, literals, names/const fetches, comparisons /
/// arithmetic, property/array reads, coalesce, instanceof, isset/empty, casts),
/// and only when nothing in the subtree has a side effect. This conservatism
/// mirrors phpstan excluding calls / `new` / assignments / closures from the
/// generic `expr.resultUnused` branch.
fn is_pure_value_noop(e: &Expr) -> bool {
    let head_ok = matches!(
        &e.kind,
        ExprKind::Variable(_)
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Str(_)
            | ExprKind::Name(_)
            | ExprKind::Binary { .. }
            | ExprKind::Unary { .. }
            | ExprKind::Index { .. }
            | ExprKind::Prop { .. }
            | ExprKind::StaticProp { .. }
            | ExprKind::ClassConst { .. }
            | ExprKind::Coalesce { .. }
            | ExprKind::Instanceof { .. }
            | ExprKind::Isset(_)
            | ExprKind::Empty(_)
            | ExprKind::Cast { .. }
            | ExprKind::Array { .. }
            | ExprKind::Paren(_)
    );
    head_ok && !has_side_effect(e)
}

/// Whether any node in the subtree of `e` is potentially side-effecting (so the
/// statement isn't a pure no-op). Conservative: a call, instantiation,
/// assignment, increment/decrement, `yield`, `throw`, `exit`, `print`, `clone`,
/// `include`, `eval`, `match`, error-suppression, or shell-exec all count.
fn has_side_effect(e: &Expr) -> bool {
    let mut found = false;
    walk::for_each_expr(
        &php_ast::Program { stmts: vec![Stmt::new(php_span::Span::new(0, 0), StmtKind::Expr(e.clone()))] },
        &mut |x| {
            if matches!(
                x.kind,
                ExprKind::Call { .. }
                    | ExprKind::MethodCall { .. }
                    | ExprKind::StaticCall { .. }
                    | ExprKind::New { .. }
                    | ExprKind::NewAnon { .. }
                    | ExprKind::Assign { .. }
                    | ExprKind::AssignOp { .. }
                    | ExprKind::AssignRef { .. }
                    | ExprKind::PreInc(_)
                    | ExprKind::PreDec(_)
                    | ExprKind::PostInc(_)
                    | ExprKind::PostDec(_)
                    | ExprKind::Yield { .. }
                    | ExprKind::YieldFrom(_)
                    | ExprKind::Throw(_)
                    | ExprKind::Exit(_)
                    | ExprKind::Print(_)
                    | ExprKind::Clone(_)
                    | ExprKind::Include { .. }
                    | ExprKind::Eval(_)
                    | ExprKind::Match { .. }
                    | ExprKind::ErrorSuppress(_)
                    | ExprKind::ShellExec(_)
            ) {
                found = true;
            }
        },
    );
    found
}

/// Whether an expression subtree contains any assignment (mirrors phpstan's
/// `hasAssign()` guard — an assignment is a side effect, so the statement isn't a
/// no-op).
fn contains_assign(e: &Expr) -> bool {
    let mut found = false;
    walk::for_each_expr(&php_ast::Program { stmts: vec![Stmt::new(php_span::Span::new(0, 0), StmtKind::Expr(e.clone()))] }, &mut |x| {
        if matches!(
            x.kind,
            ExprKind::Assign { .. } | ExprKind::AssignOp { .. } | ExprKind::AssignRef { .. }
        ) {
            found = true;
        }
    });
    found
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "deadCode.unreachable", level: 4, run: run_unreachable },
    RuleEntry { name: "method.unused", level: 4, run: run_unused_private_method },
    RuleEntry { name: "classConstant.unused", level: 4, run: run_unused_private_constant },
    RuleEntry { name: "property.unused", level: 4, run: run_unused_private_property },
    RuleEntry { name: "noop", level: 4, run: run_noop },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- unreachable -----------------------------------------------------

    #[test]
    fn statement_after_return_is_unreachable() {
        let src = "<?php function f() { return 1; echo 2; }";
        assert_eq!(codes(src, run_unreachable), ["deadCode.unreachable"]);
    }

    #[test]
    fn statement_after_throw_is_unreachable() {
        let src = "<?php function f() { throw new Exception(); echo 2; }";
        assert_eq!(codes(src, run_unreachable), ["deadCode.unreachable"]);
    }

    #[test]
    fn statement_after_break_is_unreachable() {
        let src = "<?php foreach ([] as $x) { break; echo 1; }";
        assert_eq!(codes(src, run_unreachable), ["deadCode.unreachable"]);
    }

    #[test]
    fn only_first_unreachable_is_reported_per_block() {
        let src = "<?php function f() { return 1; echo 2; echo 3; }";
        assert_eq!(codes(src, run_unreachable), ["deadCode.unreachable"]);
    }

    #[test]
    fn return_at_end_of_block_is_clean() {
        let src = "<?php function f() { echo 1; return 2; }";
        assert!(codes(src, run_unreachable).is_empty());
    }

    #[test]
    fn function_declaration_after_return_is_clean() {
        // Declarations are hoisted; not unreachable.
        let src = "<?php function f() { return 1; function g() {} }";
        assert!(codes(src, run_unreachable).is_empty());
    }

    #[test]
    fn unreachable_in_nested_block_is_found() {
        let src = "<?php function f() { if (true) { return 1; echo 2; } }";
        assert_eq!(codes(src, run_unreachable), ["deadCode.unreachable"]);
    }

    // --- unused private method ------------------------------------------

    #[test]
    fn unused_private_method_is_flagged() {
        let src = "<?php class C { private function helper() {} }";
        assert_eq!(codes(src, run_unused_private_method), ["method.unused"]);
    }

    #[test]
    fn used_private_method_is_clean() {
        let src = "<?php class C { private function helper() {} function run() { $this->helper(); } }";
        assert!(codes(src, run_unused_private_method).is_empty());
    }

    #[test]
    fn used_via_self_static_call_is_clean() {
        let src = "<?php class C { private static function helper() {} function run() { self::helper(); } }";
        assert!(codes(src, run_unused_private_method).is_empty());
    }

    #[test]
    fn public_method_is_not_flagged() {
        let src = "<?php class C { public function helper() {} }";
        assert!(codes(src, run_unused_private_method).is_empty());
    }

    #[test]
    fn private_constructor_is_not_flagged() {
        let src = "<?php class C { private function __construct() {} }";
        assert!(codes(src, run_unused_private_method).is_empty());
    }

    #[test]
    fn dynamic_method_call_disables_rule() {
        // A computed method name means we can't prove `helper` unused.
        let src = "<?php class C { private function helper() {} function run($m) { $this->$m(); } }";
        assert!(codes(src, run_unused_private_method).is_empty());
    }

    #[test]
    fn method_referenced_as_string_is_clean() {
        // e.g. a callable array `[$this, 'helper']`.
        let src = "<?php class C { private function helper() {} function run() { $f = [$this, 'helper']; } }";
        assert!(codes(src, run_unused_private_method).is_empty());
    }

    // --- unused private constant ----------------------------------------

    #[test]
    fn unused_private_constant_is_flagged() {
        let src = "<?php class C { private const FOO = 1; }";
        assert_eq!(codes(src, run_unused_private_constant), ["classConstant.unused"]);
    }

    #[test]
    fn used_private_constant_is_clean() {
        let src = "<?php class C { private const FOO = 1; function f() { return self::FOO; } }";
        assert!(codes(src, run_unused_private_constant).is_empty());
    }

    #[test]
    fn public_constant_is_not_flagged() {
        let src = "<?php class C { const FOO = 1; }";
        assert!(codes(src, run_unused_private_constant).is_empty());
    }

    // --- unused private property ----------------------------------------

    #[test]
    fn unused_private_property_is_flagged() {
        let src = "<?php class C { private $data = 1; }";
        assert_eq!(codes(src, run_unused_private_property), ["property.unused"]);
    }

    #[test]
    fn used_private_property_is_clean() {
        let src = "<?php class C { private $data = 1; function f() { return $this->data; } }";
        assert!(codes(src, run_unused_private_property).is_empty());
    }

    #[test]
    fn public_property_is_not_flagged() {
        let src = "<?php class C { public $data = 1; }";
        assert!(codes(src, run_unused_private_property).is_empty());
    }

    #[test]
    fn dynamic_property_access_disables_rule() {
        let src = "<?php class C { private $data = 1; function f($k) { return $this->$k; } }";
        assert!(codes(src, run_unused_private_property).is_empty());
    }

    // --- noop ------------------------------------------------------------

    #[test]
    fn logical_and_statement_is_flagged() {
        let src = "<?php $a and $b;";
        assert_eq!(codes(src, run_noop), ["logicalAnd.resultUnused"]);
    }

    #[test]
    fn ternary_statement_is_flagged() {
        let src = "<?php $a ? $b : $c;";
        assert_eq!(codes(src, run_noop), ["ternary.resultUnused"]);
    }

    #[test]
    fn assignment_statement_is_clean() {
        let src = "<?php $a = $b;";
        assert!(codes(src, run_noop).is_empty());
    }

    // --- noop: expr.resultUnused / booleanAnd / booleanOr ---

    #[test]
    fn bare_variable_statement_is_flagged() {
        assert_eq!(codes("<?php $a;", run_noop), ["expr.resultUnused"]);
    }

    #[test]
    fn bare_comparison_statement_is_flagged() {
        assert_eq!(codes("<?php $a > $b;", run_noop), ["expr.resultUnused"]);
    }

    #[test]
    fn bare_property_fetch_statement_is_flagged() {
        let src = "<?php class C { function f() { $this->x; } }";
        assert_eq!(codes(src, run_noop), ["expr.resultUnused"]);
    }

    #[test]
    fn function_call_statement_is_clean() {
        // A call has effects; not flagged by this rule.
        assert!(codes("<?php foo();", run_noop).is_empty());
    }

    #[test]
    fn comparison_with_call_is_clean() {
        // The call subexpression has an effect → not a pure no-op.
        assert!(codes("<?php foo() > 1;", run_noop).is_empty());
    }

    #[test]
    fn boolean_and_pure_statement_is_flagged() {
        assert_eq!(codes("<?php $a && $b;", run_noop), ["booleanAnd.resultUnused"]);
    }

    #[test]
    fn boolean_and_short_circuit_idiom_is_clean() {
        // `$cond && doThing()` — the right side has an effect; not a no-op.
        assert!(codes("<?php $cond && foo();", run_noop).is_empty());
    }

    #[test]
    fn boolean_or_short_circuit_idiom_is_clean() {
        assert!(codes("<?php $cond || foo();", run_noop).is_empty());
    }

    #[test]
    fn new_statement_is_clean() {
        // `new` may have constructor side effects; not flagged here.
        assert!(codes("<?php new Foo();", run_noop).is_empty());
    }
}
