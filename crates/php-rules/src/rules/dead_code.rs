//! phpstan category **DeadCode** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/DeadCode/` — 9 rule(s) at level(s) 4.
//! The rule set's coverage truth is `cargo run -p xtask -- rule-manifest`; for phpstan's behaviour read `phpstan-src/src/Rules/` directly. Add each rule as a `RuleEntry` to
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
//! - **CallToFunctionStatementWithoutImpurePointsRule**
//!   (`function.resultUnused`) — conservative same-file subset: a discarded call
//!   to a user function explicitly marked pure, with no by-ref params/asserts/
//!   throws and whose body has no side effects except calls/new whose targets are
//!   in the same proven-pure closure.
//! - **CallToConstructorStatementWithoutImpurePointsRule**
//!   (`new.resultUnused`) — same subset for discarded `new C()` where
//!   `C::__construct()` is proven effect-free.
//! - **CallToMethodStatementWithoutImpurePointsRule** /
//!   **CallToStaticMethodStatementWithoutImpurePointsRule**
//!   (`method.resultUnused`/`staticMethod.resultUnused`) — conservative same-file
//!   subset for non-`@pure` methods whose bodies have no impure points; direct
//!   `@pure` calls stay owned by `methods.rs` to avoid duplicate diagnostics.
//!
//! Deferred:
//! - Broader virtual-dispatch, argument, nullsafe, pipe-callable, inherited, and
//!   cross-file purity cases for the `CallTo*StatementWithoutImpurePointsRule`
//!   family.

use crate::members;
use crate::{symbols, walk, FileAnalysis, RuleEntry};
use php_ast::{
    BinOp, ClassDecl, ClassKind, Expr, ExprKind, FunctionDecl, Member, MemberName, MethodDecl,
    Stmt, StmtKind, Visibility,
};
use php_diagnostics::Diagnostic;
use php_intern::Interner;
use php_reflect::{Found, MethodReflection};
use php_resolve::{for_each_region, Resolution, Scope};
use php_types::Type;
use std::collections::{HashMap, HashSet};

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
                Diagnostic::error(
                    s.span,
                    "Unreachable statement - code above always terminates.",
                )
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
        StmtKind::Return(_) | StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Goto(_) => {
            true
        }
        StmtKind::Expr(e) => matches!(e.kind, ExprKind::Throw(_) | ExprKind::Exit(_)),
        _ => false,
    }
}

/// Recurse the reachability check into nested statement lists of `s` so each
/// block (then/else, loop body, case body, try/catch/finally, …) is checked.
fn recurse_into_blocks(s: &Stmt, out: &mut Vec<Diagnostic>) {
    match &s.kind {
        StmtKind::Block(b) => check_stmt_list(b, out),
        StmtKind::If {
            then, elseifs, els, ..
        } => {
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
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
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
        stmts: vec![Stmt::new(
            php_span::Span::new(0, 0),
            StmtKind::Class(c.clone()),
        )],
    };
    record_refs_in_program(&prog, interner, &mut refs);
    refs
}

/// Record every member-name reference in `prog` into `refs` (additive). Shared by
/// the class-body scan and the used-trait method-body scan so a private member a
/// trait method touches is correctly seen as used.
fn record_refs_in_program(prog: &php_ast::Program, interner: &Interner, refs: &mut MemberRefs) {
    walk::for_each_expr(prog, &mut |e| match &e.kind {
        ExprKind::MethodCall { method, .. } => record_member(
            method,
            &mut refs.method_names,
            interner,
            &mut refs.has_dynamic_member,
            true,
        ),
        ExprKind::StaticCall { method, .. } => record_member(
            method,
            &mut refs.method_names,
            interner,
            &mut refs.has_dynamic_member,
            false,
        ),
        ExprKind::Prop { name, .. } => record_member(
            name,
            &mut refs.prop_names,
            interner,
            &mut refs.has_dynamic_member,
            true,
        ),
        ExprKind::StaticProp { name, .. } => record_member(
            name,
            &mut refs.prop_names,
            interner,
            &mut refs.has_dynamic_member,
            false,
        ),
        ExprKind::ClassConst { name, .. } => record_member(
            name,
            &mut refs.const_names,
            interner,
            &mut refs.has_dynamic_member,
            false,
        ),
        ExprKind::Str(bytes) => {
            if let Ok(s) = std::str::from_utf8(bytes) {
                refs.string_literals.insert(s.to_string());
            }
        }
        _ => {}
    });
}

/// Member references from a concrete class *plus* the method bodies of every
/// trait it (transitively) uses. A trait method is compiled into the using class
/// and can reference its private members (`$this->prop`, `self::method()`), so a
/// class-body-only scan wrongly reports those members unused. Trait bodies live
/// in the reflection index (often cross-file); this only ever *adds* to the used
/// sets, so it can shrink but never grow the reported-unused set.
fn collect_member_refs_incl_traits(fa: &FileAnalysis, scope: &Scope, c: &ClassDecl) -> MemberRefs {
    let mut refs = collect_member_refs(c, fa.interner);
    let Some(class_fqn) = c.name.map(|n| scope.qualify(fa.interner.resolve(n))) else {
        return refs;
    };
    let Some(cref) = fa.reflection.class(&class_fqn) else {
        return refs;
    };
    let mut seen: HashSet<String> = HashSet::new();
    let mut stack: Vec<String> = trait_fqns(&cref.traits);
    while let Some(tfqn) = stack.pop() {
        if !seen.insert(tfqn.to_ascii_lowercase()) {
            continue;
        }
        let Some(tref) = fa.reflection.class(&tfqn) else {
            continue;
        };
        // A trait can itself `use` further traits — follow them transitively.
        stack.extend(trait_fqns(&tref.traits));
        for md in &tref.methods {
            if let Some((body, _)) = fa.reflection.method_body(&tfqn, &md.name) {
                let prog = php_ast::Program {
                    stmts: body.to_vec(),
                };
                record_refs_in_program(&prog, fa.interner, &mut refs);
            }
        }
    }
    refs
}

/// The fully-qualified names of the trait types on a class reflection.
fn trait_fqns(traits: &[Type]) -> Vec<String> {
    traits
        .iter()
        .filter_map(|t| match t {
            Type::Named { fqn, .. } => Some(fqn.to_string()),
            _ => None,
        })
        .collect()
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
/// The class's name **for a message**: display-stripped FQN, or the words
/// `Anonymous class`. Distinct from `constants::declared_class_fqn` and
/// `classes::qualified_class_name`, which render differently on purpose.
fn class_display_name(c: &ClassDecl, scope: &php_resolve::Scope, interner: &Interner) -> String {
    c.name
        .map(|n| scope.qualify(interner.resolve(n)))
        .unwrap_or_default()
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

fn collect_classes(
    st: &Stmt,
    scope: &php_resolve::Scope,
    f: &mut impl FnMut(&php_resolve::Scope, &ClassDecl),
) {
    match &st.kind {
        StmtKind::Class(c) if matches!(c.kind, ClassKind::Class | ClassKind::Enum) => f(scope, c),
        StmtKind::Namespace { body: Some(b), .. } => {
            b.iter().for_each(|s| collect_classes(s, scope, f))
        }
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
        let refs = collect_member_refs_incl_traits(fa, scope, c);
        if refs.has_dynamic_member {
            return; // can't prove anything unused
        }
        let used: HashSet<String> = refs
            .method_names
            .iter()
            .map(|s| s.to_ascii_lowercase())
            .collect();
        let display = class_display_name(c, scope, fa.interner);
        for m in &c.members {
            let Member::Method(md) = m else { continue };
            if md.modifiers.visibility != Some(Visibility::Private) {
                continue;
            }
            let name = fa.interner.resolve(md.name).to_string();
            let lower = name.to_ascii_lowercase();
            // Excluded: constructor, __clone, and any magic method (the engine
            // may call them implicitly, so they're never "unused").
            if members::is_magic_method(&lower) {
                continue;
            }
            if used.contains(&lower) || refs.string_literals.contains(&name) {
                continue;
            }
            let kind = if md.modifiers.is_static {
                "Static method"
            } else {
                "Method"
            };
            out.push(
                Diagnostic::error(
                    md.name_span,
                    format!("{kind} {display}::{name}() is unused."),
                )
                .with_code("method.unused"),
            );
        }
    });
    out
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
        let refs = collect_member_refs_incl_traits(fa, scope, c);
        if refs.has_dynamic_member {
            return;
        }
        let display = class_display_name(c, scope, fa.interner);
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
        let refs = collect_member_refs_incl_traits(fa, scope, c);
        if refs.has_dynamic_member {
            return;
        }
        let display = class_display_name(c, scope, fa.interner);
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
                let kind = if pd.modifiers.is_static {
                    "Static property"
                } else {
                    "Property"
                };
                out.push(
                    Diagnostic::error(
                        pe.name_span,
                        format!("{kind} {display}::${name} is unused."),
                    )
                    .with_code("property.unused"),
                );
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// CallToFunctionStatementWithoutImpurePointsRule — `function.resultUnused`
// CallToConstructorStatementWithoutImpurePointsRule — `new.resultUnused`
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum CallableKey {
    Function(String),
    Method { class: String, method: String },
}

#[derive(Clone, Debug)]
struct PureCandidate {
    deps: HashSet<CallableKey>,
    method: Option<PureMethodCandidate>,
}

#[derive(Clone, Debug)]
struct PureMethodCandidate {
    display: String,
    declared_pure: bool,
}

/// Same-file, zero-FP subset of phpstan's transitive
/// `CallTo*StatementWithoutImpurePointsRule` family.
///
/// PHPStan collects declarations whose "impure points" are only calls, then
/// solves the transitive closure. We mirror that shape locally for user
/// functions and constructors:
/// - the declaration must be explicitly `@pure`/`@phpstan-pure`/`@psalm-pure`
///   in reflection,
/// - no by-ref params / assert tags / throw tags,
/// - the body may contain no side-effecting expression except calls/new we can
///   resolve into this same candidate set.
///
/// This is intentionally narrower than phpstan, but every diagnostic it emits is
/// a case phpstan also reports.
fn run_pure_function_statement_without_impure_points(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let candidates = collect_pure_candidates(fa);
    let pure = pure_callable_closure(&candidates);
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            crate::rules::functions::stmt_level_calls(st, &mut |e| {
                let ExprKind::Call { callee, args } = &e.kind else {
                    return;
                };
                if args.iter().any(|a| a.placeholder) {
                    return;
                }
                let Some(key) = function_call_key(scope, callee) else {
                    return;
                };
                if !pure.contains(&key) {
                    return;
                }
                let CallableKey::Function(fqn) = key else {
                    return;
                };
                let display = fqn.trim_start_matches('\\');
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!("Call to function {display}() on a separate line has no effect."),
                    )
                    .with_code("function.resultUnused"),
                );
            });
        }
    });
    out
}

fn run_pure_constructor_statement_without_impure_points(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let candidates = collect_pure_candidates(fa);
    let pure = pure_callable_closure(&candidates);
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            crate::rules::functions::stmt_level_calls(st, &mut |e| {
                let ExprKind::New { class, .. } = &e.kind else {
                    return;
                };
                let Some(class_fqn) = class_expr_fqn(scope, class) else {
                    return;
                };
                let key = method_callable_key(&class_fqn, "__construct");
                if !pure.contains(&key) {
                    return;
                }
                let display = fa
                    .reflection
                    .class(&class_fqn)
                    .map(|c| c.fqn.trim_start_matches('\\'))
                    .unwrap_or_else(|| class_fqn.trim_start_matches('\\'));
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!("Call to new {display}() on a separate line has no effect."),
                    )
                    .with_code("new.resultUnused"),
                );
            });
        }
    });
    out
}

fn run_pure_method_statement_without_impure_points(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let candidates = collect_pure_candidates(fa);
    let pure = pure_callable_closure(&candidates);
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |_scope, region| {
        for st in region {
            crate::rules::functions::stmt_level_calls(st, &mut |e| {
                let ExprKind::MethodCall {
                    recv,
                    nullsafe,
                    method,
                    args,
                } = &e.kind
                else {
                    return;
                };
                if *nullsafe || !args.is_empty() {
                    return;
                }
                let Some(key) = exact_method_call_key(fa, recv, method) else {
                    return;
                };
                if !pure.contains(&key) {
                    return;
                }
                let Some(info) = candidates.get(&key).and_then(|c| c.method.as_ref()) else {
                    return;
                };
                if info.declared_pure {
                    return;
                }
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!(
                            "Call to method {}() on a separate line has no effect.",
                            info.display
                        ),
                    )
                    .with_code("method.resultUnused"),
                );
            });
        }
    });
    out
}

fn run_pure_static_method_statement_without_impure_points(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let candidates = collect_pure_candidates(fa);
    let pure = pure_callable_closure(&candidates);
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            crate::rules::functions::stmt_level_calls(st, &mut |e| {
                let ExprKind::StaticCall {
                    class,
                    method,
                    args,
                } = &e.kind
                else {
                    return;
                };
                if !args.is_empty() {
                    return;
                }
                let Some(key) = exact_static_method_call_key(fa, scope, class, method) else {
                    return;
                };
                if !pure.contains(&key) {
                    return;
                }
                let Some(info) = candidates.get(&key).and_then(|c| c.method.as_ref()) else {
                    return;
                };
                if info.declared_pure {
                    return;
                }
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!(
                            "Call to {}() on a separate line has no effect.",
                            info.display
                        ),
                    )
                    .with_code("staticMethod.resultUnused"),
                );
            });
        }
    });
    out
}

fn pure_callable_closure(candidates: &HashMap<CallableKey, PureCandidate>) -> HashSet<CallableKey> {
    let mut pure = HashSet::new();
    loop {
        let before = pure.len();
        for (key, cand) in candidates {
            if pure.contains(key) {
                continue;
            }
            if cand.deps.iter().all(|dep| pure.contains(dep)) {
                pure.insert(key.clone());
            }
        }
        if pure.len() == before {
            break;
        }
    }
    pure
}

fn collect_pure_candidates(fa: &FileAnalysis) -> HashMap<CallableKey, PureCandidate> {
    let mut out = HashMap::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            collect_pure_candidates_stmt(fa, scope, st, &mut out);
        }
    });
    out
}

fn collect_pure_candidates_stmt(
    fa: &FileAnalysis,
    scope: &Scope,
    st: &Stmt,
    out: &mut HashMap<CallableKey, PureCandidate>,
) {
    match &st.kind {
        StmtKind::Function(f) => {
            collect_function_candidate(fa, scope, f, out);
            for s in &f.body {
                collect_pure_candidates_stmt(fa, scope, s, out);
            }
        }
        StmtKind::Class(c) => collect_class_candidates(fa, scope, c, out),
        StmtKind::Block(b) | StmtKind::Namespace { body: Some(b), .. } => {
            for s in b {
                collect_pure_candidates_stmt(fa, scope, s, out);
            }
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            collect_pure_candidates_stmt(fa, scope, then, out);
            for e in elseifs {
                collect_pure_candidates_stmt(fa, scope, &e.body, out);
            }
            if let Some(e) = els {
                collect_pure_candidates_stmt(fa, scope, e, out);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => collect_pure_candidates_stmt(fa, scope, body, out),
        StmtKind::Switch { cases, .. } => {
            for case in cases {
                for s in &case.body {
                    collect_pure_candidates_stmt(fa, scope, s, out);
                }
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for s in body {
                collect_pure_candidates_stmt(fa, scope, s, out);
            }
            for c in catches {
                for s in &c.body {
                    collect_pure_candidates_stmt(fa, scope, s, out);
                }
            }
            if let Some(fin) = finally {
                for s in fin {
                    collect_pure_candidates_stmt(fa, scope, s, out);
                }
            }
        }
        _ => {}
    }
}

fn collect_function_candidate(
    fa: &FileAnalysis,
    scope: &Scope,
    f: &FunctionDecl,
    out: &mut HashMap<CallableKey, PureCandidate>,
) {
    let refl = fa.reflect_function(scope, f);
    if !refl.pure || callable_signature_disqualifies(&refl.params, f.doc.as_deref()) {
        return;
    }
    let Some(deps) = body_dependencies(fa, scope, &f.body, DependencyMode::FunctionConstructorOnly)
    else {
        return;
    };
    out.insert(
        CallableKey::Function(refl.fqn.clone()),
        PureCandidate { deps, method: None },
    );
}

fn collect_class_candidates(
    fa: &FileAnalysis,
    scope: &Scope,
    c: &ClassDecl,
    out: &mut HashMap<CallableKey, PureCandidate>,
) {
    let Some(name) = c.name else { return };
    let class_fqn = scope.qualify(fa.interner.resolve(name));
    let class = fa.reflect_class(scope, &class_fqn, c);
    for m in &c.members {
        let Member::Method(md) = m else { continue };
        if !matches!(c.kind, ClassKind::Class | ClassKind::Enum) {
            continue;
        }
        if !fa
            .interner
            .resolve(md.name)
            .eq_ignore_ascii_case("__construct")
        {
            collect_method_candidate(fa, scope, &class, md, out);
            continue;
        }
        let Some(refl) = class
            .methods
            .iter()
            .find(|r| r.name.eq_ignore_ascii_case("__construct") && !r.magic)
        else {
            continue;
        };
        if !refl.pure || callable_signature_disqualifies(&refl.params, md.doc.as_deref()) {
            continue;
        }
        let Some(body) = &md.body else { continue };
        let Some(deps) =
            body_dependencies(fa, scope, body, DependencyMode::FunctionConstructorOnly)
        else {
            continue;
        };
        out.insert(
            method_callable_key(&class.fqn, "__construct"),
            PureCandidate { deps, method: None },
        );
    }
}

fn collect_method_candidate(
    fa: &FileAnalysis,
    scope: &Scope,
    class: &php_reflect::ClassReflection,
    md: &MethodDecl,
    out: &mut HashMap<CallableKey, PureCandidate>,
) {
    let Some(body) = &md.body else { return };
    if md.by_ref || doc_is_explicit_impure(md.doc.as_deref()) {
        return;
    }
    let method_name = fa.interner.resolve(md.name);
    let Some(refl) = class
        .methods
        .iter()
        .find(|r| r.name.eq_ignore_ascii_case(method_name) && !r.magic)
    else {
        return;
    };
    if refl.name.eq_ignore_ascii_case("__construct")
        || matches!(refl.return_type, Type::Never)
        || callable_signature_disqualifies(&refl.params, md.doc.as_deref())
    {
        return;
    }
    let Some(deps) = body_dependencies(fa, scope, body, DependencyMode::IncludeMethods) else {
        return;
    };
    out.insert(
        method_callable_key(&class.fqn, &refl.name),
        PureCandidate {
            deps,
            method: Some(PureMethodCandidate {
                display: format!("{}::{}", class.fqn.trim_start_matches('\\'), refl.name),
                declared_pure: refl.pure,
            }),
        },
    );
}

fn callable_signature_disqualifies(
    params: &[php_reflect::ParamReflection],
    doc: Option<&str>,
) -> bool {
    params.iter().any(|p| p.by_ref) || doc_has_throw_or_assert(doc)
}

fn doc_has_throw_or_assert(doc: Option<&str>) -> bool {
    php_phpdoc::query::has_base_tag(
        doc,
        &["throws", "assert", "assert-if-true", "assert-if-false"],
    )
}

fn doc_is_explicit_impure(doc: Option<&str>) -> bool {
    php_phpdoc::query::has_base_tag(doc, &["impure"])
}

#[derive(Clone, Copy)]
enum DependencyMode {
    FunctionConstructorOnly,
    IncludeMethods,
}

fn body_dependencies(
    fa: &FileAnalysis,
    scope: &Scope,
    body: &[Stmt],
    mode: DependencyMode,
) -> Option<HashSet<CallableKey>> {
    let mut deps = HashSet::new();
    for st in body {
        if statement_kind_is_impure(&st.kind) {
            return None;
        }
        let mut ok = true;
        walk::for_each_expr_in_scope(st, &mut |e| {
            if !ok {
                return;
            }
            match expression_effect(fa, scope, e, mode) {
                ExprEffect::Pure => {}
                ExprEffect::Dependency(dep) => {
                    deps.insert(dep);
                }
                ExprEffect::Impure => ok = false,
            }
        });
        if !ok {
            return None;
        }
    }
    Some(deps)
}

fn statement_kind_is_impure(kind: &StmtKind) -> bool {
    matches!(
        kind,
        StmtKind::Echo(_)
            | StmtKind::Global(_)
            | StmtKind::StaticVars(_)
            | StmtKind::Unset(_)
            | StmtKind::Goto(_)
            | StmtKind::HaltCompiler(_)
            | StmtKind::InlineHtml(_)
            | StmtKind::Error
    )
}

enum ExprEffect {
    Pure,
    Dependency(CallableKey),
    Impure,
}

fn expression_effect(
    fa: &FileAnalysis,
    scope: &Scope,
    e: &Expr,
    mode: DependencyMode,
) -> ExprEffect {
    match &e.kind {
        ExprKind::Call { callee, args } => {
            if args.iter().any(|a| a.placeholder) {
                return ExprEffect::Impure;
            }
            function_call_key(scope, callee).map_or(ExprEffect::Impure, ExprEffect::Dependency)
        }
        ExprKind::New { class, .. } => {
            let Some(class) = class_expr_fqn(scope, class) else {
                return ExprEffect::Impure;
            };
            ExprEffect::Dependency(method_callable_key(&class, "__construct"))
        }
        ExprKind::MethodCall {
            recv,
            nullsafe,
            method,
            args,
        } if matches!(mode, DependencyMode::IncludeMethods) => {
            if *nullsafe || !args.is_empty() {
                return ExprEffect::Impure;
            }
            exact_method_call_key(fa, recv, method)
                .map_or(ExprEffect::Impure, ExprEffect::Dependency)
        }
        ExprKind::StaticCall {
            class,
            method,
            args,
        } if matches!(mode, DependencyMode::IncludeMethods) => {
            if !args.is_empty() {
                return ExprEffect::Impure;
            }
            exact_static_method_call_key(fa, scope, class, method)
                .map_or(ExprEffect::Impure, ExprEffect::Dependency)
        }
        ExprKind::MethodCall { .. } | ExprKind::StaticCall { .. } => ExprEffect::Impure,
        ExprKind::Index { .. } | ExprKind::Prop { .. } | ExprKind::StaticProp { .. }
            if matches!(mode, DependencyMode::IncludeMethods) =>
        {
            ExprEffect::Impure
        }
        ExprKind::NewAnon { .. }
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
        | ExprKind::Closure(_)
        | ExprKind::ArrowFn(_)
        | ExprKind::VariableVariable(_)
        | ExprKind::DollarBrace(_)
        | ExprKind::Error => ExprEffect::Impure,
        _ => ExprEffect::Pure,
    }
}

fn exact_method_call_key(
    fa: &FileAnalysis,
    recv: &Expr,
    method: &MemberName,
) -> Option<CallableKey> {
    let recv = php_ast::queries::peel_paren(recv);
    if !matches!(recv.kind, ExprKind::Variable(_)) {
        return None;
    }
    let MemberName::Ident(name) = method else {
        return None;
    };
    let receiver_fqn = named_type_fqn(&fa.type_of(recv))?;
    if !fa.class_fully_known(&receiver_fqn) {
        return None;
    }
    let method_name = fa.interner.resolve(*name);
    let found = fa.reflection.find_method(&receiver_fqn, method_name)?;
    if found.member.magic || found.member.is_static {
        return None;
    }
    if !symbols::same_fqn(found.declaring_class, &receiver_fqn) {
        return None;
    }
    if !instance_dispatch_is_exact(fa, &receiver_fqn, &found) {
        return None;
    }
    Some(method_callable_key(
        found.declaring_class,
        &found.member.name,
    ))
}

fn exact_static_method_call_key(
    fa: &FileAnalysis,
    scope: &Scope,
    class: &Expr,
    method: &MemberName,
) -> Option<CallableKey> {
    let MemberName::Ident(name) = method else {
        return None;
    };
    let class_fqn = class_expr_fqn(scope, class)?;
    if !fa.class_fully_known(&class_fqn) {
        return None;
    }
    let method_name = fa.interner.resolve(*name);
    let found = fa.reflection.find_method(&class_fqn, method_name)?;
    if found.member.magic || !found.member.is_static {
        return None;
    }
    if !symbols::same_fqn(found.declaring_class, &class_fqn) {
        return None;
    }
    Some(method_callable_key(
        found.declaring_class,
        &found.member.name,
    ))
}

fn instance_dispatch_is_exact(
    fa: &FileAnalysis,
    receiver_fqn: &str,
    found: &Found<MethodReflection>,
) -> bool {
    if found.member.visibility == Visibility::Private || found.member.is_final {
        return true;
    }
    fa.reflection
        .class(receiver_fqn)
        .is_some_and(|class| class.is_final)
}

fn method_callable_key(class: &str, method: &str) -> CallableKey {
    CallableKey::Method {
        class: class.trim_start_matches('\\').to_ascii_lowercase(),
        method: method.to_ascii_lowercase(),
    }
}

fn named_type_fqn(t: &Type) -> Option<String> {
    match t {
        Type::Named { fqn, .. } => Some(fqn.to_string()),
        Type::Nullable(inner) => named_type_fqn(inner),
        _ => None,
    }
}

fn function_call_key(scope: &Scope, callee: &Expr) -> Option<CallableKey> {
    let ExprKind::Name(name) = &php_ast::queries::peel_paren(callee).kind else {
        return None;
    };
    let fqn = match scope.resolve_function(name) {
        Resolution::Fqn(fqn) => fqn,
        Resolution::Fallback { namespaced, .. } => namespaced,
        Resolution::LateStatic(_) | Resolution::BuiltinType(_) => return None,
    };
    Some(CallableKey::Function(fqn))
}

fn class_expr_fqn(scope: &Scope, class: &Expr) -> Option<String> {
    let ExprKind::Name(name) = &php_ast::queries::peel_paren(class).kind else {
        return None;
    };
    match scope.resolve_class(name) {
        Resolution::Fqn(fqn) => Some(fqn),
        Resolution::LateStatic(_) | Resolution::BuiltinType(_) | Resolution::Fallback { .. } => {
            None
        }
    }
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
            ExprKind::Binary {
                op: BinOp::LogicalXor,
                ..
            } => out.push(
                Diagnostic::error(e.span, "Unused result of \"xor\" operator.")
                    .with_code("logicalXor.resultUnused"),
            ),
            ExprKind::Binary {
                op: BinOp::LogicalAnd,
                ..
            } => out.push(
                Diagnostic::error(e.span, "Unused result of \"and\" operator.")
                    .with_code("logicalAnd.resultUnused"),
            ),
            ExprKind::Binary {
                op: BinOp::LogicalOr,
                ..
            } => out.push(
                Diagnostic::error(e.span, "Unused result of \"or\" operator.")
                    .with_code("logicalOr.resultUnused"),
            ),
            ExprKind::Ternary { .. } if !contains_assign(e) => out.push(
                Diagnostic::error(e.span, "Unused result of ternary operator.")
                    .with_code("ternary.resultUnused"),
            ),
            // `&&` / `||` whose result is discarded and which has no side effect
            // (the short-circuit idiom `$x && f()` has an effect → not flagged).
            ExprKind::Binary {
                op: BinOp::BoolAnd, ..
            } if !has_side_effect(e) => out.push(
                Diagnostic::error(e.span, "Unused result of \"&&\" operator.")
                    .with_code("booleanAnd.resultUnused"),
            ),
            ExprKind::Binary {
                op: BinOp::BoolOr, ..
            } if !has_side_effect(e) => out.push(
                Diagnostic::error(e.span, "Unused result of \"||\" operator.")
                    .with_code("booleanOr.resultUnused"),
            ),
            // Any other pure value expression on its own line does nothing.
            // phpstan prints the expression in the message; use the source
            // text with whitespace runs collapsed (multi-line spans).
            _ if is_pure_value_noop(e) => {
                let text = e
                    .span
                    .text(fa.source)
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .join(" ");
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!("Expression \"{text}\" on a separate line does not do anything."),
                    )
                    .with_code("expr.resultUnused"),
                )
            }
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
        &php_ast::Program {
            stmts: vec![Stmt::new(
                php_span::Span::new(0, 0),
                StmtKind::Expr(e.clone()),
            )],
        },
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
    walk::for_each_expr(
        &php_ast::Program {
            stmts: vec![Stmt::new(
                php_span::Span::new(0, 0),
                StmtKind::Expr(e.clone()),
            )],
        },
        &mut |x| {
            if matches!(
                x.kind,
                ExprKind::Assign { .. } | ExprKind::AssignOp { .. } | ExprKind::AssignRef { .. }
            ) {
                found = true;
            }
        },
    );
    found
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "deadCode.unreachable",
        level: 4,
        run: run_unreachable,
    },
    RuleEntry {
        name: "method.unused",
        level: 4,
        run: run_unused_private_method,
    },
    RuleEntry {
        name: "classConstant.unused",
        level: 4,
        run: run_unused_private_constant,
    },
    RuleEntry {
        name: "property.unused",
        level: 4,
        run: run_unused_private_property,
    },
    RuleEntry {
        name: "noop",
        level: 4,
        run: run_noop,
    },
    RuleEntry {
        name: "deadCode.function.resultUnused",
        level: 4,
        run: run_pure_function_statement_without_impure_points,
    },
    RuleEntry {
        name: "deadCode.new.resultUnused",
        level: 4,
        run: run_pure_constructor_statement_without_impure_points,
    },
    RuleEntry {
        name: "deadCode.method.resultUnused",
        level: 4,
        run: run_pure_method_statement_without_impure_points,
    },
    RuleEntry {
        name: "deadCode.staticMethod.resultUnused",
        level: 4,
        run: run_pure_static_method_statement_without_impure_points,
    },
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
        let src =
            "<?php class C { private function helper() {} function run() { $this->helper(); } }";
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
        let src =
            "<?php class C { private function helper() {} function run($m) { $this->$m(); } }";
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
        assert_eq!(
            codes(src, run_unused_private_constant),
            ["classConstant.unused"]
        );
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

    #[test]
    fn private_property_read_only_in_used_trait_is_clean() {
        // A trait method is compiled into the using class and can read the
        // class's private property; the class body itself never touches it.
        let src = "<?php \
            trait T { public function show() { return $this->data; } } \
            class C { use T; private $data = 1; }";
        assert!(codes(src, run_unused_private_property).is_empty());
    }

    #[test]
    fn private_method_called_only_from_used_trait_is_clean() {
        let src = "<?php \
            trait T { public function run() { return $this->helper(); } } \
            class C { use T; private function helper() { return 1; } }";
        assert!(codes(src, run_unused_private_method).is_empty());
    }

    #[test]
    fn private_property_unused_even_with_trait_is_flagged() {
        // The trait exists but touches nothing — the property is genuinely unused.
        let src = "<?php \
            trait T { public function run() { return 1; } } \
            class C { use T; private $data = 1; }";
        assert_eq!(codes(src, run_unused_private_property), ["property.unused"]);
    }

    // --- CallTo*StatementWithoutImpurePointsRule ------------------------

    #[test]
    fn pure_user_function_statement_is_flagged() {
        let src = "<?php /** @pure */ function value(): int { return 1; } value();";
        assert_eq!(
            codes(src, run_pure_function_statement_without_impure_points),
            ["function.resultUnused"]
        );
    }

    #[test]
    fn pure_user_function_value_used_is_clean() {
        let src = "<?php /** @pure */ function value(): int { return 1; } echo value();";
        assert!(codes(src, run_pure_function_statement_without_impure_points).is_empty());
    }

    #[test]
    fn impure_user_function_statement_is_clean() {
        let src = "<?php function value(): int { return 1; } value();";
        assert!(codes(src, run_pure_function_statement_without_impure_points).is_empty());
    }

    #[test]
    fn pure_function_with_echo_is_clean() {
        let src = "<?php /** @pure */ function value(): int { echo 1; return 1; } value();";
        assert!(codes(src, run_pure_function_statement_without_impure_points).is_empty());
    }

    #[test]
    fn pure_function_transitive_call_is_flagged() {
        let src = "<?php
            /** @pure */ function leaf(): int { return 1; }
            /** @pure */ function wrap(): int { return leaf(); }
            wrap();
        ";
        assert_eq!(
            codes(src, run_pure_function_statement_without_impure_points),
            ["function.resultUnused"]
        );
    }

    #[test]
    fn pure_function_with_unknown_call_is_clean() {
        let src = "<?php /** @pure */ function value(): int { return unknown(); } value();";
        assert!(codes(src, run_pure_function_statement_without_impure_points).is_empty());
    }

    #[test]
    fn pure_constructor_new_statement_is_flagged() {
        let src = "<?php class C { /** @pure */ public function __construct() {} } new C();";
        assert_eq!(
            codes(src, run_pure_constructor_statement_without_impure_points),
            ["new.resultUnused"]
        );
    }

    #[test]
    fn pure_constructor_with_echo_is_clean() {
        let src =
            "<?php class C { /** @pure */ public function __construct() { echo 1; } } new C();";
        assert!(codes(src, run_pure_constructor_statement_without_impure_points).is_empty());
    }

    #[test]
    fn pure_constructor_value_used_is_clean() {
        let src = "<?php class C { /** @pure */ public function __construct() {} } $c = new C();";
        assert!(codes(src, run_pure_constructor_statement_without_impure_points).is_empty());
    }

    #[test]
    fn pure_constructor_with_pure_function_dependency_is_flagged() {
        let src = "<?php
            /** @pure */ function leaf(): int { return 1; }
            class C { /** @pure */ public function __construct() { leaf(); } }
            new C();
        ";
        assert_eq!(
            codes(src, run_pure_constructor_statement_without_impure_points),
            ["new.resultUnused"]
        );
    }

    #[test]
    fn method_without_impure_points_statement_is_flagged() {
        let src = r#"<?php
            final class C {
                public function value(): int { return 1; }
            }
            function f(C $c): void { $c->value(); }
        "#;
        assert_eq!(
            codes(src, run_pure_method_statement_without_impure_points),
            ["method.resultUnused"]
        );
    }

    #[test]
    fn method_without_impure_points_value_used_is_clean() {
        let src = r#"<?php
            final class C {
                public function value(): int { return 1; }
            }
            function f(C $c): int { return $c->value(); }
        "#;
        assert!(codes(src, run_pure_method_statement_without_impure_points).is_empty());
    }

    #[test]
    fn pure_annotated_method_is_left_to_methods_rule() {
        let src = r#"<?php
            final class C {
                /** @pure */
                public function value(): int { return 1; }
            }
            function f(C $c): void { $c->value(); }
        "#;
        assert!(codes(src, run_pure_method_statement_without_impure_points).is_empty());
    }

    #[test]
    fn overridable_method_without_impure_points_is_clean() {
        let src = r#"<?php
            class C {
                public function value(): int { return 1; }
            }
            function f(C $c): void { $c->value(); }
        "#;
        assert!(codes(src, run_pure_method_statement_without_impure_points).is_empty());
    }

    #[test]
    fn method_with_argument_is_clean() {
        let src = r#"<?php
            final class C {
                public function value(int $i): int { return $i; }
            }
            function f(C $c): void { $c->value(1); }
        "#;
        assert!(codes(src, run_pure_method_statement_without_impure_points).is_empty());
    }

    #[test]
    fn method_with_impure_point_is_clean() {
        let src = r#"<?php
            final class C {
                public function value(): int { echo 1; return 1; }
            }
            function f(C $c): void { $c->value(); }
        "#;
        assert!(codes(src, run_pure_method_statement_without_impure_points).is_empty());
    }

    #[test]
    fn method_with_private_pure_dependency_is_flagged() {
        let src = r#"<?php
            final class C {
                private function leaf(): int { return 1; }
                public function value(): int { return $this->leaf(); }
            }
            function f(C $c): void { $c->value(); }
        "#;
        assert_eq!(
            codes(src, run_pure_method_statement_without_impure_points),
            ["method.resultUnused"]
        );
    }

    #[test]
    fn static_method_without_impure_points_statement_is_flagged() {
        let src = r#"<?php
            class C {
                public static function value(): int { return 1; }
            }
            C::value();
        "#;
        assert_eq!(
            codes(src, run_pure_static_method_statement_without_impure_points),
            ["staticMethod.resultUnused"]
        );
    }

    #[test]
    fn pure_annotated_static_method_is_left_to_methods_rule() {
        let src = r#"<?php
            class C {
                /** @pure */
                public static function value(): int { return 1; }
            }
            C::value();
        "#;
        assert!(codes(src, run_pure_static_method_statement_without_impure_points).is_empty());
    }

    #[test]
    fn self_static_method_call_is_clean() {
        let src = r#"<?php
            class C {
                public static function value(): int { return 1; }
                public function f(): void { self::value(); }
            }
        "#;
        assert!(codes(src, run_pure_static_method_statement_without_impure_points).is_empty());
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
        // phpstan-faithful message: the expression text is included.
        let ds = crate::testutil::run("<?php $a;", run_noop);
        assert_eq!(
            ds[0].message,
            "Expression \"$a\" on a separate line does not do anything."
        );
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
        assert_eq!(
            codes("<?php $a && $b;", run_noop),
            ["booleanAnd.resultUnused"]
        );
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
