//! phpstan category **Constants** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Constants/`. Checklist: docs/phpstan-rules.md.
//! Each rule is a `RuleEntry` in `RULES`; diagnostics carry phpstan identifiers.
//!
//! Implemented:
//! - **ClassAsClassConstantRule** (`classConstant.class`, L0) — a class constant
//!   named `class` (reserved for `::class` name fetching). Purely syntactic.
//! - **FinalPrivateConstantRule** (`classConstant.finalPrivate`, L0) — a `final
//!   private` class constant (final is pointless: private consts are never
//!   inherited/overridden). Purely syntactic.
//! - **MagicConstantContextRule** (`magicConstant.outOfClass` /
//!   `magicConstant.outOfTrait` / `magicConstant.outOfFunction` /
//!   `magicConstant.outOfNamespace`, L0) — a magic constant used where it is
//!   always empty (`__CLASS__` outside a class, etc.). Context-tracked traversal.
//! - **OverridingConstantRule** (`classConstant.final` / `classConstant.visibility`,
//!   L0) — overriding a parent/interface constant that is `final`, or narrowing
//!   its visibility. Reflection-driven; gated on `class_fully_known`.
//! - **DynamicClassConstantFetchRule** (`classConstant.nameType`, L0) — a dynamic
//!   class-constant fetch (`Foo::{$x}`) whose name expression can never be a
//!   string. Type-driven, zero-FP (only flags definitely-non-string names).
//! - **ValueAssignedToClassConstantRule** (`classConstant.value`, L2) — a class
//!   constant with a native type whose initializer value can never satisfy it.
//!   Type-driven; only fires when both the native type and the value are concrete
//!   and known-incompatible.
//! - **ConstantAttributesRule** (`constant.attributesNotSupported`, L0) — global
//!   constant attributes on target PHP versions below 8.5.
//!
//! Deferred:
//! - **FinalConstantRule** (`classConstant.finalNotSupported`) &
//!   **NativeTypedClassConstantRule** (`classConstant.nativeTypeNotSupported`) &
//!   the `classConstant.dynamicFetch` branch of DynamicClassConstantFetchRule:
//!   all are pure PHP-version gates ("supported only on PHP 8.x and later"). Our
//!   target is 8.6-dev, so these never fire — implementing them would require a
//!   configurable `phpVersion` that always says "supported".
//! - **OverridingConstantRule** native-type/phpdoc covariance branches
//!   (`classConstant.nativeType` / `classConstant.missingNativeType` /
//!   `classConstant.type`): gated behind phpstan's `checkPhpDocMethodSignatures`
//!   toggle and need value-type/covariance comparison we keep conservative.
//! - **MissingClassConstantTypehintRule** (`missingType.*`, L6): requires the
//!   MissingTypehintCheck facility (iterable-value / generics / callable-signature
//!   detection) shared with many rules — out of scope for this file.
//! - **ValueAssignedToGlobalConstantRule** / **ValueAssignedToDefineRule**: check
//!   values against *configured* expected types of known constants — needs the
//!   ConstantResolver config table we don't model.

#![allow(unused_imports)]
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{
    ClassConstDecl, ClassDecl, ClassKind, Expr, ExprKind, Member, MemberName, Name, Stmt, StmtKind,
    Visibility,
};
use php_diagnostics::Diagnostic;
use php_infer::is_assignable;
use php_intern::Interner;
use php_resolve::{for_each_region, Resolution, Scope};
use php_types::Type;

// ---------------------------------------------------------------------------
// Shared: visit each class-like decl with the scope of its namespace region.
// (Mirrors classes.rs::for_each_class; kept local since that one is private.)
// ---------------------------------------------------------------------------

fn for_each_class(
    program: &php_ast::Program,
    interner: &Interner,
    mut f: impl FnMut(&Scope, &ClassDecl),
) {
    fn visit(scope: &Scope, st: &Stmt, f: &mut impl FnMut(&Scope, &ClassDecl)) {
        match &st.kind {
            StmtKind::Class(c) => {
                f(scope, c);
                // Nested anonymous classes live inside member bodies; those are
                // reached by the per-class member walks where needed, not here.
            }
            StmtKind::Block(b) => b.iter().for_each(|s| visit(scope, s, f)),
            StmtKind::If {
                then, elseifs, els, ..
            } => {
                visit(scope, then, f);
                for e in elseifs {
                    visit(scope, &e.body, f);
                }
                if let Some(e) = els {
                    visit(scope, e, f);
                }
            }
            StmtKind::While { body, .. }
            | StmtKind::DoWhile { body, .. }
            | StmtKind::For { body, .. }
            | StmtKind::Foreach { body, .. } => visit(scope, body, f),
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                body.iter().for_each(|s| visit(scope, s, f));
                for c in catches {
                    c.body.iter().for_each(|s| visit(scope, s, f));
                }
                if let Some(fin) = finally {
                    fin.iter().for_each(|s| visit(scope, s, f));
                }
            }
            StmtKind::Switch { cases, .. } => {
                for c in cases {
                    c.body.iter().for_each(|s| visit(scope, s, f));
                }
            }
            StmtKind::Declare { body: Some(b), .. } => visit(scope, b, f),
            _ => {}
        }
    }
    for_each_region(&program.stmts, interner, |scope, region| {
        for st in region {
            visit(scope, st, &mut f);
        }
    });
}

/// The display label phpstan uses (`false` = without generics): a class's name.
fn class_display(c: &ClassDecl, scope: &Scope, interner: &Interner) -> String {
    match c.name {
        Some(n) => scope.qualify(interner.resolve(n)),
        None => "class@anonymous".to_string(),
    }
}

// ---------------------------------------------------------------------------
// ClassAsClassConstantRule — `classConstant.class` (level 0)
// ---------------------------------------------------------------------------

/// A class constant must not be named `class` (`Foo::class` is reserved).
fn run_class_as_class_constant(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |_scope, c| {
        for m in &c.members {
            let Member::ClassConst(cd) = m else { continue };
            for ce in &cd.consts {
                if fa.interner.resolve(ce.name).eq_ignore_ascii_case("class") {
                    out.push(
                        Diagnostic::error(
                            ce.value.span,
                            "A class constant must not be called 'class'; it is reserved for class name fetching.",
                        )
                        .with_code("classConstant.class"),
                    );
                }
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// FinalPrivateConstantRule — `classConstant.finalPrivate` (level 0)
// ---------------------------------------------------------------------------

/// `FinalConstantRule` — a `final` class constant on a target PHP version that
/// doesn't support them (< 8.1). Gates on `fa.php_version` (default 8.4 → silent).
fn run_final_constant_version(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if fa.php_version.at_least(80100) {
        return Vec::new();
    }
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |_scope, c| {
        for m in &c.members {
            let Member::ClassConst(cd) = m else { continue };
            if cd.modifiers.is_final {
                if let Some(ce) = cd.consts.first() {
                    out.push(
                        Diagnostic::error(
                            ce.value.span,
                            "Final class constants are supported only on PHP 8.1 and later.",
                        )
                        .with_code("classConstant.finalNotSupported"),
                    );
                }
            }
        }
    });
    out
}

/// `NativeTypedClassConstantRule` — a class constant with a native type on a
/// target PHP version that doesn't support them (< 8.3).
fn run_native_typed_constant_version(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if fa.php_version.at_least(80300) {
        return Vec::new();
    }
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |_scope, c| {
        for m in &c.members {
            let Member::ClassConst(cd) = m else { continue };
            if cd.ty.is_some() {
                if let Some(ce) = cd.consts.first() {
                    out.push(
                        Diagnostic::error(
                            ce.value.span,
                            "Class constants with native types are supported only on PHP 8.3 and later.",
                        )
                        .with_code("classConstant.nativeTypeNotSupported"),
                    );
                }
            }
        }
    });
    out
}

/// `ConstantAttributesRule` — attributes on global constants are PHP 8.5+.
/// The target/repeatability checks for the attributes themselves are handled by
/// the shared `attribute.usage` rule once the target version supports the syntax.
fn run_constant_attributes_version(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if fa.php_version.at_least(80500) {
        return Vec::new();
    }
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |st| {
        let StmtKind::ConstDecl { attrs, .. } = &st.kind else {
            return;
        };
        if attrs.is_empty() {
            return;
        }
        out.push(
            Diagnostic::error(
                st.span,
                "Attributes on global constants are supported only on PHP 8.5 and later.",
            )
            .with_code("constant.attributesNotSupported"),
        );
    });
    out
}

/// `MissingClassConstantTypehintRule` (`missingType.iterableValue`): a class
/// constant with a *native* type that is a bare `array`/`iterable` (no value
/// type), e.g. `const array FOO = […]`. Conservative — only native-typed constants
/// with no `@var` (which could supply a value type) in a fully-known class. An
/// untyped constant infers its value type from the literal, so it's never bare.
fn run_missing_const_iterable_value(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |scope, c| {
        let Some(nm) = c.name else { return };
        let fqn = scope.qualify(fa.interner.resolve(nm));
        if !fa.class_fully_known(&fqn) {
            return;
        }
        let short = fqn.trim_start_matches('\\').to_string();
        for m in &c.members {
            let Member::ClassConst(cd) = m else { continue };
            let Some(ty) = &cd.ty else { continue };
            if cd.doc.as_deref().is_some_and(|d| d.contains("@var")) {
                continue;
            }
            let resolved = php_reflect::resolve_ast_type(scope, ty);
            let Some(word) = crate::rules::functions::bare_iterable_word(&resolved) else {
                continue;
            };
            for ce in &cd.consts {
                let cname = fa.interner.resolve(ce.name);
                out.push(
                    Diagnostic::error(
                        ce.value.span,
                        format!(
                            "Constant {short}::{cname} type has no value type specified in \
                             iterable type {word}."
                        ),
                    )
                    .with_code("missingType.iterableValue"),
                );
            }
        }
    });
    out
}

/// A `final private` class constant: final is meaningless because private
/// constants are never inherited and so can never be overridden.
fn run_final_private_constant(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |scope, c| {
        let display = class_display(c, scope, fa.interner);
        for m in &c.members {
            let Member::ClassConst(cd) = m else { continue };
            if !(cd.modifiers.is_final && cd.modifiers.visibility == Some(Visibility::Private)) {
                continue;
            }
            for ce in &cd.consts {
                out.push(
                    Diagnostic::error(
                        ce.value.span,
                        format!(
                            "Private constant {}::{} cannot be final as it is never overridden by other classes.",
                            display,
                            fa.interner.resolve(ce.name),
                        ),
                    )
                    .with_code("classConstant.finalPrivate"),
                );
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// MagicConstantContextRule — `magicConstant.*` (level 0)
// ---------------------------------------------------------------------------

/// Lexical context for a magic-constant occurrence.
#[derive(Clone, Copy, Default)]
struct MagicCtx {
    in_class: bool,
    in_trait: bool,
    in_function: bool,
    in_namespace: bool,
}

/// `__CLASS__`, `__TRAIT__`, `__FUNCTION__`/`__METHOD__`, `__NAMESPACE__` are
/// always empty outside their respective context — flag those uses.
fn run_magic_constant_context(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    // Each namespace region carries whether we are inside a (non-global) namespace.
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        let ctx = MagicCtx {
            in_namespace: scope.namespace().is_some(),
            ..MagicCtx::default()
        };
        for st in region {
            visit_stmt(fa, st, ctx, &mut out);
        }
    });
    out
}

fn visit_stmt(fa: &FileAnalysis, st: &Stmt, ctx: MagicCtx, out: &mut Vec<Diagnostic>) {
    match &st.kind {
        StmtKind::Class(c) => {
            // A new class/trait body: set the class/trait flags, clear function.
            let inner = MagicCtx {
                in_class: true,
                in_trait: c.kind == ClassKind::Trait,
                in_function: false,
                in_namespace: ctx.in_namespace,
            };
            for m in &c.members {
                match m {
                    Member::Method(md) => {
                        let mctx = MagicCtx {
                            in_function: true,
                            ..inner
                        };
                        // Default values / attributes of params are evaluated in
                        // the class context but NOT the function context.
                        if let Some(body) = &md.body {
                            for s in body {
                                visit_stmt(fa, s, mctx, out);
                            }
                        }
                        // Param defaults: in-class, out-of-function.
                        for p in &md.params {
                            if let Some(d) = &p.default {
                                visit_expr(fa, d, inner, out);
                            }
                        }
                    }
                    Member::Property(pd) => {
                        for pe in &pd.props {
                            if let Some(d) = &pe.default {
                                visit_expr(fa, d, inner, out);
                            }
                        }
                    }
                    Member::ClassConst(cd) => {
                        for ce in &cd.consts {
                            visit_expr(fa, &ce.value, inner, out);
                        }
                    }
                    Member::EnumCase(ec) => {
                        if let Some(v) = &ec.value {
                            visit_expr(fa, v, inner, out);
                        }
                    }
                    Member::TraitUse(_) => {}
                }
            }
        }
        StmtKind::Function(f) => {
            let inner = MagicCtx {
                in_function: true,
                in_class: false,
                in_trait: false,
                ..ctx
            };
            for s in &f.body {
                visit_stmt(fa, s, inner, out);
            }
            // Param defaults are in the enclosing (non-function) scope.
            for p in &f.params {
                if let Some(d) = &p.default {
                    visit_expr(fa, d, ctx, out);
                }
            }
        }
        StmtKind::Expr(e) => visit_expr(fa, e, ctx, out),
        StmtKind::Echo(es) => es.iter().for_each(|e| visit_expr(fa, e, ctx, out)),
        StmtKind::Return(Some(e)) => visit_expr(fa, e, ctx, out),
        StmtKind::Block(b) => b.iter().for_each(|s| visit_stmt(fa, s, ctx, out)),
        StmtKind::If {
            cond,
            then,
            elseifs,
            els,
        } => {
            visit_expr(fa, cond, ctx, out);
            visit_stmt(fa, then, ctx, out);
            for ei in elseifs {
                visit_expr(fa, &ei.cond, ctx, out);
                visit_stmt(fa, &ei.body, ctx, out);
            }
            if let Some(e) = els {
                visit_stmt(fa, e, ctx, out);
            }
        }
        StmtKind::While { cond, body } => {
            visit_expr(fa, cond, ctx, out);
            visit_stmt(fa, body, ctx, out);
        }
        StmtKind::DoWhile { body, cond } => {
            visit_stmt(fa, body, ctx, out);
            visit_expr(fa, cond, ctx, out);
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
                .for_each(|e| visit_expr(fa, e, ctx, out));
            visit_stmt(fa, body, ctx, out);
        }
        StmtKind::Foreach {
            subject,
            key,
            value,
            body,
            ..
        } => {
            visit_expr(fa, subject, ctx, out);
            if let Some(k) = key {
                visit_expr(fa, k, ctx, out);
            }
            visit_expr(fa, value, ctx, out);
            visit_stmt(fa, body, ctx, out);
        }
        StmtKind::Switch { subject, cases } => {
            visit_expr(fa, subject, ctx, out);
            for c in cases {
                if let Some(t) = &c.test {
                    visit_expr(fa, t, ctx, out);
                }
                c.body.iter().for_each(|s| visit_stmt(fa, s, ctx, out));
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter().for_each(|s| visit_stmt(fa, s, ctx, out));
            for c in catches {
                c.body.iter().for_each(|s| visit_stmt(fa, s, ctx, out));
            }
            if let Some(fin) = finally {
                fin.iter().for_each(|s| visit_stmt(fa, s, ctx, out));
            }
        }
        StmtKind::Declare { body: Some(b), .. } => visit_stmt(fa, b, ctx, out),
        StmtKind::ConstDecl { consts, .. } => {
            consts
                .iter()
                .for_each(|ce| visit_expr(fa, &ce.value, ctx, out));
        }
        _ => {}
    }
}

fn visit_expr(fa: &FileAnalysis, e: &Expr, ctx: MagicCtx, out: &mut Vec<Diagnostic>) {
    // Closures and arrow functions ARE functions — `__FUNCTION__` is defined in
    // them (anonymous, but non-empty), so flip in_function on. They do not
    // change the class/trait/namespace context.
    match &e.kind {
        ExprKind::Name(n) => {
            check_magic(n, ctx, out);
            return; // a bare name has no children
        }
        ExprKind::Closure(cl) => {
            let inner = MagicCtx {
                in_function: true,
                ..ctx
            };
            for s in &cl.body {
                visit_stmt(fa, s, inner, out);
            }
            // `use (...)` captures + param defaults are in the OUTER scope.
            for p in &cl.params {
                if let Some(d) = &p.default {
                    visit_expr(fa, d, ctx, out);
                }
            }
            return;
        }
        ExprKind::ArrowFn(af) => {
            let inner = MagicCtx {
                in_function: true,
                ..ctx
            };
            visit_expr(fa, &af.body, inner, out);
            for p in &af.params {
                if let Some(d) = &p.default {
                    visit_expr(fa, d, ctx, out);
                }
            }
            return;
        }
        _ => {}
    }
    // Generic descent: visit every child expression of `e` in the same context.
    let mut child = |c: &Expr| visit_expr(fa, c, ctx, out);
    each_child_expr(e, &mut child);
}

/// Apply `f` to each immediate child expression of `e` (no scope crossing into
/// closures/arrow-fns — those are handled explicitly in `visit_expr`).
fn each_child_expr(e: &Expr, f: &mut impl FnMut(&Expr)) {
    use ExprKind::*;
    match &e.kind {
        Interpolated(ps) | ShellExec(ps) => ps.iter().for_each(f),
        VariableVariable(x)
        | DollarBrace(x)
        | Unary { expr: x, .. }
        | Cast { expr: x, .. }
        | PreInc(x)
        | PreDec(x)
        | PostInc(x)
        | PostDec(x)
        | Clone(x)
        | Print(x)
        | Throw(x)
        | ErrorSuppress(x)
        | YieldFrom(x)
        | Eval(x)
        | Empty(x)
        | Paren(x) => f(x),
        Array { items, .. } => {
            for it in items {
                if let Some(k) = &it.key {
                    f(k);
                }
                if let Some(v) = &it.value {
                    f(v);
                }
            }
        }
        Call { callee, args } => {
            f(callee);
            args.iter().for_each(|a| f(&a.value));
        }
        MethodCall {
            recv, method, args, ..
        } => {
            f(recv);
            if let MemberName::Expr(x) = method {
                f(x);
            }
            args.iter().for_each(|a| f(&a.value));
        }
        StaticCall {
            class,
            method,
            args,
        } => {
            f(class);
            if let MemberName::Expr(x) = method {
                f(x);
            }
            args.iter().for_each(|a| f(&a.value));
        }
        New { class, args } => {
            f(class);
            args.iter().for_each(|a| f(&a.value));
        }
        Index { base, index } => {
            f(base);
            if let Some(i) = index {
                f(i);
            }
        }
        Prop { base, name, .. } => {
            f(base);
            if let MemberName::Expr(x) = name {
                f(x);
            }
        }
        StaticProp { class, name } => {
            f(class);
            if let MemberName::Expr(x) = name {
                f(x);
            }
        }
        ClassConst { class, name } => {
            f(class);
            if let MemberName::Expr(x) = name {
                f(x);
            }
        }
        Binary { lhs, rhs, .. }
        | Assign { target: lhs, rhs }
        | AssignOp {
            target: lhs, rhs, ..
        }
        | AssignRef { target: lhs, rhs }
        | Coalesce { lhs, rhs } => {
            f(lhs);
            f(rhs);
        }
        Ternary { cond, then, els } => {
            f(cond);
            if let Some(t) = then {
                f(t);
            }
            f(els);
        }
        Instanceof { expr, class } => {
            f(expr);
            f(class);
        }
        Yield { key, value } => {
            if let Some(k) = key {
                f(k);
            }
            if let Some(v) = value {
                f(v);
            }
        }
        Exit(Some(x)) | Include { expr: x, .. } => f(x),
        Isset(xs) => xs.iter().for_each(f),
        Match { subject, arms } => {
            f(subject);
            for arm in arms {
                if let Some(cs) = &arm.conds {
                    cs.iter().for_each(&mut *f);
                }
                f(&arm.body);
            }
        }
        NewAnon { args, .. } => args.iter().for_each(|a| f(&a.value)),
        _ => {}
    }
}

/// Flag a magic constant that is empty in the current context.
fn check_magic(n: &Name, ctx: MagicCtx, out: &mut Vec<Diagnostic>) {
    // Magic constants are written FQ-less; match case-insensitively (PHP does).
    let t = n.text.as_str();
    let (kind, ident, msg): (&str, &'static str, &str) = match () {
        _ if t.eq_ignore_ascii_case("__CLASS__") => {
            if ctx.in_class {
                return;
            }
            ("__CLASS__", "magicConstant.outOfClass", "outside a class")
        }
        _ if t.eq_ignore_ascii_case("__TRAIT__") => {
            if ctx.in_trait {
                return;
            }
            ("__TRAIT__", "magicConstant.outOfTrait", "outside a trait")
        }
        _ if t.eq_ignore_ascii_case("__FUNCTION__") || t.eq_ignore_ascii_case("__METHOD__") => {
            if ctx.in_function {
                return;
            }
            (
                if t.eq_ignore_ascii_case("__METHOD__") {
                    "__METHOD__"
                } else {
                    "__FUNCTION__"
                },
                "magicConstant.outOfFunction",
                "outside a function",
            )
        }
        _ if t.eq_ignore_ascii_case("__NAMESPACE__") => {
            if ctx.in_namespace {
                return;
            }
            (
                "__NAMESPACE__",
                "magicConstant.outOfNamespace",
                "in global namespace",
            )
        }
        _ => return,
    };
    out.push(
        Diagnostic::error(
            n.span,
            format!("Magic constant {kind} is always empty {msg}."),
        )
        .with_code(ident),
    );
}

// ---------------------------------------------------------------------------
// OverridingConstantRule — `classConstant.final` / `classConstant.visibility`
// (level 0)
// ---------------------------------------------------------------------------

/// Overriding a parent/interface constant: cannot override a `final` constant,
/// and cannot narrow visibility below the overridden one.
fn run_overriding_constant(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |scope, c| {
        let Some(_) = c.name else { return };
        let fqn = class_display(c, scope, fa.interner);
        // Only reason about a class whose whole hierarchy is reflected: an
        // unindexed/built-in ancestor could carry the overridden constant.
        if !fa.class_fully_known(&fqn) {
            return;
        }
        let display = fqn.trim_start_matches('\\');
        for m in &c.members {
            let Member::ClassConst(cd) = m else { continue };
            for ce in &cd.consts {
                let name = fa.interner.resolve(ce.name);
                if name.eq_ignore_ascii_case("class") {
                    continue;
                }
                let Some(proto) = find_prototype(fa, c, scope, &fqn, name) else {
                    continue;
                };
                let own_vis = cd.modifiers.visibility.unwrap_or(Visibility::Public);

                if proto.member.is_final {
                    out.push(
                        Diagnostic::error(
                            ce.value.span,
                            format!(
                                "Constant {display}::{name} overrides final constant {}::{name}.",
                                proto.declaring_class.trim_start_matches('\\'),
                            ),
                        )
                        .with_code("classConstant.final"),
                    );
                }

                // Visibility narrowing checks (mirror phpstan exactly).
                let proto_decl = proto.declaring_class.trim_start_matches('\\');
                if proto.member.visibility == Visibility::Public {
                    if own_vis != Visibility::Public {
                        let kw = if own_vis == Visibility::Private {
                            "Private"
                        } else {
                            "Protected"
                        };
                        out.push(
                            Diagnostic::error(
                                ce.value.span,
                                format!(
                                    "{kw} constant {display}::{name} overriding public constant {proto_decl}::{name} should also be public.",
                                ),
                            )
                            .with_code("classConstant.visibility"),
                        );
                    }
                } else if proto.member.visibility == Visibility::Protected
                    && own_vis == Visibility::Private
                {
                    out.push(
                        Diagnostic::error(
                            ce.value.span,
                            format!(
                                "Private constant {display}::{name} overriding protected constant {proto_decl}::{name} should be protected or public.",
                            ),
                        )
                        .with_code("classConstant.visibility"),
                    );
                }
            }
        }
    });
    out
}

/// phpstan's `findPrototype`: an immediate interface's constant wins; otherwise
/// the parent class's constant (unless private). Returns the overridden one.
fn find_prototype(
    fa: &FileAnalysis,
    c: &ClassDecl,
    scope: &Scope,
    _self_fqn: &str,
    name: &str,
) -> Option<php_reflect::Found<php_reflect::ConstReflection>> {
    // Immediate interfaces first (in declaration order).
    for iface in &c.implements {
        if let Resolution::Fqn(ifqn) = scope.resolve_class(iface) {
            if let Some(found) = fa.reflection.find_constant(&ifqn, name) {
                return Some(found);
            }
        }
    }
    // Then the parent class (a class has at most one `extends`).
    for parent in &c.extends {
        if let Resolution::Fqn(pfqn) = scope.resolve_class(parent) {
            if let Some(found) = fa.reflection.find_constant(&pfqn, name) {
                // A private parent constant is not actually inherited.
                if found.member.visibility == Visibility::Private {
                    return None;
                }
                return Some(found);
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// DynamicClassConstantFetchRule — `classConstant.nameType` (level 0)
// ---------------------------------------------------------------------------

/// A dynamic class-constant fetch `Foo::{$expr}` whose name expression can never
/// be a string. (The PHP-version gate `classConstant.dynamicFetch` is deferred —
/// our target supports dynamic fetch.)
fn run_dynamic_class_constant_fetch(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::ClassConst { name, .. } = &e.kind else {
            return;
        };
        let MemberName::Expr(name_expr) = name else {
            return;
        };
        let t = fa.type_of(name_expr);
        if never_string(&t) {
            out.push(
                Diagnostic::error(
                    e.span,
                    format!(
                        "Class constant name in dynamic fetch can only be a string, {t} given."
                    ),
                )
                .with_code("classConstant.nameType"),
            );
        }
    });
    out
}

// ---------------------------------------------------------------------------
// ValueAssignedToClassConstantRule — `classConstant.value` (level 2)
// ---------------------------------------------------------------------------

/// A class constant with a *native* type whose initializer value can never be
/// accepted by that type. Conservative: fires only when the value type and the
/// resolved native type are both concrete and definitely incompatible.
/// The type of a constant initializer (constant-folded). Initializers aren't in
/// the flow type-map; a non-constant initializer yields `mixed` (skipped).
fn literal_value_type(e: &Expr) -> php_types::Type {
    use php_infer::ConstVal;
    use php_types::Type;
    match php_infer::eval_const(e) {
        Some(ConstVal::Int(_)) => Type::Int,
        Some(ConstVal::Float(_)) => Type::Float,
        Some(ConstVal::Bool(_)) => Type::Bool,
        Some(ConstVal::Str(_)) => Type::String,
        Some(ConstVal::Null) => Type::Null,
        None => match &e.kind {
            ExprKind::Array { .. } => Type::Array(None),
            _ => Type::Mixed,
        },
    }
}

fn run_value_assigned_to_class_constant(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |scope, c| {
        let Some(_) = c.name else { return };
        let fqn = class_display(c, scope, fa.interner);
        let display = fqn.trim_start_matches('\\');
        for m in &c.members {
            let Member::ClassConst(cd) = m else { continue };
            // Only check constants that declare a NATIVE type (`const int X = …`).
            if cd.ty.is_none() {
                continue;
            }
            for ce in &cd.consts {
                let name = fa.interner.resolve(ce.name);
                // Resolve the constant's declared type via reflection (native).
                let Some(found) = fa.reflection.find_constant(&fqn, name) else {
                    continue;
                };
                let target = &found.member.ty;
                if !is_concrete(target) {
                    continue;
                }
                // Const initializers aren't in the flow type-map; fold the literal.
                let value = literal_value_type(&ce.value);
                if !is_concrete(&value) {
                    continue;
                }
                if !is_assignable(fa.reflection, &value, target) {
                    out.push(
                        Diagnostic::error(
                            ce.value.span,
                            format!("Constant {display}::{name} ({target}) does not accept value {value}."),
                        )
                        .with_code("classConstant.value"),
                    );
                }
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// Conservative type classifiers (zero false positives).
// ---------------------------------------------------------------------------

/// `true` only if `t` can never be a string (matches cast.rs's `never_string`).
fn never_string(t: &Type) -> bool {
    match t {
        Type::Array(_) | Type::Iterable(_) | Type::List(_) | Type::Shape { .. } => true,
        Type::Int
        | Type::Float
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Null
        | Type::String
        | Type::LiteralInt(_)
        | Type::LiteralString(_) => false,
        Type::Union(parts) => !parts.is_empty() && parts.iter().all(never_string),
        Type::Nullable(inner) => never_string(inner),
        _ => false,
    }
}

/// A type concrete enough to compare without risking a false positive: not
/// `mixed`/`Unknown`/templates and (for named types) reflected. We deliberately
/// only allow scalars/null/scalar-literals here — `is_assignable` is lenient on
/// classes/arrays anyway, but for the value rule we want a tight, obvious set.
fn is_concrete(t: &Type) -> bool {
    matches!(
        t,
        Type::Int
            | Type::Float
            | Type::Bool
            | Type::True
            | Type::False
            | Type::Null
            | Type::String
            | Type::LiteralInt(_)
            | Type::LiteralString(_)
    )
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "missingType.iterableValue",
        level: 6,
        run: run_missing_const_iterable_value,
    },
    RuleEntry {
        name: "classConstant.class",
        level: 0,
        run: run_class_as_class_constant,
    },
    RuleEntry {
        name: "classConstant.finalPrivate",
        level: 0,
        run: run_final_private_constant,
    },
    RuleEntry {
        name: "magicConstant.context",
        level: 0,
        run: run_magic_constant_context,
    },
    RuleEntry {
        name: "classConstant.overriding",
        level: 0,
        run: run_overriding_constant,
    },
    RuleEntry {
        name: "classConstant.nameType",
        level: 0,
        run: run_dynamic_class_constant_fetch,
    },
    RuleEntry {
        name: "classConstant.value",
        level: 2,
        run: run_value_assigned_to_class_constant,
    },
    RuleEntry {
        name: "classConstant.finalNotSupported",
        level: 0,
        run: run_final_constant_version,
    },
    RuleEntry {
        name: "classConstant.nativeTypeNotSupported",
        level: 0,
        run: run_native_typed_constant_version,
    },
    RuleEntry {
        name: "constant.attributesNotSupported",
        level: 0,
        run: run_constant_attributes_version,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{codes, codes_version};
    use crate::PhpVersion;

    // --- MissingClassConstantTypehintRule (missingType.iterableValue) ----

    #[test]
    fn bare_array_typed_const_flagged() {
        let src = r#"<?php class C { const array FOO = [1, 2]; }"#;
        assert_eq!(
            codes(src, run_missing_const_iterable_value),
            ["missingType.iterableValue"]
        );
    }

    #[test]
    fn typed_const_with_var_value_type_clean() {
        let src = r#"<?php class C { /** @var array<int, int> */ const array FOO = [1, 2]; }"#;
        assert!(codes(src, run_missing_const_iterable_value).is_empty());
    }

    #[test]
    fn untyped_const_clean() {
        // No native type → value type inferred from the literal → never bare.
        let src = r#"<?php class C { const FOO = [1, 2]; }"#;
        assert!(codes(src, run_missing_const_iterable_value).is_empty());
    }

    #[test]
    fn scalar_typed_const_clean() {
        let src = r#"<?php class C { const int FOO = 1; }"#;
        assert!(codes(src, run_missing_const_iterable_value).is_empty());
    }

    // --- version-gated: final / native-typed class constants -------------

    #[test]
    fn final_const_flagged_below_81() {
        let src = "<?php class C { final const X = 1; }";
        let v80 = PhpVersion::parse("8.0").unwrap();
        assert_eq!(
            codes_version(src, run_final_constant_version, v80),
            ["classConstant.finalNotSupported"]
        );
    }

    #[test]
    fn final_const_clean_at_default() {
        // Default target (8.4) supports final constants -> silent.
        let src = "<?php class C { final const X = 1; }";
        assert!(codes(src, run_final_constant_version).is_empty());
    }

    #[test]
    fn native_typed_const_flagged_below_83() {
        let src = "<?php class C { const int X = 1; }";
        let v82 = PhpVersion::parse("8.2").unwrap();
        assert_eq!(
            codes_version(src, run_native_typed_constant_version, v82),
            ["classConstant.nativeTypeNotSupported"]
        );
    }

    #[test]
    fn native_typed_const_clean_at_default() {
        let src = "<?php class C { const int X = 1; }";
        assert!(codes(src, run_native_typed_constant_version).is_empty());
    }

    #[test]
    fn global_constant_attributes_flagged_below_85() {
        let src = "<?php #[A] const X = 1;";
        let v84 = PhpVersion::parse("8.4").unwrap();
        assert_eq!(
            codes_version(src, run_constant_attributes_version, v84),
            ["constant.attributesNotSupported"]
        );
    }

    #[test]
    fn global_constant_attributes_clean_at_85() {
        let src = "<?php #[A] const X = 1;";
        let v85 = PhpVersion::parse("8.5").unwrap();
        assert!(codes_version(src, run_constant_attributes_version, v85).is_empty());
    }

    #[test]
    fn global_constant_without_attributes_is_clean_below_85() {
        let src = "<?php const X = 1;";
        let v84 = PhpVersion::parse("8.4").unwrap();
        assert!(codes_version(src, run_constant_attributes_version, v84).is_empty());
    }

    // --- ClassAsClassConstantRule --------------------------------------------

    #[test]
    fn class_named_class_is_flagged() {
        let src = "<?php class A { const class = 1; }";
        assert_eq!(
            codes(src, run_class_as_class_constant),
            ["classConstant.class"]
        );
    }

    #[test]
    fn class_named_class_case_insensitive() {
        let src = "<?php class A { const CLASS = 1; }";
        assert_eq!(
            codes(src, run_class_as_class_constant),
            ["classConstant.class"]
        );
    }

    #[test]
    fn normal_constant_name_is_ok() {
        let src = "<?php class A { const FOO = 1, BAR = 2; }";
        assert!(codes(src, run_class_as_class_constant).is_empty());
    }

    // --- FinalPrivateConstantRule --------------------------------------------

    #[test]
    fn final_private_constant_is_flagged() {
        let src = "<?php class A { final private const X = 1; }";
        assert_eq!(
            codes(src, run_final_private_constant),
            ["classConstant.finalPrivate"]
        );
    }

    #[test]
    fn final_public_constant_is_ok() {
        let src = "<?php class A { final public const X = 1; final const Y = 2; }";
        assert!(codes(src, run_final_private_constant).is_empty());
    }

    #[test]
    fn private_nonfinal_constant_is_ok() {
        let src = "<?php class A { private const X = 1; }";
        assert!(codes(src, run_final_private_constant).is_empty());
    }

    #[test]
    fn final_private_multi_decl_flags_each() {
        let src = "<?php class A { final private const X = 1, Y = 2; }";
        assert_eq!(
            codes(src, run_final_private_constant),
            ["classConstant.finalPrivate", "classConstant.finalPrivate"]
        );
    }

    // --- MagicConstantContextRule --------------------------------------------

    #[test]
    fn class_magic_outside_class_is_flagged() {
        assert_eq!(
            codes("<?php echo __CLASS__;", run_magic_constant_context),
            ["magicConstant.outOfClass"]
        );
    }

    #[test]
    fn class_magic_inside_class_is_ok() {
        let src = "<?php class A { public function m() { return __CLASS__; } }";
        assert!(codes(src, run_magic_constant_context).is_empty());
    }

    #[test]
    fn class_magic_in_method_const_default_ok() {
        // `__CLASS__` in a class constant initializer is inside the class.
        let src = "<?php class A { const X = __CLASS__; }";
        assert!(codes(src, run_magic_constant_context).is_empty());
    }

    #[test]
    fn trait_magic_outside_trait_is_flagged() {
        // Inside a class but not a trait → __TRAIT__ is empty.
        let src = "<?php class A { public function m() { return __TRAIT__; } }";
        assert_eq!(
            codes(src, run_magic_constant_context),
            ["magicConstant.outOfTrait"]
        );
    }

    #[test]
    fn trait_magic_inside_trait_is_ok() {
        let src = "<?php trait T { public function m() { return __TRAIT__; } }";
        assert!(codes(src, run_magic_constant_context).is_empty());
    }

    #[test]
    fn function_magic_outside_function_is_flagged() {
        assert_eq!(
            codes("<?php echo __FUNCTION__;", run_magic_constant_context),
            ["magicConstant.outOfFunction"]
        );
        assert_eq!(
            codes("<?php echo __METHOD__;", run_magic_constant_context),
            ["magicConstant.outOfFunction"]
        );
    }

    #[test]
    fn function_magic_inside_function_is_ok() {
        assert!(codes(
            "<?php function f() { return __FUNCTION__; }",
            run_magic_constant_context
        )
        .is_empty());
        // Closures and arrow functions count as functions.
        assert!(codes(
            "<?php $f = function () { return __FUNCTION__; };",
            run_magic_constant_context
        )
        .is_empty());
        assert!(codes(
            "<?php $f = fn() => __FUNCTION__;",
            run_magic_constant_context
        )
        .is_empty());
    }

    #[test]
    fn namespace_magic_in_global_is_flagged() {
        assert_eq!(
            codes("<?php echo __NAMESPACE__;", run_magic_constant_context),
            ["magicConstant.outOfNamespace"]
        );
    }

    #[test]
    fn namespace_magic_in_namespace_is_ok() {
        let src = "<?php namespace App; echo __NAMESPACE__;";
        assert!(codes(src, run_magic_constant_context).is_empty());
    }

    #[test]
    fn line_and_file_magic_never_flagged() {
        // __LINE__/__FILE__/__DIR__ are always meaningful — never flagged.
        assert!(codes(
            "<?php echo __LINE__, __FILE__, __DIR__;",
            run_magic_constant_context
        )
        .is_empty());
    }

    // --- OverridingConstantRule ----------------------------------------------

    #[test]
    fn override_final_constant_is_flagged() {
        let src = "<?php class A { final const X = 1; } class B extends A { const X = 2; }";
        assert_eq!(codes(src, run_overriding_constant), ["classConstant.final"]);
    }

    #[test]
    fn override_nonfinal_constant_is_ok() {
        let src = "<?php class A { const X = 1; } class B extends A { const X = 2; }";
        assert!(codes(src, run_overriding_constant).is_empty());
    }

    #[test]
    fn narrowing_public_to_private_is_flagged() {
        let src =
            "<?php class A { public const X = 1; } class B extends A { private const X = 2; }";
        assert_eq!(
            codes(src, run_overriding_constant),
            ["classConstant.visibility"]
        );
    }

    #[test]
    fn narrowing_protected_to_private_is_flagged() {
        let src =
            "<?php class A { protected const X = 1; } class B extends A { private const X = 2; }";
        assert_eq!(
            codes(src, run_overriding_constant),
            ["classConstant.visibility"]
        );
    }

    #[test]
    fn widening_visibility_is_ok() {
        let src =
            "<?php class A { protected const X = 1; } class B extends A { public const X = 2; }";
        assert!(codes(src, run_overriding_constant).is_empty());
    }

    #[test]
    fn override_private_parent_constant_is_ok() {
        // A private parent constant is not inherited → no override relation.
        let src =
            "<?php class A { private const X = 1; } class B extends A { private const X = 2; }";
        assert!(codes(src, run_overriding_constant).is_empty());
    }

    #[test]
    fn override_interface_final_constant_is_flagged() {
        let src = "<?php interface I { final const X = 1; } class C implements I { const X = 2; }";
        assert_eq!(codes(src, run_overriding_constant), ["classConstant.final"]);
    }

    #[test]
    fn unknown_parent_is_not_flagged() {
        // Parent class is not indexed → cannot prove an override; skip.
        let src = "<?php class B extends \\Vendor\\Unknown { const X = 2; }";
        assert!(codes(src, run_overriding_constant).is_empty());
    }

    // --- DynamicClassConstantFetchRule ---------------------------------------

    #[test]
    fn dynamic_fetch_with_array_name_is_flagged() {
        let src = "<?php $a = [1]; echo Foo::{$a};";
        assert_eq!(
            codes(src, run_dynamic_class_constant_fetch),
            ["classConstant.nameType"]
        );
    }

    #[test]
    fn dynamic_fetch_with_string_name_is_ok() {
        let src = "<?php $a = 'X'; echo Foo::{$a};";
        assert!(codes(src, run_dynamic_class_constant_fetch).is_empty());
    }

    #[test]
    fn dynamic_fetch_with_unknown_name_is_ok() {
        let src = "<?php function f($a) { echo Foo::{$a}; }";
        assert!(codes(src, run_dynamic_class_constant_fetch).is_empty());
    }

    #[test]
    fn static_constant_fetch_is_not_flagged() {
        let src = "<?php echo Foo::BAR;";
        assert!(codes(src, run_dynamic_class_constant_fetch).is_empty());
    }

    // --- ValueAssignedToClassConstantRule ------------------------------------

    #[test]
    fn native_typed_constant_bad_value_is_flagged() {
        let src = "<?php class A { const int X = 'bad'; }";
        assert_eq!(
            codes(src, run_value_assigned_to_class_constant),
            ["classConstant.value"]
        );
    }

    #[test]
    fn native_typed_constant_good_value_is_ok() {
        let src = "<?php class A { const int X = 5; const string Y = 'hi'; }";
        assert!(codes(src, run_value_assigned_to_class_constant).is_empty());
    }

    #[test]
    fn untyped_constant_is_not_checked() {
        let src = "<?php class A { const X = 'whatever'; }";
        assert!(codes(src, run_value_assigned_to_class_constant).is_empty());
    }

    #[test]
    fn native_typed_constant_int_to_float_is_ok() {
        // int → float widening is allowed.
        let src = "<?php class A { const float X = 5; }";
        assert!(codes(src, run_value_assigned_to_class_constant).is_empty());
    }
}
