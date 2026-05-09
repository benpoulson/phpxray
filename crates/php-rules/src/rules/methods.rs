//! phpstan category **Methods** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Methods/`. Checklist: docs/phpstan-rules.md.
//!
//! These rules reason about method *declarations* and method *calls*. The
//! declaration rules walk every class-like in the file together with its
//! resolved [`Scope`] (via [`php_resolve::for_each_region`]) so `self`/`parent`/
//! `static`/`$this` resolve to the enclosing class's FQN and inherited members
//! can be looked up through [`ReflectionIndex`].
//!
//! Implemented (faithful identifiers + wording):
//! - `method.abstract` (`AbstractMethodInNonAbstractClassRule`, level 0) — an
//!   abstract method declared in a non-abstract class/enum.
//! - `method.abstractPrivate` (`AbstractPrivateMethodRule`, level 0) — a private
//!   method declared abstract (in an abstract class / interface).
//! - `method.nonAbstract` (level 0) — an abstract method that nonetheless has a
//!   body, or a concrete method declared without one (PHP compile errors).
//! - `method.finalPrivate` (`FinalPrivateMethodRule`, level 0) — a `final
//!   private` method (never overridable).
//! - `method.visibility` (`MethodVisibilityInInterfaceRule`, level 0) — a
//!   non-public method in an interface.
//! - `constructor.returnType` (`ConstructorReturnTypeRule`, level 0) — a
//!   constructor with a return type.
//! - `method.staticConstructor` (level 0) — a `static` constructor in a
//!   non-interface (PHP rejects it at compile time).
//! - `method.duplicateParameter` (level 0) — two parameters with the same name.
//! - `method.missingImplementation` (`MissingMethodImplementationRule`, level 0)
//!   — a non-abstract class inheriting an abstract method it doesn't implement.
//! - `class.serializable` (`MissingMagicSerializationMethodsRule`, level 0) — a
//!   non-abstract class implementing `Serializable` without `__serialize`/
//!   `__unserialize`.
//! - `method.attributeTarget` (`MethodAttributesRule`, level 0, partial) — a
//!   class-only core attribute applied to a method.
//! - `OverridingMethodRule` (level 0) — `method.parentMethodFinal` (overriding a
//!   `final` parent), `method.nonStatic`/`method.static` (static-ness flip), and
//!   `method.visibility` (narrowing a parent method's visibility).
//! - `CallMethodsRule` / `CallStaticMethodsRule` existence + arity (level 0) —
//!   `method.notFound`/`staticMethod.notFound`, `parameter.notOptional` (too few
//!   required args), `argument.unknown` (too many positional args). Argument
//!   *types* are NOT checked here.
//! - `missingType.return` (`MissingMethodReturnTypehintRule`, level 6) — a method
//!   with no native/PHPDoc return type.
//! - `missingType.parameter` (`MissingMethodParameterTypehintRule`, level 6) — a
//!   method parameter with no type.
//! - `method.notFound` on a typed receiver (`CallMethodsRule`, level 0) —
//!   `$expr->m()` where `$expr`'s inferred type resolves to a known class with no
//!   such method (and no `__call`). Visibility (`method.private`/`.protected`) on a
//!   typed receiver is deferred: it needs the calling class context to avoid false
//!   positives on legal same-class cross-instance access.
//! - `nullsafe.neverNull` (`NullsafeMethodCallRule`, level 4) — a `?->` method call
//!   on a receiver that can never be null.
//! - `new.resultUnused` (`CallToConstructorStatementWithoutSideEffectsRule`, level
//!   4) — `new C();` as a statement whose constructor has no side effects.
//! - `staticClassAccess.privateMethod` (`CallPrivateMethodThroughStaticRule`, level
//!   2) — `static::m()` calling a private method (unsafe on non-final classes).
//! - `consistentConstructor.private` (`ConsistentConstructorDeclarationRule`, level
//!   0) — a private `__construct` in a class marked `@phpstan-consistent-constructor`.
//!
//! DEFERRED (need expression-type inference, not just the AST + reflection):
//! - `CallMethodsRule` argument *type* matching beyond positional, named-argument
//!   resolution, `MethodCallableRule`/`StaticMethodCallableRule` (`callable.notSupported`
//!   never fires on PHP 8.1+ — the only condition our target version triggers),
//!   `IncompatibleDefaultParameterTypeRule`, `MethodSignatureRule` param/return
//!   covariance, `Call*MethodStatementWithNoDiscardRule` (needs `#[NoDiscard]`/void-cast
//!   reflection), `ExistingClassesInTypehintsRule` (overlaps class-existence rules),
//!   `MissingMethodSelfOutTypeRule`, `MethodCallWithPossiblyRenamedNamedArgumentRule`,
//!   `ConsistentConstructorRule` (param/visibility comparison vs parent constructor —
//!   the `consistentConstructor` *attribute* requires a custom PHPDoc tag we don't model).

use crate::{FileAnalysis, RuleEntry};
use php_ast::{
    ClassDecl, ClassKind, Expr, ExprKind, Member, MemberName, MethodDecl, Stmt, StmtKind, Visibility,
};
use php_diagnostics::Diagnostic;
use php_intern::Interner;
use php_reflect::{ClassReflection, Found, MethodReflection, ReflectionIndex};
use php_resolve::{for_each_region, Resolution, Scope};
use php_span::Span;
use php_types::Type;
use std::collections::HashSet;

// ---------------------------------------------------------------------------
// shared traversal: every class-like with its FQN + declaring scope
// ---------------------------------------------------------------------------

/// Visit every class-like declaration in the file, paired with its resolved FQN
/// and the [`Scope`] of its namespace region. Descends into nested declarations
/// (blocks, control flow) so conditionally-declared classes are covered.
fn for_each_class(fa: &FileAnalysis, mut f: impl FnMut(&Scope, &str, &ClassDecl)) {
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            walk_class_stmt(st, scope, fa.interner, &mut f);
        }
    });
}

fn walk_class_stmt(
    st: &Stmt,
    scope: &Scope,
    interner: &Interner,
    f: &mut impl FnMut(&Scope, &str, &ClassDecl),
) {
    match &st.kind {
        StmtKind::Class(c) => {
            if let Some(name) = c.name {
                let fqn = scope.qualify(interner.resolve(name));
                f(scope, &fqn, c);
            }
        }
        StmtKind::Block(b) => b.iter().for_each(|s| walk_class_stmt(s, scope, interner, f)),
        StmtKind::If { then, elseifs, els, .. } => {
            walk_class_stmt(then, scope, interner, f);
            for e in elseifs {
                walk_class_stmt(&e.body, scope, interner, f);
            }
            if let Some(e) = els {
                walk_class_stmt(e, scope, interner, f);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => walk_class_stmt(body, scope, interner, f),
        StmtKind::Try { body, catches, finally } => {
            body.iter().for_each(|s| walk_class_stmt(s, scope, interner, f));
            for c in catches {
                c.body.iter().for_each(|s| walk_class_stmt(s, scope, interner, f));
            }
            if let Some(fin) = finally {
                fin.iter().for_each(|s| walk_class_stmt(s, scope, interner, f));
            }
        }
        StmtKind::Switch { cases, .. } => {
            for case in cases {
                case.body.iter().for_each(|s| walk_class_stmt(s, scope, interner, f));
            }
        }
        StmtKind::Declare { body: Some(b), .. } => walk_class_stmt(b, scope, interner, f),
        _ => {}
    }
}

/// Iterate the real methods of a class.
fn methods(c: &ClassDecl) -> impl Iterator<Item = &MethodDecl> {
    c.members.iter().filter_map(|m| match m {
        Member::Method(md) => Some(md),
        _ => None,
    })
}

fn vis(m: &MethodDecl) -> Visibility {
    m.modifiers.visibility.unwrap_or(Visibility::Public)
}

fn is_ctor(fa: &FileAnalysis, m: &MethodDecl) -> bool {
    fa.interner.resolve(m.name).eq_ignore_ascii_case("__construct")
}

/// The display name of a class (its name as written, leading `\` stripped).
fn display(fa: &FileAnalysis, c: &ClassDecl) -> String {
    c.name
        .map(|n| fa.interner.resolve(n).to_string())
        .unwrap_or_else(|| "class@anonymous".to_string())
}

/// A best-effort span for a method-level diagnostic. Our AST does not record a
/// span on [`MethodDecl`] itself, so we point at the first available child span:
/// a parameter type, a parameter default, the return type, the first body
/// statement, an attribute argument — else a zero span.
fn method_span(m: &MethodDecl) -> Span {
    for p in &m.params {
        if let Some(t) = &p.ty {
            return t.span;
        }
        if let Some(d) = &p.default {
            return d.span;
        }
    }
    if let Some(t) = &m.return_type {
        return t.span;
    }
    if let Some(body) = &m.body {
        if let Some(first) = body.first() {
            return first.span;
        }
    }
    if let Some(a) = m.attrs.first().and_then(|g| g.attrs.first()) {
        return a.name.span;
    }
    Span::new(0, 0)
}

/// A best-effort span for a class-level diagnostic: the first member's span, else
/// a parent/interface reference, else a zero span (no class-name span in the AST).
fn class_span(c: &ClassDecl) -> Span {
    c.members
        .iter()
        .find_map(|m| match m {
            Member::Method(md) => Some(method_span(md)),
            Member::Property(pd) => pd.ty.as_ref().map(|t| t.span),
            _ => None,
        })
        .or_else(|| c.extends.first().map(|n| n.span))
        .or_else(|| c.implements.first().map(|n| n.span))
        .or_else(|| c.backing.as_ref().map(|t| t.span))
        .unwrap_or(Span::new(0, 0))
}

// ---------------------------------------------------------------------------
// declaration rules
// ---------------------------------------------------------------------------

/// `AbstractMethodInNonAbstractClassRule` — an abstract method in a class/enum
/// that is not itself abstract.
fn run_abstract_in_non_abstract(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, _, c| {
        // Interfaces and traits legitimately hold abstract methods.
        if matches!(c.kind, ClassKind::Interface | ClassKind::Trait) || c.modifiers.is_abstract {
            return;
        }
        for m in methods(c) {
            if !m.modifiers.is_abstract {
                continue;
            }
            let mname = fa.interner.resolve(m.name);
            // Enums get implicit `cases`/`from`/`tryFrom`.
            if c.kind == ClassKind::Enum
                && matches!(mname.to_ascii_lowercase().as_str(), "cases" | "from" | "tryfrom")
            {
                continue;
            }
            let lead = if c.kind == ClassKind::Enum { "Enum" } else { "Non-abstract class" };
            out.push(
                Diagnostic::error(
                    method_span(m),
                    format!("{lead} {} contains abstract method {mname}().", display(fa, c)),
                )
                .with_code("method.abstract"),
            );
        }
    });
    out
}

/// `AbstractPrivateMethodRule` — a private abstract method (only meaningful in an
/// abstract class / interface; PHP rejects it).
fn run_abstract_private(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, _, c| {
        if c.kind == ClassKind::Trait {
            return;
        }
        // In a non-abstract class the abstract-in-non-abstract rule fires instead.
        if c.kind != ClassKind::Interface && !c.modifiers.is_abstract {
            return;
        }
        for m in methods(c) {
            if m.modifiers.is_abstract && vis(m) == Visibility::Private {
                out.push(
                    Diagnostic::error(
                        method_span(m),
                        format!(
                            "Private method {}::{}() cannot be abstract.",
                            display(fa, c),
                            fa.interner.resolve(m.name)
                        ),
                    )
                    .with_code("method.abstractPrivate"),
                );
            }
        }
    });
    out
}

/// An abstract method that nonetheless has a body, or a concrete method missing a
/// body. Mirrors PHP's own compile error.
fn run_abstract_body(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, _, c| {
        for m in methods(c) {
            let name = fa.interner.resolve(m.name);
            if m.modifiers.is_abstract && m.body.is_some() {
                out.push(
                    Diagnostic::error(
                        method_span(m),
                        format!("Abstract method {}::{}() cannot contain body.", display(fa, c), name),
                    )
                    .with_code("method.nonAbstract"),
                );
            } else if !m.modifiers.is_abstract && m.body.is_none() && c.kind != ClassKind::Interface {
                out.push(
                    Diagnostic::error(
                        method_span(m),
                        format!("Non-abstract method {}::{}() must contain body.", display(fa, c), name),
                    )
                    .with_code("method.nonAbstract"),
                );
            }
        }
    });
    out
}

/// `FinalPrivateMethodRule` — a `final private` method can never be overridden.
fn run_final_private(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, _, c| {
        for m in methods(c) {
            if is_ctor(fa, m) {
                continue;
            }
            if m.modifiers.is_final && vis(m) == Visibility::Private {
                out.push(
                    Diagnostic::error(
                        method_span(m),
                        format!(
                            "Private method {}::{}() cannot be final as it is never overridden by other classes.",
                            display(fa, c),
                            fa.interner.resolve(m.name)
                        ),
                    )
                    .with_code("method.finalPrivate"),
                );
            }
        }
    });
    out
}

/// `MethodVisibilityInInterfaceRule` — interface methods must be public.
fn run_visibility_in_interface(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, _, c| {
        if c.kind != ClassKind::Interface {
            return;
        }
        for m in methods(c) {
            if vis(m) != Visibility::Public {
                out.push(
                    Diagnostic::error(
                        method_span(m),
                        format!(
                            "Method {}::{}() cannot use non-public visibility in interface.",
                            display(fa, c),
                            fa.interner.resolve(m.name)
                        ),
                    )
                    .with_code("method.visibility"),
                );
            }
        }
    });
    out
}

/// `ConstructorReturnTypeRule` — a constructor may not declare a return type.
fn run_constructor_return_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, _, c| {
        for m in methods(c) {
            if is_ctor(fa, m) && m.return_type.is_some() {
                out.push(
                    Diagnostic::error(
                        method_span(m),
                        format!("Constructor of class {} has a return type.", display(fa, c)),
                    )
                    .with_code("constructor.returnType"),
                );
            }
        }
    });
    out
}

/// A `static` constructor in a non-interface — PHP rejects it.
fn run_constructor_modifiers(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, _, c| {
        if c.kind == ClassKind::Interface {
            return;
        }
        for m in methods(c) {
            if is_ctor(fa, m) && m.modifiers.is_static {
                out.push(
                    Diagnostic::error(
                        method_span(m),
                        format!("Constructor {}::__construct() cannot be static.", display(fa, c)),
                    )
                    .with_code("method.staticConstructor"),
                );
            }
        }
    });
    out
}

/// Two parameters of one method sharing a name (a fatal redeclare in PHP).
fn run_duplicate_parameter(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, _, c| {
        for m in methods(c) {
            let mut seen: HashSet<&str> = HashSet::new();
            for p in &m.params {
                let pn = fa.interner.resolve(p.name);
                if !seen.insert(pn) {
                    out.push(
                        Diagnostic::error(
                            method_span(m),
                            format!(
                                "Redefinition of parameter ${pn} in method {}::{}().",
                                display(fa, c),
                                fa.interner.resolve(m.name)
                            ),
                        )
                        .with_code("method.duplicateParameter"),
                    );
                }
            }
        }
    });
    out
}

/// `MissingMethodImplementationRule` — a non-abstract class that inherits an
/// abstract method (from an abstract parent or interface) it never implements.
fn run_missing_implementation(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, fqn, c| {
        if matches!(c.kind, ClassKind::Interface | ClassKind::Trait) || c.modifiers.is_abstract {
            return;
        }
        for (mname, declaring) in collect_unimplemented_abstracts(fa.reflection, fqn) {
            let lead = if c.kind == ClassKind::Enum { "Enum" } else { "Non-abstract class" };
            out.push(
                Diagnostic::error(
                    class_span(c),
                    format!(
                        "{lead} {} contains abstract method {mname}() from {declaring}.",
                        display(fa, c)
                    ),
                )
                .with_code("method.missingImplementation"),
            );
        }
    });
    out
}

/// `(method_name, "<kind> <declaring fqn>")` for every abstract method reachable
/// from `fqn` that has no concrete override. Only reported when the class is known
/// in the reflection index (so unresolved hierarchies don't yield false positives).
fn collect_unimplemented_abstracts(refl: &ReflectionIndex, fqn: &str) -> Vec<(String, String)> {
    if refl.class(fqn).is_none() {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    // Examine every method name in scope (own + inherited) once.
    let mut names: Vec<String> = Vec::new();
    collect_method_names(refl, fqn, &mut Vec::new(), &mut names);
    for name in names {
        let key = name.to_ascii_lowercase();
        if !seen.insert(key) {
            continue;
        }
        if let Some(found) = refl.find_method(fqn, &name) {
            if found.member.is_abstract && !found.member.magic {
                let declaring = describe_declarer(refl, &found.declaring_class);
                out.push((found.member.name.clone(), declaring));
            }
        }
    }
    out
}

/// Gather every method name declared anywhere in `fqn`'s hierarchy.
fn collect_method_names(refl: &ReflectionIndex, fqn: &str, visited: &mut Vec<String>, out: &mut Vec<String>) {
    let key = fqn.trim_start_matches('\\').to_ascii_lowercase();
    if visited.contains(&key) {
        return;
    }
    visited.push(key);
    let Some(class) = refl.class(fqn) else { return };
    for m in &class.methods {
        if !m.magic {
            out.push(m.name.clone());
        }
    }
    for parent in class.parents.iter().chain(&class.interfaces).chain(&class.traits) {
        if let Type::Named { fqn: pf, .. } = parent {
            collect_method_names(refl, pf, visited, out);
        }
    }
}

fn describe_declarer(refl: &ReflectionIndex, fqn: &str) -> String {
    let kind = match refl.class(fqn).map(|c| c.kind) {
        Some(ClassKind::Interface) => "interface",
        _ => "class",
    };
    format!("{kind} {}", fqn.trim_start_matches('\\'))
}

/// `MissingMagicSerializationMethodsRule` — a concrete class implementing
/// `Serializable` must define `__serialize` and `__unserialize`.
fn run_serializable_methods(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |scope, fqn, c| {
        if c.kind != ClassKind::Class || c.modifiers.is_abstract {
            return;
        }
        let implements_serializable = c.implements.iter().any(|n| {
            scope
                .resolve_class(n)
                .fqn()
                .map(|f| f.trim_start_matches('\\').eq_ignore_ascii_case("Serializable"))
                .unwrap_or(false)
        }) || fa.reflection.is_subclass_of(fqn, "Serializable");
        if !implements_serializable {
            return;
        }
        let missing = |name: &str| fa.reflection.find_method(fqn, name).is_none();
        if missing("__serialize") {
            out.push(serializable_diag(fa, c, "__serialize"));
        }
        if missing("__unserialize") {
            out.push(serializable_diag(fa, c, "__unserialize"));
        }
    });
    out
}

fn serializable_diag(fa: &FileAnalysis, c: &ClassDecl, method: &str) -> Diagnostic {
    Diagnostic::error(
        class_span(c),
        format!(
            "Non-abstract class {} implements the Serializable interface, but does not implement {method}().",
            display(fa, c)
        ),
    )
    .with_code("class.serializable")
}

/// `MethodAttributesRule` (partial) — a class-only core attribute applied to a
/// method. Full validation needs the attribute class's `#[Attribute(...)]` target
/// flags; here we cover the well-known class-only built-ins.
fn run_method_attribute_target(fa: &FileAnalysis) -> Vec<Diagnostic> {
    // Core attributes whose target is class-only (cannot annotate a method).
    const CLASS_ONLY: &[&str] = &["AllowDynamicProperties", "Attribute"];
    let mut out = Vec::new();
    for_each_class(fa, |scope, _, c| {
        for m in methods(c) {
            for group in &m.attrs {
                for attr in &group.attrs {
                    let Some(fqn) = scope.resolve_class(&attr.name).fqn().map(str::to_string) else {
                        continue;
                    };
                    let short = fqn.trim_start_matches('\\');
                    if CLASS_ONLY.iter().any(|a| short.eq_ignore_ascii_case(a)) {
                        out.push(
                            Diagnostic::error(
                                attr.name.span,
                                format!("Attribute class {short} does not have the method target."),
                            )
                            .with_code("method.attributeTarget"),
                        );
                    }
                }
            }
        }
    });
    out
}

/// `OverridingMethodRule` (the parts expressible from reflection) — for each
/// method overriding a parent method: flag static-ness flips, overriding a
/// `final` parent method, and narrowing visibility.
fn run_overriding_method(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, fqn, c| {
        let Some(class) = fa.reflection.class(fqn) else { return };
        for m in &class.methods {
            if m.magic {
                continue;
            }
            let Some(parent) = find_parent_method(fa.reflection, class, &m.name) else { continue };
            let pm = &parent.member;
            let here = display(fa, c);
            let there = parent.declaring_class.trim_start_matches('\\');
            let mname = &m.name;

            if pm.is_final {
                out.push(
                    Diagnostic::error(
                        class_span(c),
                        format!("Method {here}::{mname}() overrides final method {there}::{mname}()."),
                    )
                    .with_code("method.parentMethodFinal"),
                );
            }
            if pm.is_static && !m.is_static {
                out.push(
                    Diagnostic::error(
                        class_span(c),
                        format!("Non-static method {here}::{mname}() overrides static method {there}::{mname}()."),
                    )
                    .with_code("method.nonStatic"),
                );
            } else if !pm.is_static && m.is_static {
                out.push(
                    Diagnostic::error(
                        class_span(c),
                        format!("Static method {here}::{mname}() overrides non-static method {there}::{mname}()."),
                    )
                    .with_code("method.static"),
                );
            }
            // Visibility must not be narrowed (private parent methods aren't
            // really overridden, so skip them).
            if pm.visibility != Visibility::Private && vis_rank(pm.visibility) > vis_rank(m.visibility) {
                let (lead, want) = match (pm.visibility, m.visibility) {
                    (Visibility::Public, Visibility::Private) => ("Private", "be public"),
                    (Visibility::Public, _) => ("Protected", "also be public"),
                    (_, Visibility::Private) => ("Private", "be protected or public"),
                    _ => ("Protected", "also be public"),
                };
                let pvis = vis_word(pm.visibility);
                out.push(
                    Diagnostic::error(
                        class_span(c),
                        format!(
                            "{lead} method {here}::{mname}() overriding {pvis} method {there}::{mname}() should {want}."
                        ),
                    )
                    .with_code("method.visibility"),
                );
            }
        }
    });
    out
}

fn vis_rank(v: Visibility) -> u8 {
    match v {
        Visibility::Public => 3,
        Visibility::Protected => 2,
        Visibility::Private => 1,
    }
}

fn vis_word(v: Visibility) -> &'static str {
    match v {
        Visibility::Public => "public",
        Visibility::Protected => "protected",
        Visibility::Private => "private",
    }
}

/// Find the nearest non-magic method named `name` strictly above `class` in the
/// hierarchy (parents, then interfaces).
fn find_parent_method(refl: &ReflectionIndex, class: &ClassReflection, name: &str) -> Option<Found<MethodReflection>> {
    for parent in class.parents.iter().chain(&class.interfaces) {
        if let Type::Named { fqn: pf, .. } = parent {
            if let Some(found) = refl.find_method(pf, name) {
                if !found.member.magic {
                    return Some(found);
                }
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// missing-typehint rules (level 6)
// ---------------------------------------------------------------------------

/// `MissingMethodReturnTypehintRule` — a method with no return type at all.
fn run_missing_return_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, fqn, c| {
        let Some(class) = fa.reflection.class(fqn) else { return };
        for (md, _mr) in zip_methods(fa.interner, c, class) {
            // "Specified" = a native return type OR a `@return` tag in the method's
            // docblock. We key off the tag's *presence* (like phpstan), not the
            // resolved type — a `@return $this`/exotic type that resolves to `mixed`
            // still counts as documented.
            if md.return_type.is_some() || doc_has_return(md.doc.as_deref()) {
                continue;
            }
            let name = fa.interner.resolve(md.name);
            if name.eq_ignore_ascii_case("__construct") || name.eq_ignore_ascii_case("__destruct") {
                continue;
            }
            // An override inherits the prototype's return typehint.
            if inherited_return_typed(fa, class, name) {
                continue;
            }
            out.push(
                Diagnostic::error(
                    method_span(md),
                    format!("Method {}::{name}() has no return type specified.", display(fa, c)),
                )
                .with_code("missingType.return"),
            );
        }
    });
    out
}

/// Whether a docblock declares a `@return` (incl. `@phpstan-`/`@psalm-return`).
fn doc_has_return(doc: Option<&str>) -> bool {
    doc.is_some_and(|d| d.contains("@return") || d.contains("-return"))
}

/// Walk the transitive supertypes of `class` (parents, interfaces, traits — and
/// their supertypes), invoking `check` on each ancestor's *own* declaration of the
/// method `name`. Returns true as soon as `check` does. phpstan considers a method
/// "typed" if *any* prototype anywhere up the hierarchy supplies the type — e.g. an
/// interface's `@return` flows down through an abstract base to a concrete override.
fn hierarchy_method<F>(fa: &FileAnalysis, class: &php_reflect::ClassReflection, name: &str, mut check: F) -> bool
where
    F: FnMut(&MethodReflection) -> bool,
{
    let mut seen = std::collections::HashSet::new();
    let mut stack: Vec<String> = class
        .parents
        .iter()
        .chain(&class.interfaces)
        .chain(&class.traits)
        .filter_map(named_fqn)
        .collect();
    while let Some(fqn) = stack.pop() {
        if !seen.insert(fqn.clone()) {
            continue;
        }
        let Some(anc) = fa.reflection.class(&fqn) else { continue };
        if let Some(m) = anc.methods.iter().find(|m| !m.magic && m.name.eq_ignore_ascii_case(name)) {
            if check(m) {
                return true;
            }
        }
        stack.extend(anc.parents.iter().chain(&anc.interfaces).chain(&anc.traits).filter_map(named_fqn));
    }
    false
}

/// Whether an overridden prototype anywhere up the hierarchy declares a non-`mixed`
/// return type (native or `@return`). phpstan inherits it, so the override needn't repeat.
fn inherited_return_typed(fa: &FileAnalysis, class: &php_reflect::ClassReflection, name: &str) -> bool {
    hierarchy_method(fa, class, name, |m| m.explicit_return)
}

/// Whether an overridden prototype anywhere up the hierarchy types the parameter at `idx`.
fn inherited_param_typed(
    fa: &FileAnalysis,
    class: &php_reflect::ClassReflection,
    name: &str,
    idx: usize,
) -> bool {
    hierarchy_method(fa, class, name, |m| m.params.get(idx).is_some_and(|p| p.explicit))
}

/// Whether a docblock declares a `@param … $name` (any `@param*` prefix), with
/// `$name` matched as a whole variable token. Mirrors the function-rule helper.
fn doc_has_param(doc: Option<&str>, name: &str) -> bool {
    let Some(d) = doc else { return false };
    let needle = format!("${name}");
    let mut search = d;
    while let Some(off) = search.find("@param") {
        let after = &search[off + "@param".len()..];
        let seg = after.split('@').next().unwrap_or(after);
        if let Some(p) = seg.find(&needle) {
            let end = p + needle.len();
            let b = seg.as_bytes();
            if end >= b.len() || !(b[end].is_ascii_alphanumeric() || b[end] == b'_') {
                return true;
            }
        }
        search = after;
    }
    false
}

/// `MissingMethodParameterTypehintRule` — a method parameter with no type.
fn run_missing_param_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, fqn, c| {
        let Some(class) = fa.reflection.class(fqn) else { return };
        for (md, _mr) in zip_methods(fa.interner, c, class) {
            let mname = fa.interner.resolve(md.name);
            for (idx, p) in md.params.iter().enumerate() {
                if p.ty.is_some() {
                    continue; // native type hint present
                }
                let pname = fa.interner.resolve(p.name);
                if doc_has_param(md.doc.as_deref(), pname) {
                    continue; // documented via @param
                }
                if inherited_param_typed(fa, class, mname, idx) {
                    continue; // inherited from an overridden prototype
                }
                out.push(
                    Diagnostic::error(
                        method_span(md),
                        format!(
                            "Method {}::{}() has parameter ${} with no type specified.",
                            display(fa, c),
                            fa.interner.resolve(md.name),
                            pname
                        ),
                    )
                    .with_code("missingType.parameter"),
                );
            }
        }
    });
    out
}

/// Pair each AST method with its reflected counterpart, matched by name.
fn zip_methods<'a>(
    interner: &'a Interner,
    c: &'a ClassDecl,
    class: &'a ClassReflection,
) -> impl Iterator<Item = (&'a MethodDecl, &'a MethodReflection)> {
    methods(c).filter_map(move |md| {
        let name = interner.resolve(md.name);
        class
            .methods
            .iter()
            .find(|r| !r.magic && r.name.eq_ignore_ascii_case(name))
            .map(|r| (md, r))
    })
}

// ---------------------------------------------------------------------------
// call rules (existence + arity)
// ---------------------------------------------------------------------------

/// `CallMethodsRule` / `CallStaticMethodsRule` (existence + arity only) —
/// `$this->m()`, `self::m()`, `static::m()` where the receiver's class is known:
/// flag a missing method, too few required arguments, or too many positional
/// arguments. Argument *types* are deferred to the type system.
fn run_call_existence(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |scope, fqn, c| {
        for m in methods(c) {
            let Some(body) = &m.body else { continue };
            let mut exprs: Vec<&Expr> = Vec::new();
            for st in body {
                collect_exprs_in_stmt(st, &mut exprs);
            }
            for e in exprs {
                check_call_expr(e, fa, scope, fqn, &mut out);
            }
        }
    });
    out
}

fn check_call_expr(e: &Expr, fa: &FileAnalysis, scope: &Scope, self_fqn: &str, out: &mut Vec<Diagnostic>) {
    match &e.kind {
        ExprKind::MethodCall { recv, method, args, .. } => {
            // Only `$this->m(...)` — other receivers need type inference.
            if !is_this(recv, fa) {
                return;
            }
            if let MemberName::Ident(name) = method {
                // Spread/named args make arity opaque — skip arity but still check existence.
                let opaque = args.iter().any(|a| a.spread || a.name.is_some() || a.placeholder);
                check_member_call(e, fa, self_fqn, fa.interner.resolve(*name), args.len(), opaque, false, out);
            }
        }
        ExprKind::StaticCall { class, method, args } => {
            let Some(target) = static_target_fqn(class, scope, self_fqn) else { return };
            if let MemberName::Ident(name) = method {
                let opaque = args.iter().any(|a| a.spread || a.name.is_some() || a.placeholder);
                check_member_call(e, fa, &target, fa.interner.resolve(*name), args.len(), opaque, true, out);
            }
        }
        _ => {}
    }
}

/// Whether an expression is `$this`.
fn is_this(e: &Expr, fa: &FileAnalysis) -> bool {
    matches!(&e.kind, ExprKind::Variable(s) if fa.interner.resolve(*s) == "this")
}

/// Resolve a static-call class operand to an FQN if it names `self`/`static`
/// (resolved against the enclosing class). `parent` is skipped (we don't have the
/// parent FQN directly here); fully-qualified names resolve normally.
fn static_target_fqn(class: &Expr, scope: &Scope, self_fqn: &str) -> Option<String> {
    let ExprKind::Name(n) = &class.kind else { return None };
    match scope.resolve_class(n) {
        Resolution::LateStatic(which) => match which.as_str() {
            "self" | "static" => Some(self_fqn.to_string()),
            _ => None,
        },
        r => r.fqn().map(str::to_string),
    }
}

#[allow(clippy::too_many_arguments)]
fn check_member_call(
    call: &Expr,
    fa: &FileAnalysis,
    class_fqn: &str,
    method: &str,
    arg_count: usize,
    arity_opaque: bool,
    is_static: bool,
    out: &mut Vec<Diagnostic>,
) {
    // The class must be known, else we can't judge.
    if fa.reflection.class(class_fqn).is_none() {
        return;
    }
    let Some(found) = fa.reflection.find_method(class_fqn, method) else {
        // A class with __call / __callStatic accepts any method name.
        let magic = if is_static { "__callStatic" } else { "__call" };
        if fa.reflection.find_method(class_fqn, magic).is_some() {
            return;
        }
        let short = class_fqn.trim_start_matches('\\');
        let code = if is_static { "staticMethod.notFound" } else { "method.notFound" };
        out.push(
            Diagnostic::error(call.span, format!("Call to an undefined method {short}::{method}()."))
                .with_code(code),
        );
        return;
    };
    let mr = &found.member;
    if mr.magic || arity_opaque {
        return;
    }
    let required = mr.params.iter().filter(|p| !p.optional && !p.variadic).count();
    let variadic = mr.params.iter().any(|p| p.variadic);
    let max = mr.params.len();
    let here = found.declaring_class.trim_start_matches('\\');
    if arg_count < required {
        out.push(
            Diagnostic::error(
                call.span,
                format!(
                    "Method {here}::{method}() invoked with {arg_count} parameter{}, {required} required.",
                    plural(arg_count)
                ),
            )
            .with_code("parameter.notOptional"),
        );
    } else if !variadic && arg_count > max {
        out.push(
            Diagnostic::error(
                call.span,
                format!(
                    "Method {here}::{method}() invoked with {arg_count} parameter{}, {}.",
                    plural(arg_count),
                    arity_phrase(required, max)
                ),
            )
            .with_code("argument.unknown"),
        );
    }
}

fn plural(n: usize) -> &'static str {
    if n == 1 {
        ""
    } else {
        "s"
    }
}

fn arity_phrase(required: usize, max: usize) -> String {
    if required == max {
        format!("{max} expected")
    } else {
        format!("{required}-{max} expected")
    }
}

/// Collect every expression contained in a single method-body statement, NOT
/// crossing into nested class declarations.
fn collect_exprs_in_stmt<'a>(st: &'a Stmt, out: &mut Vec<&'a Expr>) {
    match &st.kind {
        StmtKind::Expr(e) | StmtKind::Return(Some(e)) => collect_expr(e, out),
        StmtKind::Echo(es) | StmtKind::Global(es) | StmtKind::Unset(es) => {
            es.iter().for_each(|e| collect_expr(e, out))
        }
        StmtKind::Block(b) => b.iter().for_each(|s| collect_exprs_in_stmt(s, out)),
        StmtKind::If { cond, then, elseifs, els } => {
            collect_expr(cond, out);
            collect_exprs_in_stmt(then, out);
            for ei in elseifs {
                collect_expr(&ei.cond, out);
                collect_exprs_in_stmt(&ei.body, out);
            }
            if let Some(e) = els {
                collect_exprs_in_stmt(e, out);
            }
        }
        StmtKind::While { cond, body } => {
            collect_expr(cond, out);
            collect_exprs_in_stmt(body, out);
        }
        StmtKind::DoWhile { body, cond } => {
            collect_exprs_in_stmt(body, out);
            collect_expr(cond, out);
        }
        StmtKind::For { init, cond, update, body } => {
            for e in init.iter().chain(cond).chain(update) {
                collect_expr(e, out);
            }
            collect_exprs_in_stmt(body, out);
        }
        StmtKind::Foreach { subject, key, value, body, .. } => {
            collect_expr(subject, out);
            if let Some(k) = key {
                collect_expr(k, out);
            }
            collect_expr(value, out);
            collect_exprs_in_stmt(body, out);
        }
        StmtKind::Switch { subject, cases } => {
            collect_expr(subject, out);
            for cs in cases {
                if let Some(t) = &cs.test {
                    collect_expr(t, out);
                }
                cs.body.iter().for_each(|s| collect_exprs_in_stmt(s, out));
            }
        }
        StmtKind::Try { body, catches, finally } => {
            body.iter().for_each(|s| collect_exprs_in_stmt(s, out));
            for cc in catches {
                cc.body.iter().for_each(|s| collect_exprs_in_stmt(s, out));
            }
            if let Some(f) = finally {
                f.iter().for_each(|s| collect_exprs_in_stmt(s, out));
            }
        }
        StmtKind::Declare { directives, body } => {
            for (_, e) in directives {
                collect_expr(e, out);
            }
            if let Some(b) = body {
                collect_exprs_in_stmt(b, out);
            }
        }
        _ => {}
    }
}

/// Recursively collect sub-expressions of `e` (pre-order), but DO NOT descend
/// into nested closures/arrow-fns/anon-classes (they rebind `$this`).
fn collect_expr<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    out.push(e);
    use ExprKind::*;
    match &e.kind {
        Interpolated(parts) | ShellExec(parts) | Isset(parts) => {
            parts.iter().for_each(|p| collect_expr(p, out))
        }
        VariableVariable(x) | DollarBrace(x) => collect_expr(x, out),
        Array { items, .. } => {
            for it in items {
                if let Some(k) = &it.key {
                    collect_expr(k, out);
                }
                if let Some(v) = &it.value {
                    collect_expr(v, out);
                }
            }
        }
        Call { callee, args } => {
            collect_expr(callee, out);
            args.iter().for_each(|a| collect_expr(&a.value, out));
        }
        MethodCall { recv, args, .. } => {
            collect_expr(recv, out);
            args.iter().for_each(|a| collect_expr(&a.value, out));
        }
        StaticCall { class, args, .. } => {
            collect_expr(class, out);
            args.iter().for_each(|a| collect_expr(&a.value, out));
        }
        New { class, args } => {
            collect_expr(class, out);
            args.iter().for_each(|a| collect_expr(&a.value, out));
        }
        Index { base, index } => {
            collect_expr(base, out);
            if let Some(i) = index {
                collect_expr(i, out);
            }
        }
        Prop { base, .. } => collect_expr(base, out),
        StaticProp { class, .. } | ClassConst { class, .. } => collect_expr(class, out),
        Unary { expr, .. } | Cast { expr, .. } => collect_expr(expr, out),
        Binary { lhs, rhs, .. }
        | Assign { target: lhs, rhs }
        | AssignOp { target: lhs, rhs, .. }
        | AssignRef { target: lhs, rhs }
        | Coalesce { lhs, rhs } => {
            collect_expr(lhs, out);
            collect_expr(rhs, out);
        }
        Ternary { cond, then, els } => {
            collect_expr(cond, out);
            if let Some(t) = then {
                collect_expr(t, out);
            }
            collect_expr(els, out);
        }
        PreInc(x) | PreDec(x) | PostInc(x) | PostDec(x) => collect_expr(x, out),
        Instanceof { expr, class } => {
            collect_expr(expr, out);
            collect_expr(class, out);
        }
        Clone(x) | Print(x) | Throw(x) | ErrorSuppress(x) | YieldFrom(x) | Eval(x) | Empty(x) => {
            collect_expr(x, out)
        }
        Yield { key, value } => {
            if let Some(k) = key {
                collect_expr(k, out);
            }
            if let Some(v) = value {
                collect_expr(v, out);
            }
        }
        Exit(Some(x)) => collect_expr(x, out),
        Match { subject, arms } => {
            collect_expr(subject, out);
            for arm in arms {
                if let Some(conds) = &arm.conds {
                    conds.iter().for_each(|c| collect_expr(c, out));
                }
                collect_expr(&arm.body, out);
            }
        }
        Include { expr, .. } => collect_expr(expr, out),
        Paren(x) => collect_expr(x, out),
        // Do not descend into Closure / ArrowFn / NewAnon: different `$this`.
        _ => {}
    }
}

/// Argument-**type** checking for instance method calls, using the type map.
/// `$recv->m($arg)` — when the receiver's type resolves to a known class, each
/// positional argument is checked against the method parameter's type. Static
/// calls (`self::`/`static::`/`Foo::`) need scope-aware class resolution and are
/// deferred. Lenient: unknown receiver/arg/param types produce no diagnostic.
fn run_method_argument_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::MethodCall { recv, method, args, .. } = &e.kind else { return };
        let MemberName::Ident(name) = method else { return };
        if args.iter().any(|a| a.spread || a.name.is_some() || a.placeholder) {
            return;
        }
        let Some(fqn) = named_fqn(&fa.type_of(recv)) else { return };
        let mname = fa.interner.resolve(*name);
        let Some(found) = fa.reflection.find_method(&fqn, mname) else { return };
        let mr = &found.member;
        if mr.magic {
            return;
        }
        let short = fqn.trim_start_matches('\\');
        for (i, arg) in args.iter().enumerate() {
            let Some(param) = mr.params.get(i) else { break };
            if param.variadic {
                break;
            }
            let given = fa.type_of(&arg.value);
            if !fa.accepts(&arg.value, &param.ty, &param.native_ty) {
                out.push(
                    Diagnostic::error(
                        arg.value.span,
                        format!(
                            "Parameter #{} ${} of method {short}::{mname}() expects {}, {given} given.",
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

/// The class FQN named by a type (through nullability), if any.
fn named_fqn(t: &Type) -> Option<String> {
    match t {
        Type::Named { fqn, .. } => Some(fqn.clone()),
        Type::Nullable(inner) => named_fqn(inner),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// CallMethodsRule — existence + visibility on a typed receiver (`$expr->m()`)
// ---------------------------------------------------------------------------

/// `CallMethodsRule` (the existence part expressible from the type map) — an
/// instance method call `$expr->m(...)` on a non-`$this` receiver whose inferred
/// type resolves to a *known* class with no method `m` and no `__call`
/// (`method.notFound`). `$this` receivers are handled by `run_call_existence`
/// (which has the self-class context), so they're skipped here to avoid duplicate
/// diagnostics. Visibility checks are deferred (need the calling class context).
fn run_call_methods_typed(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::MethodCall { recv, method, .. } = &e.kind else { return };
        let MemberName::Ident(name) = method else { return };
        // `$this->m()` is handled by run_call_existence (with self-class context).
        if is_this(recv, fa) {
            return;
        }
        let Some(fqn) = named_fqn(&fa.type_of(recv)) else { return };
        // The class must be known so absence/visibility is reliable.
        if !fa.class_fully_known(&fqn) {
            return;
        }
        let mname = fa.interner.resolve(*name);
        let short = fqn.trim_start_matches('\\');
        match fa.reflection.find_method(&fqn, mname) {
            None => {
                // __call accepts any method name.
                if fa.reflection.find_method(&fqn, "__call").is_some() {
                    return;
                }
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!("Call to an undefined method {short}::{mname}()."),
                    )
                    .with_code("method.notFound"),
                );
            }
            Some(_) => {
                // Visibility (`method.private`/`method.protected`) needs the
                // calling class context to avoid false positives on legal
                // same-class cross-instance access; deferred. Existence only here.
            }
        }
    });
    out
}

/// `CallStaticMethodsRule` (existence on an explicitly-named class) — a static
/// call `Foo::m(...)` inside a method body where `Foo` is a *known* class
/// (resolved through the namespace scope, not `self`/`static`/`parent`) with no
/// static method `m` and no `__callStatic` (`staticMethod.notFound`).
/// `self`/`static` calls are handled by `run_call_existence` with self-class
/// context, so they're skipped here.
fn run_static_call_named(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |scope, _, c| {
        for m in methods(c) {
            let Some(body) = &m.body else { continue };
            let mut exprs: Vec<&Expr> = Vec::new();
            for st in body {
                collect_exprs_in_stmt(st, &mut exprs);
            }
            for e in exprs {
                let ExprKind::StaticCall { class, method, .. } = &e.kind else { continue };
                let MemberName::Ident(name) = method else { continue };
                let ExprKind::Name(n) = &class.kind else { continue };
                // Only explicitly-named classes (skip self/static/parent/builtins).
                let fqn = match scope.resolve_class(n) {
                    Resolution::LateStatic(_) | Resolution::BuiltinType(_) => continue,
                    r => match r.fqn() {
                        Some(f) => f.trim_start_matches('\\').to_string(),
                        None => continue,
                    },
                };
                if !fa.class_fully_known(&fqn) {
                    continue;
                }
                let mname = fa.interner.resolve(*name);
                if fa.reflection.find_method(&fqn, mname).is_some()
                    || fa.reflection.find_method(&fqn, "__callStatic").is_some()
                {
                    continue;
                }
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!("Call to an undefined static method {fqn}::{mname}()."),
                    )
                    .with_code("staticMethod.notFound"),
                );
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// NullsafeMethodCallRule (level 4)
// ---------------------------------------------------------------------------

/// `NullsafeMethodCallRule` — a `?->` method call on a receiver whose inferred
/// type can never be null. Lenient: only fires when the receiver type is concrete
/// and provably non-nullable (not `mixed`/`unknown`/a union containing null).
fn run_nullsafe_never_null(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::MethodCall { recv, nullsafe: true, .. } = &e.kind else { return };
        let ty = fa.type_of(recv);
        if !type_is_definitely_non_null(&ty) {
            return;
        }
        out.push(
            Diagnostic::error(
                e.span,
                format!(
                    "Using nullsafe method call on non-nullable type {ty}. Use -> instead."
                ),
            )
            .with_code("nullsafe.neverNull"),
        );
    });
    out
}

/// Whether a type provably excludes `null` (and is concrete enough to judge).
/// `mixed`/`unknown`/`never`/`void`/template vars yield `false` (we stay silent).
fn type_is_definitely_non_null(t: &Type) -> bool {
    match t {
        Type::Mixed
        | Type::Unknown(_)
        | Type::Null
        | Type::Nullable(_)
        | Type::Never
        | Type::Void => false,
        Type::TemplateVar(_) => false,
        Type::Union(parts) => !parts.is_empty() && parts.iter().all(type_is_definitely_non_null),
        // A concrete object/scalar that is not nullable.
        Type::Named { .. }
        | Type::SelfType
        | Type::StaticType
        | Type::Parent
        | Type::Int
        | Type::Float
        | Type::String
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Array(_)
        | Type::List(_)
        | Type::Iterable(_)
        | Type::Callable(_)
        | Type::Object => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// CallToConstructorStatementWithoutSideEffectsRule (level 4)
// ---------------------------------------------------------------------------

/// `CallToConstructorStatementWithoutSideEffectsRule` — a `new C();` used as a
/// bare statement, where `C` is a known class with no constructor — the
/// instantiation result is discarded so the statement has no effect.
///
/// phpstan reports both the no-constructor and the side-effect-free-constructor
/// forms, but the latter relies on purity/`@phpstan-assert` reflection we don't
/// model. To keep zero false positives we only flag the **no-constructor** case,
/// which is unambiguous — a `new C()` whose `C` has no `__construct` truly does
/// nothing.
fn run_new_result_unused(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_stmt(fa.program, &mut |st| {
        let StmtKind::Expr(e) = &st.kind else { return };
        // Only the immediate `new C()` as a statement (not `$x = new C()`).
        let ExprKind::New { class, .. } = &e.kind else { return };
        let ExprKind::Name(_) = &class.kind else { return };
        let Some(fqn) = named_fqn(&fa.type_of(e)) else { return };
        let Some(cr) = fa.reflection.class(&fqn) else { return };
        // Skip anything we can't be sure about; only flag when the class has no
        // constructor at all (definitively side-effect-free instantiation).
        if fa.reflection.find_method(&fqn, "__construct").is_some() {
            return;
        }
        let short = cr.fqn.trim_start_matches('\\');
        out.push(
            Diagnostic::error(
                e.span,
                format!("Call to new {short}() on a separate line has no effect."),
            )
            .with_code("new.resultUnused"),
        );
    });
    out
}

// ---------------------------------------------------------------------------
// CallPrivateMethodThroughStaticRule (level 2)
// ---------------------------------------------------------------------------

/// `CallPrivateMethodThroughStaticRule` — `static::m()` where `m` is a private
/// method. Because `static::` resolves to the runtime class, a subclass that
/// redeclares `m` would shadow the private one, making the call unsafe. Skipped
/// when the enclosing class is `final` (no subclasses possible).
fn run_private_through_static(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |scope, fqn, c| {
        // A final class has no subclasses, so `static::` is safe.
        if c.modifiers.is_final {
            return;
        }
        for m in methods(c) {
            let Some(body) = &m.body else { continue };
            let mut exprs: Vec<&Expr> = Vec::new();
            for st in body {
                collect_exprs_in_stmt(st, &mut exprs);
            }
            for e in exprs {
                let ExprKind::StaticCall { class, method, .. } = &e.kind else { continue };
                let MemberName::Ident(name) = method else { continue };
                // Only `static::` (late static binding), spelled as a bare name.
                let ExprKind::Name(n) = &class.kind else { continue };
                if !matches!(scope.resolve_class(n), Resolution::LateStatic(ref w) if w == "static")
                {
                    continue;
                }
                let mname = fa.interner.resolve(*name);
                let Some(found) = fa.reflection.find_method(fqn, mname) else { continue };
                if found.member.magic || found.member.visibility != Visibility::Private {
                    continue;
                }
                let here = found.declaring_class.trim_start_matches('\\');
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!("Unsafe call to private method {here}::{mname}() through static::."),
                    )
                    .with_code("staticClassAccess.privateMethod"),
                );
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// ConsistentConstructorDeclarationRule (level 0)
// ---------------------------------------------------------------------------

/// `ConsistentConstructorDeclarationRule` — a private `__construct` in a class
/// declaring the `@consistent-constructor` (or phpstan/psalm-prefixed) PHPDoc tag.
/// A private constructor cannot be enforced for child classes. Skipped for `final`
/// classes (no children to enforce against).
fn run_consistent_constructor_private(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, _, c| {
        if c.modifiers.is_final || c.kind != ClassKind::Class {
            return;
        }
        if !has_consistent_constructor_tag(fa, c) {
            return;
        }
        for m in methods(c) {
            if is_ctor(fa, m) && vis(m) == Visibility::Private {
                out.push(
                    Diagnostic::error(
                        method_span(m),
                        "Private constructor cannot be enforced as consistent for child classes."
                            .to_string(),
                    )
                    .with_code("consistentConstructor.private"),
                );
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// IncompatibleDefaultParameterTypeRule (level 2)
// ---------------------------------------------------------------------------

/// `IncompatibleDefaultParameterTypeRule` — a method parameter whose default
/// value's type is not assignable to the parameter's declared type, e.g.
/// `function f(int $x = 'str')`. Lenient: `null` defaults are always allowed (PHP
/// makes the parameter implicitly nullable), and only definitively-incompatible
/// concrete defaults are flagged (`is_assignable` is the same lenient relation the
/// argument-type rules use).
/// The type of a parameter's default-value expression (constant-folded). Param
/// defaults aren't in the flow type-map, so we evaluate the literal directly;
/// a non-constant default yields `mixed` (skipped, false-positive-safe).
/// Whether `t` (under one level of nullable) is array/iterable-like.
fn is_array_or_iterable(t: &Type) -> bool {
    match t {
        Type::Array(_) | Type::Iterable(_) | Type::List(_) | Type::Shape { .. } => true,
        Type::Nullable(inner) => is_array_or_iterable(inner),
        _ => false,
    }
}

fn const_default_type(e: &php_ast::Expr) -> Type {
    use php_infer::ConstVal;
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

fn run_incompatible_default_param(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, fqn, c| {
        let Some(class) = fa.reflection.class(fqn) else { return };
        let short = class.fqn.trim_start_matches('\\');
        for (md, mr) in zip_methods(fa.interner, c, class) {
            for (i, (p, pr)) in md.params.iter().zip(&mr.params).enumerate() {
                let Some(default) = &p.default else { continue };
                // A literal `null` default implicitly nullablizes the parameter.
                if matches!(&default.kind, ExprKind::Name(n) if n.text.eq_ignore_ascii_case("null"))
                {
                    continue;
                }
                // No declared type → nothing to check.
                if pr.ty == Type::Mixed {
                    continue;
                }
                // Param defaults aren't in the body type-map; fold the literal.
                let given = const_default_type(default);
                // An array-literal default is compatible with any array/iterable
                // parameter (empty `[]` fits any `array<K,V>`; element precision is
                // intentionally under-reported rather than false-flagged).
                if matches!(given, Type::Array(_)) && is_array_or_iterable(&pr.ty) {
                    continue;
                }
                if crate::is_assignable(fa.reflection, &given, &pr.ty) {
                    continue;
                }
                out.push(
                    Diagnostic::error(
                        default.span,
                        format!(
                            "Default value of the parameter #{} ${} ({}) of method {short}::{}() is incompatible with type {}.",
                            i + 1,
                            fa.interner.resolve(p.name),
                            given,
                            fa.interner.resolve(md.name),
                            pr.ty
                        ),
                    )
                    .with_code("parameter.defaultValue"),
                );
            }
        }
    });
    out
}

/// Whether the class docblock carries a `@consistent-constructor` tag (the marker
/// phpstan honours; also accept the `@phpstan-`/`@psalm-` prefixed spellings).
fn has_consistent_constructor_tag(_fa: &FileAnalysis, c: &ClassDecl) -> bool {
    let Some(raw) = &c.doc else { return false };
    raw.contains("@consistent-constructor")
        || raw.contains("@phpstan-consistent-constructor")
        || raw.contains("@psalm-consistent-constructor")
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "method.abstract", level: 0, run: run_abstract_in_non_abstract },
    RuleEntry { name: "method.abstractPrivate", level: 0, run: run_abstract_private },
    RuleEntry { name: "method.nonAbstract", level: 0, run: run_abstract_body },
    RuleEntry { name: "method.finalPrivate", level: 0, run: run_final_private },
    RuleEntry { name: "method.visibilityInInterface", level: 0, run: run_visibility_in_interface },
    RuleEntry { name: "constructor.returnType", level: 0, run: run_constructor_return_type },
    RuleEntry { name: "method.staticConstructor", level: 0, run: run_constructor_modifiers },
    RuleEntry { name: "method.duplicateParameter", level: 0, run: run_duplicate_parameter },
    RuleEntry { name: "method.missingImplementation", level: 0, run: run_missing_implementation },
    RuleEntry { name: "class.serializable", level: 0, run: run_serializable_methods },
    RuleEntry { name: "method.attributeTarget", level: 0, run: run_method_attribute_target },
    RuleEntry { name: "method.overriding", level: 0, run: run_overriding_method },
    RuleEntry { name: "method.callExistence", level: 0, run: run_call_existence },
    RuleEntry { name: "method.callTyped", level: 0, run: run_call_methods_typed },
    RuleEntry { name: "staticMethod.callNamed", level: 0, run: run_static_call_named },
    RuleEntry { name: "consistentConstructor.private", level: 0, run: run_consistent_constructor_private },
    RuleEntry { name: "staticClassAccess.privateMethod", level: 2, run: run_private_through_static },
    RuleEntry { name: "parameter.defaultValue", level: 2, run: run_incompatible_default_param },
    RuleEntry { name: "nullsafe.neverNull", level: 4, run: run_nullsafe_never_null },
    RuleEntry { name: "new.resultUnused", level: 4, run: run_new_result_unused },
    RuleEntry { name: "argument.type", level: 5, run: run_method_argument_types },
    RuleEntry { name: "missingType.return", level: 6, run: run_missing_return_type },
    RuleEntry { name: "missingType.parameter", level: 6, run: run_missing_param_type },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    #[test]
    fn abstract_method_in_non_abstract_class() {
        let src = "<?php class C { abstract function f(); }";
        assert_eq!(codes(src, run_abstract_in_non_abstract), ["method.abstract"]);
    }

    #[test]
    fn abstract_method_in_abstract_class_is_clean() {
        let src = "<?php abstract class C { abstract function f(); }";
        assert!(codes(src, run_abstract_in_non_abstract).is_empty());
    }

    #[test]
    fn abstract_method_in_interface_is_clean() {
        let src = "<?php interface I { public function f(); }";
        assert!(codes(src, run_abstract_in_non_abstract).is_empty());
    }

    #[test]
    fn private_abstract_method_flagged() {
        let src = "<?php abstract class C { private abstract function f(); }";
        assert_eq!(codes(src, run_abstract_private), ["method.abstractPrivate"]);
    }

    #[test]
    fn private_abstract_in_interface_flagged() {
        let src = "<?php interface I { private abstract function f(); }";
        assert_eq!(codes(src, run_abstract_private), ["method.abstractPrivate"]);
    }

    #[test]
    fn abstract_method_with_body_flagged() {
        let src = "<?php abstract class C { abstract function f() { return 1; } }";
        assert_eq!(codes(src, run_abstract_body), ["method.nonAbstract"]);
    }

    #[test]
    fn concrete_method_without_body_flagged() {
        let src = "<?php class C { public function f(); }";
        assert_eq!(codes(src, run_abstract_body), ["method.nonAbstract"]);
    }

    #[test]
    fn normal_methods_body_clean() {
        let src =
            "<?php class C { public function f() {} } abstract class D { abstract function g(); }";
        assert!(codes(src, run_abstract_body).is_empty());
    }

    #[test]
    fn final_private_method_flagged() {
        let src = "<?php class C { final private function f() {} }";
        assert_eq!(codes(src, run_final_private), ["method.finalPrivate"]);
    }

    #[test]
    fn final_private_constructor_is_clean() {
        let src = "<?php class C { final private function __construct() {} }";
        assert!(codes(src, run_final_private).is_empty());
    }

    #[test]
    fn non_public_interface_method_flagged() {
        let src = "<?php interface I { protected function f(); }";
        assert_eq!(codes(src, run_visibility_in_interface), ["method.visibility"]);
    }

    #[test]
    fn public_interface_method_clean() {
        let src = "<?php interface I { public function f(); }";
        assert!(codes(src, run_visibility_in_interface).is_empty());
    }

    #[test]
    fn constructor_with_return_type_flagged() {
        let src = "<?php class C { public function __construct(): void {} }";
        assert_eq!(codes(src, run_constructor_return_type), ["constructor.returnType"]);
    }

    #[test]
    fn constructor_without_return_type_clean() {
        let src = "<?php class C { public function __construct() {} }";
        assert!(codes(src, run_constructor_return_type).is_empty());
    }

    #[test]
    fn static_constructor_flagged() {
        let src = "<?php class C { public static function __construct() {} }";
        assert_eq!(codes(src, run_constructor_modifiers), ["method.staticConstructor"]);
    }

    #[test]
    fn duplicate_parameter_flagged() {
        let src = "<?php class C { public function f($a, $a) {} }";
        assert_eq!(codes(src, run_duplicate_parameter), ["method.duplicateParameter"]);
    }

    #[test]
    fn distinct_parameters_clean() {
        let src = "<?php class C { public function f($a, $b) {} }";
        assert!(codes(src, run_duplicate_parameter).is_empty());
    }

    #[test]
    fn missing_implementation_flagged() {
        let src = "<?php
            abstract class Base { abstract public function f(): void; }
            class C extends Base {}";
        assert_eq!(codes(src, run_missing_implementation), ["method.missingImplementation"]);
    }

    #[test]
    fn implemented_abstract_is_clean() {
        let src = "<?php
            abstract class Base { abstract public function f(): void; }
            class C extends Base { public function f(): void {} }";
        assert!(codes(src, run_missing_implementation).is_empty());
    }

    #[test]
    fn override_final_method_flagged() {
        let src = "<?php
            class Base { final public function f(): void {} }
            class C extends Base { public function f(): void {} }";
        assert!(codes(src, run_overriding_method).contains(&"method.parentMethodFinal"));
    }

    #[test]
    fn override_static_flip_flagged() {
        let src = "<?php
            class Base { public static function f(): void {} }
            class C extends Base { public function f(): void {} }";
        assert!(codes(src, run_overriding_method).contains(&"method.nonStatic"));
    }

    #[test]
    fn override_narrows_visibility_flagged() {
        let src = "<?php
            class Base { public function f(): void {} }
            class C extends Base { protected function f(): void {} }";
        assert!(codes(src, run_overriding_method).contains(&"method.visibility"));
    }

    #[test]
    fn compatible_override_clean() {
        let src = "<?php
            class Base { public function f(): void {} }
            class C extends Base { public function f(): void {} }";
        assert!(codes(src, run_overriding_method).is_empty());
    }

    #[test]
    fn call_to_undefined_this_method_flagged() {
        let src = "<?php class C { public function a() { $this->missing(); } public function b() {} }";
        assert!(codes(src, run_call_existence).contains(&"method.notFound"));
    }

    #[test]
    fn call_to_existing_this_method_clean() {
        let src = "<?php class C { public function a() { $this->b(); } public function b() {} }";
        assert!(codes(src, run_call_existence).is_empty());
    }

    #[test]
    fn self_static_call_to_undefined_flagged() {
        let src = "<?php class C { public function a() { self::missing(); } }";
        assert!(codes(src, run_call_existence).contains(&"staticMethod.notFound"));
    }

    #[test]
    fn too_few_arguments_flagged() {
        let src =
            "<?php class C { public function a() { $this->need(1); } public function need($x, $y) {} }";
        assert!(codes(src, run_call_existence).contains(&"parameter.notOptional"));
    }

    #[test]
    fn too_many_arguments_flagged() {
        let src =
            "<?php class C { public function a() { $this->one(1, 2); } public function one($x) {} }";
        assert!(codes(src, run_call_existence).contains(&"argument.unknown"));
    }

    #[test]
    fn correct_argument_count_clean() {
        let src =
            "<?php class C { public function a() { $this->two(1, 2); } public function two($x, $y) {} }";
        assert!(codes(src, run_call_existence).is_empty());
    }

    #[test]
    fn variadic_allows_extra_args() {
        let src =
            "<?php class C { public function a() { $this->v(1, 2, 3); } public function v(...$xs) {} }";
        assert!(codes(src, run_call_existence).is_empty());
    }

    #[test]
    fn optional_param_allows_fewer_args() {
        let src =
            "<?php class C { public function a() { $this->o(1); } public function o($x, $y = 0) {} }";
        assert!(codes(src, run_call_existence).is_empty());
    }

    #[test]
    fn missing_return_type_flagged() {
        let src = "<?php class C { public function f() { return 1; } }";
        assert_eq!(codes(src, run_missing_return_type), ["missingType.return"]);
    }

    #[test]
    fn present_return_type_clean() {
        let src = "<?php class C { public function f(): int { return 1; } }";
        assert!(codes(src, run_missing_return_type).is_empty());
    }

    #[test]
    fn phpdoc_return_type_clean() {
        let src = "<?php class C { /** @return int */ public function f() { return 1; } }";
        assert!(codes(src, run_missing_return_type).is_empty());
    }

    #[test]
    fn phpdoc_return_this_clean() {
        // `@return $this` resolves to a type our reflection may render as exotic,
        // but the *tag* is present — so it's documented, not "missing".
        let src = "<?php class C { /** @return $this */ public function chain() { return $this; } }";
        assert!(codes(src, run_missing_return_type).is_empty());
    }

    #[test]
    fn override_inherits_return_typehint() {
        // The implementing method has no own return type, but the interface
        // prototype declares `@return`, which phpstan (and we) inherit.
        let src = "<?php interface I { /** @return int */ public function v(); } \
            class C implements I { public function v() { return 1; } }";
        assert!(codes(src, run_missing_return_type).is_empty());
    }

    #[test]
    fn override_inherits_param_typehint() {
        let src = "<?php interface I { public function v(int $x); } \
            class C implements I { public function v($x): void {} }";
        assert!(codes(src, run_missing_param_type).is_empty());
    }

    #[test]
    fn untyped_method_with_no_prototype_still_flagged() {
        let src = "<?php class C { public function v() { return 1; } }";
        assert_eq!(codes(src, run_missing_return_type), ["missingType.return"]);
    }

    #[test]
    fn phpdoc_param_clean_for_method() {
        let src = "<?php class C { /** @param int $x */ public function f($x): void {} }";
        assert!(codes(src, run_missing_param_type).is_empty());
    }

    #[test]
    fn array_literal_default_for_typed_array_param_clean() {
        // `array<string,mixed> $o = []` — an empty array fits any array<K,V>.
        let src = "<?php class C { /** @param array<string,mixed> $o */ public function __construct(array $o = []) {} }";
        assert!(codes(src, run_incompatible_default_param).is_empty());
    }

    #[test]
    fn constructor_return_type_not_required() {
        let src = "<?php class C { public function __construct() {} }";
        assert!(codes(src, run_missing_return_type).is_empty());
    }

    #[test]
    fn serializable_without_magic_methods_flagged() {
        let src = "<?php class C implements Serializable {}";
        let cs = codes(src, run_serializable_methods);
        assert!(cs.contains(&"class.serializable"));
        assert_eq!(cs.len(), 2); // __serialize + __unserialize
    }

    #[test]
    fn serializable_with_magic_methods_clean() {
        let src = "<?php class C implements Serializable {
            public function __serialize(): array { return []; }
            public function __unserialize(array $d): void {}
        }";
        assert!(codes(src, run_serializable_methods).is_empty());
    }

    #[test]
    fn non_serializable_class_clean() {
        let src = "<?php class C {}";
        assert!(codes(src, run_serializable_methods).is_empty());
    }

    #[test]
    fn class_only_attribute_on_method_flagged() {
        let src = "<?php class C { #[\\Attribute] public function f(): void {} }";
        assert!(codes(src, run_method_attribute_target).contains(&"method.attributeTarget"));
    }

    #[test]
    fn missing_param_type_flagged() {
        let src = "<?php class C { public function f($a): void {} }";
        assert_eq!(codes(src, run_missing_param_type), ["missingType.parameter"]);
    }

    #[test]
    fn typed_param_clean() {
        let src = "<?php class C { public function f(int $a): void {} }";
        assert!(codes(src, run_missing_param_type).is_empty());
    }

    #[test]
    fn phpdoc_param_type_clean() {
        let src = "<?php class C { /** @param int $a */ public function f($a): void {} }";
        assert!(codes(src, run_missing_param_type).is_empty());
    }

    // --- method argument types -------------------------------------------

    #[test]
    fn wrong_method_argument_type_on_this_is_flagged() {
        let src = "<?php class C { public function set(int $n): void {} public function go(): void { $this->set('x'); } }";
        assert_eq!(codes(src, run_method_argument_types), ["argument.type"]);
    }

    #[test]
    fn wrong_method_argument_type_on_typed_local_is_flagged() {
        let src = "<?php class C { public function set(int $n): void {} } function f(): void { $c = new C(); $c->set('x'); }";
        assert_eq!(codes(src, run_method_argument_types), ["argument.type"]);
    }

    #[test]
    fn correct_method_argument_type_is_clean() {
        let src = "<?php class C { public function set(int $n): void {} public function go(): void { $this->set(5); } }";
        assert!(codes(src, run_method_argument_types).is_empty());
    }

    #[test]
    fn unknown_receiver_is_lenient() {
        // $x untyped -> mixed receiver -> no class -> no diagnostic.
        let src = "<?php function f($x): void { $x->set('s'); }";
        assert!(codes(src, run_method_argument_types).is_empty());
    }

    // --- CallMethodsRule on a typed receiver -----------------------------

    #[test]
    fn undefined_method_on_typed_local_flagged() {
        let src = "<?php class C { public function a(): void {} } function f(): void { $c = new C(); $c->missing(); }";
        assert!(codes(src, run_call_methods_typed).contains(&"method.notFound"));
    }

    #[test]
    fn existing_method_on_typed_local_clean() {
        let src = "<?php class C { public function a(): void {} } function f(): void { $c = new C(); $c->a(); }";
        assert!(codes(src, run_call_methods_typed).is_empty());
    }

    #[test]
    fn this_receiver_skipped_by_typed_rule() {
        // $this is handled by run_call_existence; this rule must stay silent.
        let src = "<?php class C { public function a(): void { $this->missing(); } }";
        assert!(codes(src, run_call_methods_typed).is_empty());
    }

    #[test]
    fn magic_call_receiver_is_lenient() {
        let src = "<?php class C { public function __call($n, $a) {} } function f(): void { $c = new C(); $c->whatever(); }";
        assert!(codes(src, run_call_methods_typed).is_empty());
    }

    // --- CallStaticMethodsRule (named class) -----------------------------

    #[test]
    fn undefined_static_method_on_named_class_flagged() {
        let src = "<?php class D { public static function ok(): void {} } class C { public function a(): void { D::missing(); } }";
        assert!(codes(src, run_static_call_named).contains(&"staticMethod.notFound"));
    }

    #[test]
    fn existing_static_method_on_named_class_clean() {
        let src = "<?php class D { public static function ok(): void {} } class C { public function a(): void { D::ok(); } }";
        assert!(codes(src, run_static_call_named).is_empty());
    }

    #[test]
    fn callstatic_magic_named_class_lenient() {
        let src = "<?php class D { public static function __callStatic($n, $a) {} } class C { public function a(): void { D::whatever(); } }";
        assert!(codes(src, run_static_call_named).is_empty());
    }

    #[test]
    fn unknown_named_class_static_lenient() {
        let src = "<?php class C { public function a(): void { Unknown::x(); } }";
        assert!(codes(src, run_static_call_named).is_empty());
    }

    #[test]
    fn self_static_call_skipped_by_named_rule() {
        let src = "<?php class C { public function a(): void { self::missing(); } }";
        assert!(codes(src, run_static_call_named).is_empty());
    }

    // --- NullsafeMethodCallRule -----------------------------------------

    #[test]
    fn nullsafe_on_non_nullable_flagged() {
        let src = "<?php class C { public function a(): void {} } function f(): void { $c = new C(); $c?->a(); }";
        assert!(codes(src, run_nullsafe_never_null).contains(&"nullsafe.neverNull"));
    }

    #[test]
    fn nullsafe_on_nullable_clean() {
        let src = "<?php class C { public function a(): void {} } function f(?C $c): void { $c?->a(); }";
        assert!(codes(src, run_nullsafe_never_null).is_empty());
    }

    #[test]
    fn nullsafe_on_unknown_is_lenient() {
        let src = "<?php function f($x): void { $x?->a(); }";
        assert!(codes(src, run_nullsafe_never_null).is_empty());
    }

    #[test]
    fn plain_arrow_call_not_flagged() {
        let src = "<?php class C { public function a(): void {} } function f(): void { $c = new C(); $c->a(); }";
        assert!(codes(src, run_nullsafe_never_null).is_empty());
    }

    // --- CallToConstructorStatementWithoutSideEffectsRule ----------------

    #[test]
    fn new_without_constructor_as_statement_flagged() {
        let src = "<?php class C {} function f(): void { new C(); }";
        assert!(codes(src, run_new_result_unused).contains(&"new.resultUnused"));
    }

    #[test]
    fn new_with_constructor_as_statement_clean() {
        let src = "<?php class C { public function __construct() {} } function f(): void { new C(); }";
        assert!(codes(src, run_new_result_unused).is_empty());
    }

    #[test]
    fn assigned_new_clean() {
        let src = "<?php class C {} function f(): void { $x = new C(); }";
        assert!(codes(src, run_new_result_unused).is_empty());
    }

    #[test]
    fn new_of_unknown_class_lenient() {
        let src = "<?php function f(): void { new Unknown(); }";
        assert!(codes(src, run_new_result_unused).is_empty());
    }

    // --- CallPrivateMethodThroughStaticRule ------------------------------

    #[test]
    fn static_call_to_private_flagged() {
        let src =
            "<?php class C { private function p(): void {} public function a(): void { static::p(); } }";
        assert!(codes(src, run_private_through_static).contains(&"staticClassAccess.privateMethod"));
    }

    #[test]
    fn static_call_to_public_clean() {
        let src =
            "<?php class C { public function p(): void {} public function a(): void { static::p(); } }";
        assert!(codes(src, run_private_through_static).is_empty());
    }

    #[test]
    fn static_call_to_private_in_final_class_clean() {
        let src =
            "<?php final class C { private function p(): void {} public function a(): void { static::p(); } }";
        assert!(codes(src, run_private_through_static).is_empty());
    }

    #[test]
    fn self_call_to_private_not_flagged_by_static_rule() {
        let src =
            "<?php class C { private function p(): void {} public function a(): void { self::p(); } }";
        assert!(codes(src, run_private_through_static).is_empty());
    }

    // --- ConsistentConstructorDeclarationRule ----------------------------

    #[test]
    fn private_constructor_with_consistent_tag_flagged() {
        let src = "<?php /** @consistent-constructor */ class C { private function __construct() {} }";
        assert!(codes(src, run_consistent_constructor_private)
            .contains(&"consistentConstructor.private"));
    }

    #[test]
    fn public_constructor_with_consistent_tag_clean() {
        let src = "<?php /** @consistent-constructor */ class C { public function __construct() {} }";
        assert!(codes(src, run_consistent_constructor_private).is_empty());
    }

    #[test]
    fn private_constructor_without_tag_clean() {
        let src = "<?php class C { private function __construct() {} }";
        assert!(codes(src, run_consistent_constructor_private).is_empty());
    }

    #[test]
    fn private_constructor_in_final_with_tag_clean() {
        let src = "<?php /** @consistent-constructor */ final class C { private function __construct() {} }";
        assert!(codes(src, run_consistent_constructor_private).is_empty());
    }

    // --- IncompatibleDefaultParameterTypeRule ----------------------------

    #[test]
    fn incompatible_string_default_for_int_flagged() {
        let src = "<?php class C { public function f(int $x = 'str'): void {} }";
        assert!(codes(src, run_incompatible_default_param).contains(&"parameter.defaultValue"));
    }

    #[test]
    fn compatible_int_default_clean() {
        let src = "<?php class C { public function f(int $x = 5): void {} }";
        assert!(codes(src, run_incompatible_default_param).is_empty());
    }

    #[test]
    fn null_default_always_allowed() {
        let src = "<?php class C { public function f(int $x = null): void {} }";
        assert!(codes(src, run_incompatible_default_param).is_empty());
    }

    #[test]
    fn untyped_param_default_clean() {
        let src = "<?php class C { public function f($x = 'str'): void {} }";
        assert!(codes(src, run_incompatible_default_param).is_empty());
    }
}
