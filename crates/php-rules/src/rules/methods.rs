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
//! - `method.resultDiscarded` / `method.inVoidCast` and
//!   `staticMethod.resultDiscarded` / `staticMethod.inVoidCast`
//!   (`Call*MethodStatementWithNoDiscardRule`) — PHP 8.5 `#[NoDiscard]` calls
//!   and unnecessary `(void)` casts.
//! - `MissingMethodSelfOutTypeRule` (level 6) — missing iterable value type,
//!   generic args, or callable signature inside `@phpstan-self-out`.
//!
//! DEFERRED (need expression-type inference, not just the AST + reflection):
//! - `CallMethodsRule` argument *type* matching beyond positional, named-argument
//!   resolution, `MethodCallableRule`/`StaticMethodCallableRule` (`callable.notSupported`
//!   never fires on PHP 8.1+ — the only condition our target version triggers),
//!   `IncompatibleDefaultParameterTypeRule`, `MethodSignatureRule` param/return
//!   covariance, closure/arrow callable NoDiscard metadata propagation,
//!   `ExistingClassesInTypehintsRule` (overlaps class-existence rules),
//!   `MethodCallWithPossiblyRenamedNamedArgumentRule`,
//!   `ConsistentConstructorRule` (param/visibility comparison vs parent constructor —
//!   the `consistentConstructor` *attribute* requires a custom PHPDoc tag we don't model).

use crate::{
    compat, decls,
    members::{MemberAccessResolver, ResolveStatus},
    symbols, FileAnalysis, RuleEntry,
};
use php_ast::{
    BinOp, CastKind, ClassDecl, ClassKind, Expr, ExprKind, Member, MemberName, MethodDecl, Stmt,
    StmtKind, Visibility,
};
use php_diagnostics::Diagnostic;
use php_intern::Interner;
use php_phpdoc::DocType;
use php_reflect::{
    ClassReflection, Found, MethodReflection, ParamReflection, ReflectionIndex,
};
use php_resolve::{for_each_region, Resolution, Scope};
use php_span::Span;
use php_types::Type;
use std::collections::{HashMap, HashSet};

// ---------------------------------------------------------------------------
// shared traversal: every class-like with its FQN + declaring scope
// ---------------------------------------------------------------------------

/// Visit every class-like declaration in the file, paired with its resolved FQN
/// and the [`Scope`] of its namespace region. Descends into nested declarations
/// (blocks, control flow) so conditionally-declared classes are covered.
fn for_each_class(fa: &FileAnalysis, mut f: impl FnMut(&Scope, &str, &ClassDecl)) {
    decls::for_each_class_like(fa, &mut f);
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
    fa.interner
        .resolve(m.name)
        .eq_ignore_ascii_case("__construct")
}

/// The display name of a class (its name as written, leading `\` stripped).
fn display(fa: &FileAnalysis, c: &ClassDecl) -> String {
    c.name
        .map(|n| fa.interner.resolve(n).to_string())
        .unwrap_or_else(|| "class@anonymous".to_string())
}

/// A best-effort span for a method-level diagnostic. Our AST does not record a
/// span on [`MethodDecl`] itself, so we point at the first available child span:
/// The method-name token span.
fn method_span(m: &MethodDecl) -> Span {
    m.name_span
}

/// The class-name token span (the `class` keyword for anonymous classes).
fn class_span(c: &ClassDecl) -> Span {
    c.name_span
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
                && matches!(
                    mname.to_ascii_lowercase().as_str(),
                    "cases" | "from" | "tryfrom"
                )
            {
                continue;
            }
            let lead = if c.kind == ClassKind::Enum {
                "Enum"
            } else {
                "Non-abstract class"
            };
            out.push(
                Diagnostic::error(
                    method_span(m),
                    format!(
                        "{lead} {} contains abstract method {mname}().",
                        display(fa, c)
                    ),
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
                        format!(
                            "Abstract method {}::{}() cannot contain body.",
                            display(fa, c),
                            name
                        ),
                    )
                    .with_code("method.nonAbstract"),
                );
            } else if !m.modifiers.is_abstract && m.body.is_none() && c.kind != ClassKind::Interface
            {
                out.push(
                    Diagnostic::error(
                        method_span(m),
                        format!(
                            "Non-abstract method {}::{}() must contain body.",
                            display(fa, c),
                            name
                        ),
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
                        format!(
                            "Constructor {}::__construct() cannot be static.",
                            display(fa, c)
                        ),
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
            let lead = if c.kind == ClassKind::Enum {
                "Enum"
            } else {
                "Non-abstract class"
            };
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
                let declaring = describe_declarer(refl, found.declaring_class);
                out.push((found.member.name.clone(), declaring));
            }
        }
    }
    out
}

/// Gather every method name declared anywhere in `fqn`'s hierarchy.
fn collect_method_names(
    refl: &ReflectionIndex,
    fqn: &str,
    visited: &mut Vec<String>,
    out: &mut Vec<String>,
) {
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
    for parent in class
        .parents
        .iter()
        .chain(&class.interfaces)
        .chain(&class.traits)
    {
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
                .map(|f| {
                    f.trim_start_matches('\\')
                        .eq_ignore_ascii_case("Serializable")
                })
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
                    let Some(fqn) = scope.resolve_class(&attr.name).fqn().map(str::to_string)
                    else {
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
        let Some(class) = fa.reflection.class(fqn) else {
            return;
        };
        for (md, m) in zip_methods(fa.interner, c, class) {
            if m.magic {
                continue;
            }
            let Some(parent) = find_parent_method(fa.reflection, class, &m.name) else {
                continue;
            };
            let pm = &parent.member;
            let here = display(fa, c);
            let there = parent.declaring_class.trim_start_matches('\\');
            let mname = &m.name;

            if pm.is_final {
                out.push(
                    Diagnostic::error(
                        class_span(c),
                        format!(
                            "Method {here}::{mname}() overrides final method {there}::{mname}()."
                        ),
                    )
                    .with_code("method.parentMethodFinal"),
                );
            }
            // Constructors have no prototype: PHP lets a child constructor
            // change the signature and visibility freely (phpstan's
            // OverridingMethodRule only keeps the final-parent check above).
            if m.name.eq_ignore_ascii_case("__construct") {
                continue;
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
            if pm.visibility != Visibility::Private
                && vis_rank(pm.visibility) > vis_rank(m.visibility)
            {
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
            check_overriding_method_signature(fa, c, md, m, &parent, &mut out);
        }
    });
    out
}

fn check_overriding_method_signature(
    fa: &FileAnalysis,
    c: &ClassDecl,
    md: &MethodDecl,
    method: &MethodReflection,
    parent: &Found<MethodReflection>,
    out: &mut Vec<Diagnostic>,
) {
    let pm = &parent.member;
    let here = display(fa, c);
    let there = parent.declaring_class.trim_start_matches('\\');
    let mname = &method.name;

    if compat::declaration_mismatch(
        fa,
        &method.return_type,
        &method.native_return,
        &pm.return_type,
        &pm.native_return,
    ) {
        out.push(
            Diagnostic::error(
                md.return_type
                    .as_ref()
                    .map(|t| t.span)
                    .unwrap_or_else(|| method_span(md)),
                format!(
                    "Return type ({}) of method {here}::{mname}() should be compatible with return type ({}) of method {there}::{mname}()",
                    method.return_type, pm.return_type
                ),
            )
            .with_code("method.childReturnType"),
        );
    }

    let count = method
        .params
        .len()
        .min(pm.params.len())
        .min(md.params.len());
    for i in 0..count {
        let child = &method.params[i];
        let parent_param = &pm.params[i];
        if child.variadic || parent_param.variadic {
            continue;
        }
        if !compat::declaration_mismatch(
            fa,
            &parent_param.ty,
            &parent_param.native_ty,
            &child.ty,
            &child.native_ty,
        ) {
            continue;
        }
        let span = md.params[i]
            .ty
            .as_ref()
            .map(|t| t.span)
            .unwrap_or(md.params[i].span);
        out.push(
            Diagnostic::error(
                span,
                format!(
                    "Parameter #{} ${} ({}) of method {here}::{mname}() should be compatible with parameter ${} ({}) of method {there}::{mname}()",
                    i + 1,
                    child.name,
                    child.ty,
                    parent_param.name,
                    parent_param.ty
                ),
            )
            .with_code("method.childParameterType"),
        );
    }
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
fn find_parent_method<'a>(
    refl: &'a ReflectionIndex,
    class: &ClassReflection,
    name: &str,
) -> Option<Found<'a, MethodReflection>> {
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
        let Some(class) = fa.reflection.class(fqn) else {
            return;
        };
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
                    format!(
                        "Method {}::{name}() has no return type specified.",
                        display(fa, c)
                    ),
                )
                .with_code("missingType.return"),
            );
        }
    });
    out
}

/// Whether a docblock declares a `@return` (incl. `@phpstan-`/`@psalm-return`).
fn doc_has_return(doc: Option<&str>) -> bool {
    php_phpdoc::query::has_return_conservative(doc)
}

/// Walk the transitive supertypes of `class` (parents, interfaces, traits — and
/// their supertypes), invoking `check` on each ancestor's *own* declaration of the
/// method `name`. Returns true as soon as `check` does. phpstan considers a method
/// "typed" if *any* prototype anywhere up the hierarchy supplies the type — e.g. an
/// interface's `@return` flows down through an abstract base to a concrete override.
fn hierarchy_method<F>(
    fa: &FileAnalysis,
    class: &php_reflect::ClassReflection,
    name: &str,
    mut check: F,
) -> bool
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
        let Some(anc) = fa.reflection.class(&fqn) else {
            continue;
        };
        if let Some(m) = anc
            .methods
            .iter()
            .find(|m| !m.magic && m.name.eq_ignore_ascii_case(name))
        {
            if check(m) {
                return true;
            }
        }
        stack.extend(
            anc.parents
                .iter()
                .chain(&anc.interfaces)
                .chain(&anc.traits)
                .filter_map(named_fqn),
        );
    }
    false
}

/// Whether an overridden prototype anywhere up the hierarchy declares a non-`mixed`
/// return type (native or `@return`). phpstan inherits it, so the override needn't repeat.
fn inherited_return_typed(
    fa: &FileAnalysis,
    class: &php_reflect::ClassReflection,
    name: &str,
) -> bool {
    hierarchy_method(fa, class, name, |m| m.explicit_return)
}

/// Whether an overridden prototype anywhere up the hierarchy types the parameter at `idx`.
fn inherited_param_typed(
    fa: &FileAnalysis,
    class: &php_reflect::ClassReflection,
    name: &str,
    idx: usize,
) -> bool {
    hierarchy_method(fa, class, name, |m| {
        m.params.get(idx).is_some_and(|p| p.explicit)
    })
}

/// Whether a docblock declares a `@param … $name` (any `@param*` prefix), with
/// `$name` matched as a whole variable token. Mirrors the function-rule helper.
fn doc_has_param(doc: Option<&str>, name: &str) -> bool {
    php_phpdoc::query::has_param_conservative(doc, name)
}

/// `MissingMethodParameterTypehintRule` — a method parameter with no type.
fn run_missing_param_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, fqn, c| {
        let Some(class) = fa.reflection.class(fqn) else {
            return;
        };
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
        if c.kind == ClassKind::Trait {
            return;
        }
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

fn check_call_expr(
    e: &Expr,
    fa: &FileAnalysis,
    scope: &Scope,
    self_fqn: &str,
    out: &mut Vec<Diagnostic>,
) {
    match &e.kind {
        ExprKind::MethodCall {
            recv, method, args, ..
        } => {
            // Only `$this->m(...)` — other receivers need type inference.
            if !is_this(recv, fa) {
                return;
            }
            if let MemberName::Ident(name) = method {
                // Spread/named args make arity opaque — skip arity but still check existence.
                let opaque = args
                    .iter()
                    .any(|a| a.spread || a.name.is_some() || a.placeholder);
                check_member_call(
                    e,
                    fa,
                    self_fqn,
                    fa.interner.resolve(*name),
                    args.len(),
                    opaque,
                    false,
                    out,
                );
            }
        }
        ExprKind::StaticCall {
            class,
            method,
            args,
        } => {
            let Some(target) = static_target_fqn(class, scope, self_fqn) else {
                return;
            };
            if let MemberName::Ident(name) = method {
                let opaque = args
                    .iter()
                    .any(|a| a.spread || a.name.is_some() || a.placeholder);
                check_member_call(
                    e,
                    fa,
                    &target,
                    fa.interner.resolve(*name),
                    args.len(),
                    opaque,
                    true,
                    out,
                );
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
    let ExprKind::Name(n) = &class.kind else {
        return None;
    };
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
        if !is_static
            && fa
                .reflection
                .final_concrete_descendants_have_method(class_fqn, method)
        {
            return;
        }
        let short = class_fqn.trim_start_matches('\\');
        let code = if is_static {
            "staticMethod.notFound"
        } else {
            "method.notFound"
        };
        out.push(
            Diagnostic::error(
                call.span,
                format!("Call to an undefined method {short}::{method}()."),
            )
            .with_code(code),
        );
        return;
    };
    let mr = &found.member;
    if mr.magic || arity_opaque {
        return;
    }
    let required = mr
        .params
        .iter()
        .filter(|p| !p.optional && !p.variadic)
        .count();
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
        StmtKind::If {
            cond,
            then,
            elseifs,
            els,
        } => {
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
        StmtKind::For {
            init,
            cond,
            update,
            body,
        } => {
            for e in init.iter().chain(cond).chain(update) {
                collect_expr(e, out);
            }
            collect_exprs_in_stmt(body, out);
        }
        StmtKind::Foreach {
            subject,
            key,
            value,
            body,
            ..
        } => {
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
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
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
        | AssignOp {
            target: lhs, rhs, ..
        }
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
    for call in fa.facts.method_calls() {
        let MemberName::Ident(name) = call.method else {
            continue;
        };
        if call
            .args
            .iter()
            .any(|a| a.spread || a.name.is_some() || a.placeholder)
        {
            continue;
        }
        let Some(fqn) = named_fqn(&fa.type_of(call.recv)) else {
            continue;
        };
        let mname = fa.interner.resolve(*name);
        let Some(found) = fa.reflection.find_method(&fqn, mname) else {
            continue;
        };
        let mr = &found.member;
        if mr.magic {
            continue;
        }
        let short = fqn.trim_start_matches('\\');
        for (i, arg) in call.args.iter().enumerate() {
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
    }
    out
}

/// The class FQN named by a type (through nullability), if any.
fn named_fqn(t: &Type) -> Option<String> {
    match t {
        Type::Named { fqn, .. } => Some(fqn.to_string()),
        Type::Nullable(inner) => named_fqn(inner),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// CallMethodsRule — existence + visibility on a typed receiver (`$expr->m()`)
// ---------------------------------------------------------------------------

/// Level-8 `checkNullables` strictness for method calls: at lower levels
/// phpstan strips `null` from a nullable receiver before judging the call, while
/// level 8+ reports `method.nonObject` for `$maybeC->m()`. This branch is
/// intentionally separate from method-existence so `?C->missing()` is reported
/// as a nullable receiver problem, not as an undefined method.
fn run_nullable_method_access(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::MethodCall {
            recv,
            nullsafe,
            method,
            ..
        } = &e.kind
        else {
            return;
        };
        if *nullsafe {
            return;
        }
        let MemberName::Ident(name) = method else {
            return;
        };
        let recv_ty = fa.type_of(recv);
        let Some(non_null) = super::non_null_part(&recv_ty) else {
            return;
        };
        if !super::known_objectish_type(fa, &non_null) {
            return;
        }
        let mname = fa.interner.resolve(*name);
        out.push(
            Diagnostic::error(
                e.span,
                format!(
                    "Cannot call method {mname}() on {}.",
                    super::nullable_type_display(&recv_ty)
                ),
            )
            .with_code("method.nonObject"),
        );
    });
    out
}

/// Level-7 `checkUnionTypes`: when a method call is valid for only some arms of
/// a concrete object union, phpstan reports the call on the whole union. We
/// implement the FP-safe slice: every union arm must be a fully-known class-ish
/// type, and at least one arm has the method while at least one definitely does
/// not.
fn run_union_method_access(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.report_maybes {
        return Vec::new();
    }
    let mut out = Vec::new();
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::MethodCall {
            recv,
            method,
            nullsafe,
            ..
        } = &e.kind
        else {
            return;
        };
        if *nullsafe {
            return;
        }
        let MemberName::Ident(name) = method else {
            return;
        };
        let recv_ty = fa.type_of(recv);
        let Some((has_method, lacks_method)) =
            union_method_status(fa, &recv_ty, fa.interner.resolve(*name))
        else {
            return;
        };
        if !(has_method && lacks_method) {
            return;
        }
        let mname = fa.interner.resolve(*name);
        out.push(
            Diagnostic::error(
                e.span,
                format!("Call to an undefined method {recv_ty}::{mname}()."),
            )
            .with_code("method.notFound"),
        );
    });
    out
}

fn union_method_status(fa: &FileAnalysis, ty: &Type, method: &str) -> Option<(bool, bool)> {
    let Type::Union(parts) = ty else {
        return None;
    };
    if parts.len() < 2 || super::type_contains_null(ty) {
        return None;
    }
    let mut has_method = false;
    let mut lacks_method = false;
    for part in parts.iter() {
        let Type::Named { fqn, .. } = part else {
            return None;
        };
        if !fa.class_fully_known(fqn) {
            return None;
        }
        if fa.reflection.find_method(fqn, method).is_some()
            || fa.reflection.find_method(fqn, "__call").is_some()
            || fa
                .reflection
                .final_concrete_descendants_have_method(fqn, method)
        {
            has_method = true;
        } else {
            lacks_method = true;
        }
    }
    Some((has_method, lacks_method))
}

/// `CallMethodsRule` (the existence part expressible from the type map) — an
/// instance method call `$expr->m(...)` on a non-`$this` receiver whose inferred
/// type resolves to a *known* class with no method `m` and no `__call`
/// (`method.notFound`). `$this` receivers are handled by `run_call_existence`
/// (which has the self-class context), so they're skipped here to avoid duplicate
/// diagnostics. Visibility checks are deferred (need the calling class context).
fn run_call_methods_typed(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let resolver = MemberAccessResolver::new(fa);
    crate::walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::MethodCall { recv, method, .. } = &e.kind else {
            return;
        };
        let MemberName::Ident(name) = method else {
            return;
        };
        // `$this->m()` is handled by run_call_existence (with self-class context).
        if is_this(recv, fa) {
            return;
        }
        let recv_ty = fa.type_of(recv);
        if fa.check_nullables && super::type_contains_null(&recv_ty) {
            return;
        }
        let Some(fqn) = named_fqn(&recv_ty) else {
            return;
        };
        // The class must be known so absence/visibility is reliable.
        if !fa.class_fully_known(&fqn) {
            return;
        }
        let mname = fa.interner.resolve(*name);
        let short = fqn.trim_start_matches('\\');
        match resolver.instance_method(&recv_ty, mname) {
            ResolveStatus::Unknown => {
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!("Call to an undefined method {short}::{mname}()."),
                    )
                    .with_code("method.notFound"),
                );
            }
            ResolveStatus::Known(_) | ResolveStatus::Opaque | ResolveStatus::Skipped => {
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
    let resolver = MemberAccessResolver::new(fa);
    for_each_class(fa, |scope, _, c| {
        if c.kind == ClassKind::Trait {
            return;
        }
        for m in methods(c) {
            let Some(body) = &m.body else { continue };
            let mut exprs: Vec<&Expr> = Vec::new();
            for st in body {
                collect_exprs_in_stmt(st, &mut exprs);
            }
            for e in exprs {
                let ExprKind::StaticCall { class, method, .. } = &e.kind else {
                    continue;
                };
                let MemberName::Ident(name) = method else {
                    continue;
                };
                let ExprKind::Name(n) = &class.kind else {
                    continue;
                };
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
                if matches!(resolver.static_method(&fqn, mname), ResolveStatus::Unknown) {
                    out.push(
                        Diagnostic::error(
                            e.span,
                            format!("Call to an undefined static method {fqn}::{mname}()."),
                        )
                        .with_code("staticMethod.notFound"),
                    );
                }
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// MethodCallWithPossiblyRenamedNamedArgumentRule (level 0)
// ---------------------------------------------------------------------------

/// `MethodCallWithPossiblyRenamedNamedArgumentRule` — a call to
/// `Base::m(paramName: ...)` through a parameter typed as `Base`, where a known
/// subtype overrides `m()` and renames that parameter. Conservative: only
/// parameter receivers are considered, and both the receiver class hierarchy and
/// the subtype hierarchy must be fully indexed.
fn run_renamed_named_argument_call(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let renames = collect_overriding_parameter_renames(fa);
    if renames.is_empty() {
        return Vec::new();
    }

    let mut calls: HashMap<(String, String, String), Vec<NamedArgMethodCall>> = HashMap::new();
    for call in collect_parameter_receiver_named_arg_calls(fa) {
        calls
            .entry((
                call.prototype_class.to_ascii_lowercase(),
                call.method.to_ascii_lowercase(),
                call.parameter.clone(),
            ))
            .or_default()
            .push(call);
    }

    let mut out = Vec::new();
    for rename in renames {
        let key = (
            rename.prototype_class.to_ascii_lowercase(),
            rename.method.to_ascii_lowercase(),
            rename.prototype_parameter.clone(),
        );
        let Some(matching_calls) = calls.get(&key) else {
            continue;
        };
        for call in matching_calls {
            out.push(
                Diagnostic::error(
                    call.span,
                    format!(
                        "Call to {}::{}() uses named argument for parameter ${}, but {} renames it to ${}.",
                        rename.prototype_class.trim_start_matches('\\'),
                        rename.method,
                        rename.prototype_parameter,
                        rename.subtype_class.trim_start_matches('\\'),
                        rename.subtype_parameter
                    ),
                )
                .with_code("argument.parameterRenamedInSubtype"),
            );
        }
    }
    out
}

#[derive(Debug, Clone)]
struct ParameterRename {
    prototype_class: String,
    method: String,
    subtype_class: String,
    prototype_parameter: String,
    subtype_parameter: String,
}

#[derive(Debug, Clone)]
struct NamedArgMethodCall {
    prototype_class: String,
    method: String,
    parameter: String,
    span: Span,
}

fn collect_overriding_parameter_renames(fa: &FileAnalysis) -> Vec<ParameterRename> {
    let mut out = Vec::new();
    for_each_class(fa, |_, fqn, _| {
        if !fa.class_fully_known(fqn) {
            return;
        }
        let Some(class) = fa.reflection.class(fqn) else {
            return;
        };
        for method in &class.methods {
            if method.magic || method.visibility == Visibility::Private {
                continue;
            }
            let Some(parent) = find_parent_method(fa.reflection, class, &method.name) else {
                continue;
            };
            if parent.member.visibility == Visibility::Private || parent.member.magic {
                continue;
            }
            if !method_accepts_named_arguments(fa, parent.declaring_class, &parent.member.name) {
                continue;
            }
            for (prototype_param, method_param) in parent.member.params.iter().zip(&method.params) {
                if prototype_param.name == method_param.name {
                    continue;
                }
                out.push(ParameterRename {
                    prototype_class: parent.declaring_class.to_string(),
                    method: parent.member.name.clone(),
                    subtype_class: class.fqn.clone(),
                    prototype_parameter: prototype_param.name.clone(),
                    subtype_parameter: method_param.name.clone(),
                });
            }
        }
    });
    out
}

fn collect_parameter_receiver_named_arg_calls(fa: &FileAnalysis) -> Vec<NamedArgMethodCall> {
    let mut out = Vec::new();
    crate::walk::for_each_stmt(fa.program, &mut |st| match &st.kind {
        StmtKind::Function(f) => {
            let params = param_name_set(fa, &f.params);
            collect_named_arg_calls_in_body(fa, &params, &f.body, &mut out);
        }
        StmtKind::Class(c) => {
            for member in &c.members {
                let Member::Method(m) = member else { continue };
                let Some(body) = &m.body else { continue };
                let params = param_name_set(fa, &m.params);
                collect_named_arg_calls_in_body(fa, &params, body, &mut out);
            }
        }
        _ => {}
    });
    out
}

fn param_name_set(fa: &FileAnalysis, params: &[php_ast::Param]) -> HashSet<String> {
    params
        .iter()
        .map(|p| fa.interner.resolve(p.name).to_string())
        .collect()
}

fn collect_named_arg_calls_in_body(
    fa: &FileAnalysis,
    parameter_names: &HashSet<String>,
    body: &[Stmt],
    out: &mut Vec<NamedArgMethodCall>,
) {
    for st in body {
        crate::walk::for_each_expr_in_scope(st, &mut |e| {
            let ExprKind::MethodCall {
                recv, method, args, ..
            } = &e.kind
            else {
                return;
            };
            if !receiver_is_parameter(recv, fa, parameter_names) {
                return;
            }
            let MemberName::Ident(name) = method else {
                return;
            };
            let Some(receiver_fqn) = named_fqn(&fa.type_of(recv)) else {
                return;
            };
            if !fa.class_fully_known(&receiver_fqn) {
                return;
            }
            let method_name = fa.interner.resolve(*name);
            let Some(found) = fa.reflection.find_method(&receiver_fqn, method_name) else {
                return;
            };
            if found.member.magic || found.member.visibility == Visibility::Private {
                return;
            }
            let Some(declaring_class) = fa.reflection.class(found.declaring_class) else {
                return;
            };
            if declaring_class.is_final {
                return;
            }
            if !method_accepts_named_arguments(fa, found.declaring_class, &found.member.name) {
                return;
            }
            for arg in args {
                let Some(arg_name) = arg.name.map(|s| fa.interner.resolve(s)) else {
                    continue;
                };
                if !found.member.params.iter().any(|p| p.name == arg_name) {
                    continue;
                }
                out.push(NamedArgMethodCall {
                    prototype_class: found.declaring_class.to_string(),
                    method: found.member.name.clone(),
                    parameter: arg_name.to_string(),
                    span: arg.span,
                });
            }
        });
    }
}

fn receiver_is_parameter(e: &Expr, fa: &FileAnalysis, parameter_names: &HashSet<String>) -> bool {
    let ExprKind::Variable(sym) = &e.kind else {
        return false;
    };
    let name = fa.interner.resolve(*sym);
    name != "this" && parameter_names.contains(name)
}

fn method_accepts_named_arguments(fa: &FileAnalysis, class_fqn: &str, method: &str) -> bool {
    if !class_accepts_named_arguments(fa, class_fqn, &mut Vec::new()) {
        return false;
    }
    let mut found = false;
    let mut accepts = true;
    for_each_class(fa, |_, fqn, c| {
        if found || !symbols::same_fqn(fqn, class_fqn) {
            return;
        }
        for m in methods(c) {
            if !fa.interner.resolve(m.name).eq_ignore_ascii_case(method) {
                continue;
            }
            found = true;
            accepts = !doc_has_no_named_arguments(m.doc.as_deref());
            break;
        }
    });
    found && accepts
}

fn class_accepts_named_arguments(
    fa: &FileAnalysis,
    class_fqn: &str,
    seen: &mut Vec<String>,
) -> bool {
    let key = class_fqn.trim_start_matches('\\').to_ascii_lowercase();
    if seen.contains(&key) {
        return true;
    }
    seen.push(key);
    let mut accepts = None;
    for_each_class(fa, |_, fqn, c| {
        if symbols::same_fqn(fqn, class_fqn) {
            accepts = Some(!doc_has_no_named_arguments(c.doc.as_deref()));
        }
    });
    if accepts != Some(true) {
        return false;
    }
    let Some(class) = fa.reflection.class(class_fqn) else {
        return false;
    };
    class
        .parents
        .iter()
        .filter_map(named_fqn)
        .all(|parent| class_accepts_named_arguments(fa, &parent, seen))
}

fn doc_has_no_named_arguments(doc: Option<&str>) -> bool {
    php_phpdoc::query::has_no_named_arguments(doc)
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
        let ExprKind::MethodCall {
            recv,
            nullsafe: true,
            ..
        } = &e.kind
        else {
            return;
        };
        let ty = fa.type_of(recv);
        if !type_is_definitely_non_null(&ty) {
            return;
        }
        out.push(
            Diagnostic::error(
                e.span,
                format!("Using nullsafe method call on non-nullable type {ty}. Use -> instead."),
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
        let ExprKind::New { class, .. } = &e.kind else {
            return;
        };
        let ExprKind::Name(_) = &class.kind else {
            return;
        };
        let Some(fqn) = named_fqn(&fa.type_of(e)) else {
            return;
        };
        let Some(cr) = fa.reflection.class(&fqn) else {
            return;
        };
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
                let ExprKind::StaticCall { class, method, .. } = &e.kind else {
                    continue;
                };
                let MemberName::Ident(name) = method else {
                    continue;
                };
                // Only `static::` (late static binding), spelled as a bare name.
                let ExprKind::Name(n) = &class.kind else {
                    continue;
                };
                if !matches!(scope.resolve_class(n), Resolution::LateStatic(ref w) if w == "static")
                {
                    continue;
                }
                let mname = fa.interner.resolve(*name);
                let Some(found) = fa.reflection.find_method(fqn, mname) else {
                    continue;
                };
                if found.member.magic || found.member.visibility != Visibility::Private {
                    continue;
                }
                let here = found.declaring_class.trim_start_matches('\\');
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!(
                            "Unsafe call to private method {here}::{mname}() through static::."
                        ),
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

/// `ConsistentConstructorRule` — when a parent (or ancestor) class declares
/// `@consistent-constructor`, a child constructor must stay compatible with the
/// constructor contract found there. Conservative: requires a fully-indexed
/// hierarchy and skips type comparisons whose answer depends on unresolved
/// classes/templates/self/static.
fn run_consistent_constructor(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |_, fqn, c| {
        if c.kind != ClassKind::Class || !fa.class_fully_known(fqn) {
            return;
        }
        let Some(class) = fa.reflection.class(fqn) else {
            return;
        };
        let Some(parent_fqn) = class.parents.iter().find_map(named_fqn) else {
            return;
        };
        let Some(proto) = find_consistent_constructor_prototype(fa, &parent_fqn, &mut Vec::new())
        else {
            return;
        };
        for (md, mr) in zip_methods(fa.interner, c, class) {
            if !mr.name.eq_ignore_ascii_case("__construct") {
                continue;
            }
            compare_constructor_signature(fa, &proto, fqn, mr, method_span(md), &mut out);
        }
    });
    out
}

#[derive(Clone)]
struct ConstructorPrototype {
    declaring_class: String,
    params: Vec<ParamReflection>,
    visibility: Visibility,
}

fn find_consistent_constructor_prototype(
    fa: &FileAnalysis,
    fqn: &str,
    seen: &mut Vec<String>,
) -> Option<ConstructorPrototype> {
    let key = fqn.trim_start_matches('\\').to_ascii_lowercase();
    if seen.contains(&key) {
        return None;
    }
    seen.push(key);
    let class = fa.reflection.class(fqn)?;
    if class.consistent_constructor {
        if let Some(found) = fa.reflection.find_method(&class.fqn, "__construct") {
            if !found.member.magic {
                return Some(ConstructorPrototype {
                    declaring_class: found.declaring_class.to_string(),
                    params: found.member.params.clone(),
                    visibility: found.member.visibility,
                });
            }
        }
        // PHPStan uses DummyConstructorReflection for a consistent class without
        // a constructor: public, no parameters.
        return Some(ConstructorPrototype {
            declaring_class: class.fqn.clone(),
            params: Vec::new(),
            visibility: Visibility::Public,
        });
    }
    for parent in &class.parents {
        if let Some(parent_fqn) = named_fqn(parent) {
            if let Some(proto) = find_consistent_constructor_prototype(fa, &parent_fqn, seen) {
                return Some(proto);
            }
        }
    }
    None
}

fn compare_constructor_signature(
    fa: &FileAnalysis,
    proto: &ConstructorPrototype,
    child_fqn: &str,
    method: &MethodReflection,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    compare_constructor_params(fa, proto, child_fqn, method, span, out);
    compare_constructor_visibility(proto, child_fqn, method, span, out);
}

fn compare_constructor_params(
    fa: &FileAnalysis,
    proto: &ConstructorPrototype,
    child_fqn: &str,
    method: &MethodReflection,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    let child = child_fqn.trim_start_matches('\\');
    let parent = proto.declaring_class.trim_start_matches('\\');
    let mname = &method.name;
    let pname = "__construct";
    let mut last_proto_idx: Option<usize> = None;
    let mut prototype_after_variadic = false;

    for (i, prototype_param) in proto.params.iter().enumerate() {
        last_proto_idx = Some(i);
        let Some(method_param) = method.params.get(i) else {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "Method {child}::{mname}() overrides method {parent}::{pname}() but misses parameter #{} ${}.",
                        i + 1,
                        prototype_param.name
                    ),
                )
                .with_code("parameter.missing"),
            );
            continue;
        };

        if !prototype_param.by_ref && method_param.by_ref {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "Parameter #{} ${} of method {child}::{mname}() is passed by reference but parameter #{} ${} of method {parent}::{pname}() is not passed by reference.",
                        i + 1,
                        method_param.name,
                        i + 1,
                        prototype_param.name
                    ),
                )
                .with_code("parameter.byRef"),
            );
        } else if prototype_param.by_ref && !method_param.by_ref {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "Parameter #{} ${} of method {child}::{mname}() is not passed by reference but parameter #{} ${} of method {parent}::{pname}() is passed by reference.",
                        i + 1,
                        method_param.name,
                        i + 1,
                        prototype_param.name
                    ),
                )
                .with_code("parameter.notByRef"),
            );
        }

        if prototype_param.variadic {
            prototype_after_variadic = true;
            if !method_param.variadic {
                if !method_param.optional {
                    if method.params.len() != i + 1 {
                        out.push(
                            Diagnostic::error(
                                span,
                                format!(
                                    "Parameter #{} ${} of method {child}::{mname}() is not optional.",
                                    i + 1,
                                    method_param.name
                                ),
                            )
                            .with_code("parameter.notOptional"),
                        );
                    } else {
                        out.push(
                            Diagnostic::error(
                                span,
                                format!(
                                    "Parameter #{} ${} of method {child}::{mname}() is not variadic but parameter #{} ${} of method {parent}::{pname}() is variadic.",
                                    i + 1,
                                    method_param.name,
                                    i + 1,
                                    prototype_param.name
                                ),
                            )
                            .with_code("parameter.notVariadic"),
                        );
                    }
                    continue;
                } else if method.params.len() == i + 1 {
                    out.push(
                        Diagnostic::error(
                            span,
                            format!(
                                "Parameter #{} ${} of method {child}::{mname}() is not variadic.",
                                i + 1,
                                method_param.name
                            ),
                        )
                        .with_code("parameter.notVariadic"),
                    );
                }
            }
        } else if method_param.variadic {
            for (j, remaining) in proto.params.iter().enumerate().skip(i) {
                if constructor_param_type_compatible(
                    fa,
                    &method_param.native_ty,
                    &remaining.native_ty,
                ) {
                    continue;
                }
                out.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "Parameter #{} ...${} ({}) of method {child}::{mname}() is not contravariant with parameter #{} ${} ({}) of method {parent}::{pname}().",
                            i + 1,
                            method_param.name,
                            method_param.native_ty,
                            j + 1,
                            remaining.name,
                            remaining.native_ty
                        ),
                    )
                    .with_code("method.childParameterType"),
                );
            }
            break;
        }

        if prototype_param.optional && !method_param.optional {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "Parameter #{} ${} of method {child}::{mname}() is required but parameter #{} ${} of method {parent}::{pname}() is optional.",
                        i + 1,
                        method_param.name,
                        i + 1,
                        prototype_param.name
                    ),
                )
                .with_code("parameter.notOptional"),
            );
        }

        if !constructor_param_type_compatible(
            fa,
            &method_param.native_ty,
            &prototype_param.native_ty,
        ) {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "Parameter #{} ${} ({}) of method {child}::{mname}() is not contravariant with parameter #{} ${} ({}) of method {parent}::{pname}().",
                        i + 1,
                        method_param.name,
                        method_param.native_ty,
                        i + 1,
                        prototype_param.name,
                        prototype_param.native_ty
                    ),
                )
                .with_code("method.childParameterType"),
            );
        }
    }

    let last_checked = last_proto_idx.map_or(0, |i| i + 1);
    for (j, method_param) in method.params.iter().enumerate().skip(last_checked) {
        if j == method.params.len() - 1 && prototype_after_variadic && !method_param.variadic {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "Parameter #{} ${} of method {child}::{mname}() is not variadic.",
                        j + 1,
                        method_param.name
                    ),
                )
                .with_code("parameter.notVariadic"),
            );
            continue;
        }
        if method_param.optional {
            continue;
        }
        out.push(
            Diagnostic::error(
                span,
                format!(
                    "Parameter #{} ${} of method {child}::{mname}() is not optional.",
                    j + 1,
                    method_param.name
                ),
            )
            .with_code("parameter.notOptional"),
        );
    }
}

fn compare_constructor_visibility(
    proto: &ConstructorPrototype,
    child_fqn: &str,
    method: &MethodReflection,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    if proto.visibility == Visibility::Private {
        return;
    }
    let child = child_fqn.trim_start_matches('\\');
    let parent = proto.declaring_class.trim_start_matches('\\');
    let mname = &method.name;
    if proto.visibility == Visibility::Public && method.visibility != Visibility::Public {
        let lead = if method.visibility == Visibility::Private {
            "Private"
        } else {
            "Protected"
        };
        out.push(
            Diagnostic::error(
                span,
                format!(
                    "{lead} method {child}::{mname}() overriding public method {parent}::__construct() should also be public."
                ),
            )
            .with_code("method.visibility"),
        );
    } else if method.visibility == Visibility::Private {
        out.push(
            Diagnostic::error(
                span,
                format!(
                    "Private method {child}::{mname}() overriding protected method {parent}::__construct() should be protected or public."
                ),
            )
            .with_code("method.visibility"),
        );
    }
}

fn constructor_param_type_compatible(
    fa: &FileAnalysis,
    method_type: &Type,
    prototype_type: &Type,
) -> bool {
    if !constructor_type_decidable(fa, method_type)
        || !constructor_type_decidable(fa, prototype_type)
    {
        return true;
    }
    php_infer::is_assignable(fa.reflection, prototype_type, method_type)
}

fn constructor_type_decidable(fa: &FileAnalysis, ty: &Type) -> bool {
    match ty {
        Type::Mixed
        | Type::Unknown(_)
        | Type::SelfType
        | Type::StaticType
        | Type::Parent
        | Type::TemplateVar(_)
        | Type::Conditional { .. } => false,
        Type::Named { fqn, args } => {
            fa.class_fully_known(fqn) && args.iter().all(|a| constructor_type_decidable(fa, a))
        }
        Type::Nullable(inner) | Type::List(inner) | Type::ClassString(Some(inner)) => {
            constructor_type_decidable(fa, inner)
        }
        Type::Union(parts) | Type::Intersection(parts) => {
            parts.iter().all(|p| constructor_type_decidable(fa, p))
        }
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            constructor_type_decidable(fa, &kv.0) && constructor_type_decidable(fa, &kv.1)
        }
        Type::Callable(Some(sig)) => {
            sig.params.iter().all(|p| constructor_type_decidable(fa, p))
                && constructor_type_decidable(fa, &sig.ret)
        }
        _ => true,
    }
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
        let Some(class) = fa.reflection.class(fqn) else {
            return;
        };
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
                if pr.ty.is_mixed() {
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
                if !compat::value_mismatch(fa, &given, Some(&given), &pr.ty, &pr.native_ty) {
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
    php_phpdoc::query::has_base_tag(c.doc.as_deref(), &["consistent-constructor"])
}

// ---------------------------------------------------------------------------
// Call-as-statement to a pure method (CallToMethodStatementWithoutSideEffectsRule
// / CallToStaticMethodStatementWithoutSideEffectsRule) — method/staticMethod.resultUnused
// ---------------------------------------------------------------------------

/// `$obj->m();` as a whole statement where `m` is a *pure* method (`@pure`/
/// `@phpstan-pure`): the return value is the only effect, so the statement is dead.
/// Conservative — fires only when the receiver pins to a known class and the
/// resolved method is annotated pure (never on `mixed`/unknown/magic).
fn run_method_result_unused(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for s in &fa.program.stmts {
        crate::rules::functions::stmt_level_calls(s, &mut |e| {
            let ExprKind::MethodCall { recv, method, .. } = &e.kind else {
                return;
            };
            let MemberName::Ident(name) = method else {
                return;
            };
            let Some(fqn) = named_fqn(&fa.type_of(recv)) else {
                return;
            };
            let mname = fa.interner.resolve(*name);
            let Some(found) = fa.reflection.find_method(&fqn, mname) else {
                return;
            };
            if let Some(d) = pure_call_diag(&found.member, &fqn, "method.resultUnused", e.span) {
                out.push(d);
            }
        });
    }
    out
}

/// `C::m();` as a whole statement where `m` is a *pure* static (or instance)
/// method. Class names resolved through the region scope (skips self/static/parent
/// and built-ins).
fn run_static_method_result_unused(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for s in region {
            crate::rules::functions::stmt_level_calls(s, &mut |e| {
                let ExprKind::StaticCall { class, method, .. } = &e.kind else {
                    return;
                };
                let MemberName::Ident(name) = method else {
                    return;
                };
                let ExprKind::Name(n) = &class.kind else {
                    return;
                };
                let fqn = match scope.resolve_class(n) {
                    Resolution::LateStatic(_) | Resolution::BuiltinType(_) => return,
                    r => match r.fqn() {
                        Some(f) => f.trim_start_matches('\\').to_string(),
                        None => return,
                    },
                };
                let mname = fa.interner.resolve(*name);
                let Some(found) = fa.reflection.find_method(&fqn, mname) else {
                    return;
                };
                if let Some(d) =
                    pure_call_diag(&found.member, &fqn, "staticMethod.resultUnused", e.span)
                {
                    out.push(d);
                }
            });
        }
    });
    out
}

/// Build the `*.resultUnused` diagnostic for a discarded call to `m`, if `m` is a
/// non-magic pure method that doesn't return `never`.
fn pure_call_diag(
    m: &MethodReflection,
    fqn: &str,
    code: &'static str,
    span: Span,
) -> Option<Diagnostic> {
    if m.magic || !m.pure || matches!(m.return_type, Type::Never) {
        return None;
    }
    let short = fqn.trim_start_matches('\\');
    let kind = if m.is_static {
        "static method"
    } else {
        "method"
    };
    Some(
        Diagnostic::error(
            span,
            format!(
                "Call to {kind} {short}::{}() on a separate line has no effect.",
                m.name
            ),
        )
        .with_code(code),
    )
}

// ---------------------------------------------------------------------------
// CallTo*MethodStatementWithNoDiscardRule
// ---------------------------------------------------------------------------

/// `$obj->m();` / `(void) $obj->m();` for methods declared with `#[NoDiscard]`.
///
/// Pipe-right first-class callables are treated as calls to the referenced
/// method, matching PHPStan. Standalone first-class callables remain clean.
fn run_method_no_discard(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.php_version.at_least(80500) {
        return Vec::new();
    }
    let mut out = Vec::new();
    for s in &fa.program.stmts {
        crate::rules::functions::stmt_level_calls(s, &mut |e| {
            let Some((call, in_void_cast, from_pipe)) = method_call_for_no_discard(e) else {
                return;
            };
            let ExprKind::MethodCall {
                recv, method, args, ..
            } = &call.kind
            else {
                return;
            };
            if !from_pipe && args.iter().any(|a| a.placeholder) {
                return;
            }
            let MemberName::Ident(name) = method else {
                return;
            };
            let Some(fqn) = named_fqn(&fa.type_of(recv)) else {
                return;
            };
            let mname = fa.interner.resolve(*name);
            let Some(found) = fa.reflection.find_method(&fqn, mname) else {
                return;
            };
            if let Some(d) = no_discard_method_diag(
                &found.member,
                found.declaring_class,
                "method",
                in_void_cast,
                e.span,
            ) {
                out.push(d);
            }
        });
    }
    out
}

/// `C::m();` / `(void) C::m();` for static methods declared with `#[NoDiscard]`.
fn run_static_method_no_discard(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.php_version.at_least(80500) {
        return Vec::new();
    }
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for s in region {
            crate::rules::functions::stmt_level_calls(s, &mut |e| {
                let Some((call, in_void_cast, from_pipe)) = static_method_call_for_no_discard(e)
                else {
                    return;
                };
                let ExprKind::StaticCall {
                    class,
                    method,
                    args,
                } = &call.kind
                else {
                    return;
                };
                if !from_pipe && args.iter().any(|a| a.placeholder) {
                    return;
                }
                let MemberName::Ident(name) = method else {
                    return;
                };
                let Some(fqn) = static_call_class_fqn_for_no_discard(fa, scope, class) else {
                    return;
                };
                let mname = fa.interner.resolve(*name);
                let Some(found) = fa.reflection.find_method(&fqn, mname) else {
                    return;
                };
                if let Some(d) = no_discard_method_diag(
                    &found.member,
                    found.declaring_class,
                    "staticMethod",
                    in_void_cast,
                    e.span,
                ) {
                    out.push(d);
                }
            });
        }
    });
    out
}

fn method_call_for_no_discard(e: &Expr) -> Option<(&Expr, bool, bool)> {
    let (e, in_void_cast) = match &e.kind {
        ExprKind::Cast {
            kind: CastKind::Void,
            expr,
        } => (peel_paren(expr), true),
        _ => (e, false),
    };
    let e = peel_paren(e);
    match &e.kind {
        ExprKind::MethodCall { .. } => Some((e, in_void_cast, false)),
        ExprKind::Binary {
            op: BinOp::Pipe,
            rhs,
            ..
        } => pipe_method_call_for_no_discard(rhs)
            .map(|(call, from_pipe)| (call, in_void_cast, from_pipe)),
        _ => None,
    }
}

fn static_method_call_for_no_discard(e: &Expr) -> Option<(&Expr, bool, bool)> {
    let (e, in_void_cast) = match &e.kind {
        ExprKind::Cast {
            kind: CastKind::Void,
            expr,
        } => (peel_paren(expr), true),
        _ => (e, false),
    };
    let e = peel_paren(e);
    match &e.kind {
        ExprKind::StaticCall { .. } => Some((e, in_void_cast, false)),
        ExprKind::Binary {
            op: BinOp::Pipe,
            rhs,
            ..
        } => pipe_static_method_call_for_no_discard(rhs)
            .map(|(call, from_pipe)| (call, in_void_cast, from_pipe)),
        _ => None,
    }
}

fn pipe_method_call_for_no_discard(rhs: &Expr) -> Option<(&Expr, bool)> {
    let rhs = peel_paren(rhs);
    match &rhs.kind {
        ExprKind::MethodCall { args, .. } if args.iter().any(|a| a.placeholder) => {
            Some((rhs, true))
        }
        ExprKind::ArrowFn(a)
            if matches!(&peel_paren(&a.body).kind, ExprKind::MethodCall { .. }) =>
        {
            Some((peel_paren(&a.body), false))
        }
        _ => None,
    }
}

fn pipe_static_method_call_for_no_discard(rhs: &Expr) -> Option<(&Expr, bool)> {
    let rhs = peel_paren(rhs);
    match &rhs.kind {
        ExprKind::StaticCall { args, .. } if args.iter().any(|a| a.placeholder) => {
            Some((rhs, true))
        }
        ExprKind::ArrowFn(a)
            if matches!(&peel_paren(&a.body).kind, ExprKind::StaticCall { .. }) =>
        {
            Some((peel_paren(&a.body), false))
        }
        _ => None,
    }
}

fn peel_paren(mut e: &Expr) -> &Expr {
    while let ExprKind::Paren(inner) = &e.kind {
        e = inner;
    }
    e
}

fn static_call_class_fqn_for_no_discard(
    fa: &FileAnalysis,
    scope: &Scope,
    class: &Expr,
) -> Option<String> {
    if let ExprKind::Name(n) = &class.kind {
        return match scope.resolve_class(n) {
            Resolution::LateStatic(_) | Resolution::BuiltinType(_) => None,
            r => r.fqn().map(|f| f.trim_start_matches('\\').to_string()),
        };
    }
    static_class_fqn_from_type(fa, &fa.type_of(class))
}

fn static_class_fqn_from_type(fa: &FileAnalysis, t: &Type) -> Option<String> {
    match t {
        Type::Named { fqn, .. } => Some(fqn.to_string()),
        Type::ClassString(Some(inner)) => static_class_fqn_from_type(fa, inner),
        Type::LiteralString(s) => fa.reflection.class(s).map(|c| c.fqn.clone()),
        Type::Nullable(inner) => static_class_fqn_from_type(fa, inner),
        _ => None,
    }
}

fn no_discard_method_diag(
    m: &MethodReflection,
    declaring_class: &str,
    code_base: &'static str,
    in_void_cast: bool,
    span: Span,
) -> Option<Diagnostic> {
    let short = declaring_class.trim_start_matches('\\');
    let kind = if m.is_static {
        "static method"
    } else {
        "method"
    };
    if in_void_cast {
        if m.must_use_return_value {
            return None;
        }
        let code = match code_base {
            "staticMethod" => "staticMethod.inVoidCast",
            _ => "method.inVoidCast",
        };
        return Some(
            Diagnostic::error(
                span,
                format!(
                    "Call to {kind} {short}::{}() in (void) cast but method allows discarding return value.",
                    m.name
                ),
            )
            .with_code(code),
        );
    }
    if !m.must_use_return_value {
        return None;
    }
    let code = match code_base {
        "staticMethod" => "staticMethod.resultDiscarded",
        _ => "method.resultDiscarded",
    };
    Some(
        Diagnostic::error(
            span,
            format!(
                "Call to {kind} {short}::{}() on a separate line discards return value.",
                m.name
            ),
        )
        .with_code(code),
    )
}

/// `MissingMethodReturn/ParameterTypehintRule` — the `missingType.iterableValue`
/// branch: a method param/return whose reflected (native ∪ PHPDoc) type is a bare
/// `array`/`iterable`. Disjoint from the no-type-at-all `missingType.*` checks.
fn run_missing_method_iterable_value(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            let StmtKind::Class(c) = &st.kind else {
                continue;
            };
            let Some(nm) = c.name else { continue };
            let fqn = scope.qualify(fa.interner.resolve(nm));
            let refl = fa.reflect_class(scope, &fqn, c);
            // phpstan inherits @param/@return from overridden parent/interface
            // methods. We don't model that, so we only check methods that can't
            // inherit: the class (and all its ancestors) must be fully known, and
            // the method must not override an ancestor method. Otherwise skip
            // (under-report) to stay false-positive-free.
            if !fa.class_fully_known(&fqn) {
                continue;
            }
            let ancestors: Vec<String> = refl
                .parents
                .iter()
                .chain(refl.interfaces.iter())
                .chain(refl.traits.iter())
                .filter_map(named_fqn)
                .collect();
            let short = fqn.trim_start_matches('\\');
            for m in &c.members {
                let Member::Method(md) = m else { continue };
                let mname = fa.interner.resolve(md.name);
                let Some(mr) = refl
                    .methods
                    .iter()
                    .find(|x| !x.magic && x.name.eq_ignore_ascii_case(mname))
                else {
                    continue;
                };
                // Overrides an ancestor method → its @param/@return may be inherited.
                if ancestors
                    .iter()
                    .any(|a| fa.reflection.find_method(a, mname).is_some())
                {
                    continue;
                }
                for (p, pr) in md.params.iter().zip(mr.params.iter()) {
                    if let Some(word) = crate::rules::functions::bare_iterable_word(&pr.ty) {
                        let pname = fa.interner.resolve(p.name);
                        out.push(
                            Diagnostic::error(
                                crate::rules::functions::p_span(p),
                                format!(
                                    "Method {short}::{mname}() has parameter ${pname} with no \
                                     value type specified in iterable type {word}."
                                ),
                            )
                            .with_code("missingType.iterableValue"),
                        );
                    }
                }
                if let Some(rt) = &md.return_type {
                    if let Some(word) = crate::rules::functions::bare_iterable_word(&mr.return_type)
                    {
                        out.push(
                            Diagnostic::error(
                                rt.span,
                                format!(
                                    "Method {short}::{mname}() return type has no value type \
                                     specified in iterable type {word}."
                                ),
                            )
                            .with_code("missingType.iterableValue"),
                        );
                    }
                }
            }
        }
    });
    out
}

fn run_missing_method_self_out_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa, |scope, class_fqn, c| {
        let class_short = class_fqn.trim_start_matches('\\');
        let class_templates = fa
            .reflection
            .class(class_fqn)
            .map(|r| r.templates.clone())
            .unwrap_or_default();
        for member in &c.members {
            let Member::Method(md) = member else { continue };
            let Some(doc) = md.doc.as_deref() else {
                continue;
            };
            let method_name = fa.interner.resolve(md.name);
            let span = method_span(md);
            for ty in self_out_doc_types(doc) {
                SelfOutDocCheck {
                    fa,
                    scope,
                    class_fqn,
                    class_short,
                    method_name,
                    class_templates: &class_templates,
                    span,
                    out: &mut out,
                }
                .check(&ty);
            }
        }
    });
    out
}

fn self_out_doc_types(doc_raw: &str) -> Vec<DocType> {
    php_phpdoc::parse_block(doc_raw)
        .tags
        .iter()
        .filter_map(|tag| {
            let base = tag
                .name
                .strip_prefix("phpstan-")
                .or_else(|| tag.name.strip_prefix("psalm-"))
                .unwrap_or(&tag.name);
            if base != "self-out" {
                return None;
            }
            php_phpdoc::parse_type_prefix(&tag.value).map(|(ty, _)| ty)
        })
        .collect()
}

struct SelfOutDocCheck<'a, 'b> {
    fa: &'a FileAnalysis<'a>,
    scope: &'a Scope,
    class_fqn: &'a str,
    class_short: &'a str,
    method_name: &'a str,
    class_templates: &'a [String],
    span: Span,
    out: &'b mut Vec<Diagnostic>,
}

impl SelfOutDocCheck<'_, '_> {
    fn check(&mut self, ty: &DocType) {
        let ctx = crate::missing_type::DocGenericContext {
            reflection: self.fa.reflection,
            scope: self.scope,
            class_fqn: Some(self.class_fqn),
            current_class_templates: self.class_templates,
            excluded_templates: &[],
            skip_traits: false,
        };
        for issue in crate::missing_type::check_doc_type(ctx, ty) {
            match issue {
                crate::missing_type::MissingTypeIssue::IterableValue { word } => {
                    self.out.push(
                        Diagnostic::error(
                            self.span,
                            format!(
                                "Method {}::{}() has PHPDoc tag @phpstan-self-out with no value type specified in iterable type {word}.",
                                self.class_short, self.method_name
                            ),
                        )
                        .with_code("missingType.iterableValue"),
                    );
                }
                crate::missing_type::MissingTypeIssue::GenericArgs { name, templates } => {
                    self.out.push(
                        Diagnostic::error(
                            self.span,
                            format!(
                                "Method {}::{}() has PHPDoc tag @phpstan-self-out with generic class {name} but does not specify its types: {templates}",
                                self.class_short, self.method_name
                            ),
                        )
                        .with_code("missingType.generics"),
                    );
                }
                crate::missing_type::MissingTypeIssue::CallableSignature => {
                    self.out.push(
                        Diagnostic::error(
                            self.span,
                            format!(
                                "Method {}::{}() has PHPDoc tag @phpstan-self-out with no signature specified for callable.",
                                self.class_short, self.method_name
                            ),
                        )
                        .with_code("missingType.callable"),
                    );
                }
            }
        }
    }
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "method.resultUnused",
        level: 4,
        run: run_method_result_unused,
    },
    RuleEntry {
        name: "method.noDiscard",
        level: 0,
        run: run_method_no_discard,
    },
    RuleEntry {
        name: "missingType.iterableValue",
        level: 6,
        run: run_missing_method_iterable_value,
    },
    RuleEntry {
        name: "missingType.selfOut",
        level: 6,
        run: run_missing_method_self_out_type,
    },
    RuleEntry {
        name: "staticMethod.resultUnused",
        level: 4,
        run: run_static_method_result_unused,
    },
    RuleEntry {
        name: "staticMethod.noDiscard",
        level: 0,
        run: run_static_method_no_discard,
    },
    RuleEntry {
        name: "method.abstract",
        level: 0,
        run: run_abstract_in_non_abstract,
    },
    RuleEntry {
        name: "method.abstractPrivate",
        level: 0,
        run: run_abstract_private,
    },
    RuleEntry {
        name: "method.nonAbstract",
        level: 0,
        run: run_abstract_body,
    },
    RuleEntry {
        name: "method.finalPrivate",
        level: 0,
        run: run_final_private,
    },
    RuleEntry {
        name: "method.visibilityInInterface",
        level: 0,
        run: run_visibility_in_interface,
    },
    RuleEntry {
        name: "constructor.returnType",
        level: 0,
        run: run_constructor_return_type,
    },
    RuleEntry {
        name: "method.staticConstructor",
        level: 0,
        run: run_constructor_modifiers,
    },
    RuleEntry {
        name: "method.duplicateParameter",
        level: 0,
        run: run_duplicate_parameter,
    },
    RuleEntry {
        name: "method.missingImplementation",
        level: 0,
        run: run_missing_implementation,
    },
    RuleEntry {
        name: "class.serializable",
        level: 0,
        run: run_serializable_methods,
    },
    RuleEntry {
        name: "method.attributeTarget",
        level: 0,
        run: run_method_attribute_target,
    },
    RuleEntry {
        name: "method.overriding",
        level: 0,
        run: run_overriding_method,
    },
    RuleEntry {
        name: "method.callExistence",
        level: 0,
        run: run_call_existence,
    },
    RuleEntry {
        name: "method.callTyped",
        level: 0,
        run: run_call_methods_typed,
    },
    RuleEntry {
        name: "method.nullableAccess",
        level: 8,
        run: run_nullable_method_access,
    },
    RuleEntry {
        name: "method.unionAccess",
        level: 7,
        run: run_union_method_access,
    },
    RuleEntry {
        name: "staticMethod.callNamed",
        level: 0,
        run: run_static_call_named,
    },
    RuleEntry {
        name: "argument.parameterRenamedInSubtype",
        level: 0,
        run: run_renamed_named_argument_call,
    },
    RuleEntry {
        name: "consistentConstructor.private",
        level: 0,
        run: run_consistent_constructor_private,
    },
    RuleEntry {
        name: "consistentConstructor",
        level: 0,
        run: run_consistent_constructor,
    },
    RuleEntry {
        name: "staticClassAccess.privateMethod",
        level: 2,
        run: run_private_through_static,
    },
    RuleEntry {
        name: "parameter.defaultValue",
        level: 2,
        run: run_incompatible_default_param,
    },
    RuleEntry {
        name: "nullsafe.neverNull",
        level: 4,
        run: run_nullsafe_never_null,
    },
    RuleEntry {
        name: "new.resultUnused",
        level: 4,
        run: run_new_result_unused,
    },
    RuleEntry {
        name: "argument.type",
        level: 5,
        run: run_method_argument_types,
    },
    RuleEntry {
        name: "missingType.return",
        level: 6,
        run: run_missing_return_type,
    },
    RuleEntry {
        name: "missingType.parameter",
        level: 6,
        run: run_missing_param_type,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{codes, codes_version, codes_with};
    use crate::PhpVersion;

    // --- missingType.iterableValue ---

    #[test]
    fn bare_array_param_flagged() {
        let src = r#"<?php class C { public function m(array $a): void {} }"#;
        assert_eq!(
            codes(src, run_missing_method_iterable_value),
            ["missingType.iterableValue"]
        );
    }

    #[test]
    fn typed_array_param_via_phpdoc_clean() {
        let src = r#"<?php class C { /** @param array<string, mixed> $a */ public function m(array $a): void {} }"#;
        assert!(
            codes(src, run_missing_method_iterable_value).is_empty(),
            "{:?}",
            codes(src, run_missing_method_iterable_value)
        );
    }

    #[test]
    fn typed_array_param_multiline_with_description_clean() {
        let src = "<?php class C {\n    /**\n     * @param array<string, mixed> $attributes Additional attributes\n     */\n    public function m(array $attributes = []): void {}\n}";
        assert!(
            codes(src, run_missing_method_iterable_value).is_empty(),
            "{:?}",
            codes(src, run_missing_method_iterable_value)
        );
    }

    #[test]
    fn self_out_bare_array_arg_is_flagged() {
        let src = r#"<?php
            /** @template T */
            class Foo {
                /** @phpstan-self-out self<array> */
                public function doFoo(): void {}
            }
        "#;
        assert_eq!(
            codes(src, run_missing_method_self_out_type),
            ["missingType.iterableValue"]
        );
    }

    #[test]
    fn self_out_generic_class_without_args_is_flagged() {
        let src = r#"<?php
            /** @template T */
            class Foo {
                /** @phpstan-self-out self */
                public function doFoo(): void {}
            }
        "#;
        assert_eq!(
            codes(src, run_missing_method_self_out_type),
            ["missingType.generics"]
        );
    }

    #[test]
    fn self_out_callable_without_signature_is_flagged() {
        let src = r#"<?php
            /** @template T */
            class Foo {
                /** @phpstan-self-out Foo<int>&callable */
                public function doFoo(): void {}
            }
        "#;
        assert_eq!(
            codes(src, run_missing_method_self_out_type),
            ["missingType.callable"]
        );
    }

    // --- method/staticMethod.resultUnused (pure call discarded) ---------

    #[test]
    fn pure_method_call_discarded_is_flagged() {
        let src = r#"<?php
            class C {
                /** @pure */
                public function val(): int { return 1; }
            }
            function f(C $c) { $c->val(); }"#;
        assert_eq!(
            codes(src, run_method_result_unused),
            ["method.resultUnused"]
        );
    }

    #[test]
    fn pure_method_call_used_is_clean() {
        let src = r#"<?php
            class C {
                /** @pure */
                public function val(): int { return 1; }
            }
            function f(C $c) { $x = $c->val(); }"#;
        assert!(codes(src, run_method_result_unused).is_empty());
    }

    #[test]
    fn impure_method_call_discarded_is_clean() {
        // No @pure annotation → assume side effects → not flagged.
        let src = r#"<?php
            class C {
                public function doThing(): int { return 1; }
            }
            function f(C $c) { $c->doThing(); }"#;
        assert!(codes(src, run_method_result_unused).is_empty());
    }

    #[test]
    fn pure_static_method_call_discarded_is_flagged() {
        let src = r#"<?php
            class C {
                /** @pure */
                public static function val(): int { return 1; }
            }
            function f() { C::val(); }"#;
        assert_eq!(
            codes(src, run_static_method_result_unused),
            ["staticMethod.resultUnused"]
        );
    }

    #[test]
    fn impure_annotated_pure_is_not_pure() {
        let src = r#"<?php
            class C {
                /**
                 * @pure
                 * @phpstan-impure
                 */
                public function val(): int { return 1; }
            }
            function f(C $c) { $c->val(); }"#;
        assert!(codes(src, run_method_result_unused).is_empty());
    }

    #[test]
    fn nodiscard_method_statement_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = r#"<?php
            class C { #[NoDiscard] public function val(): int { return 1; } }
            function f(C $c): void { $c->val(); }"#;
        assert_eq!(
            codes_version(src, run_method_no_discard, v85),
            ["method.resultDiscarded"]
        );
    }

    #[test]
    fn nodiscard_method_statement_is_version_gated() {
        let src = r#"<?php
            class C { #[NoDiscard] public function val(): int { return 1; } }
            function f(C $c): void { $c->val(); }"#;
        assert!(codes(src, run_method_no_discard).is_empty());
    }

    #[test]
    fn void_cast_plain_method_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = r#"<?php
            class C { public function val(): int { return 1; } }
            function f(C $c): void { (void) $c->val(); }"#;
        assert_eq!(
            codes_version(src, run_method_no_discard, v85),
            ["method.inVoidCast"]
        );
    }

    #[test]
    fn standalone_first_class_callable_nodiscard_method_is_clean_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = r#"<?php
            class C { #[NoDiscard] public function val(): int { return 1; } }
            function f(C $c): void { $c->val(...); }"#;
        assert!(codes_version(src, run_method_no_discard, v85).is_empty());
    }

    #[test]
    fn pipe_into_nodiscard_method_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = r#"<?php
            class C { #[NoDiscard] public function val(int $i): int { return $i; } }
            function f(C $c): void { 5 |> $c->val(...); }"#;
        assert_eq!(
            codes_version(src, run_method_no_discard, v85),
            ["method.resultDiscarded"]
        );
    }

    #[test]
    fn void_cast_pipe_into_plain_method_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = r#"<?php
            class C { public function val(int $i): int { return $i; } }
            function f(C $c): void { (void) (5 |> $c->val(...)); }"#;
        assert_eq!(
            codes_version(src, run_method_no_discard, v85),
            ["method.inVoidCast"]
        );
    }

    #[test]
    fn nodiscard_static_method_statement_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = r#"<?php
            class C { #[NoDiscard] public static function val(): int { return 1; } }
            function f(): void { C::val(); }"#;
        assert_eq!(
            codes_version(src, run_static_method_no_discard, v85),
            ["staticMethod.resultDiscarded"]
        );
    }

    #[test]
    fn void_cast_plain_static_method_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = r#"<?php
            class C { public static function val(): int { return 1; } }
            function f(): void { (void) C::val(); }"#;
        assert_eq!(
            codes_version(src, run_static_method_no_discard, v85),
            ["staticMethod.inVoidCast"]
        );
    }

    #[test]
    fn standalone_first_class_callable_nodiscard_static_method_is_clean_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = r#"<?php
            class C { #[NoDiscard] public static function val(): int { return 1; } }
            function f(): void { C::val(...); }"#;
        assert!(codes_version(src, run_static_method_no_discard, v85).is_empty());
    }

    #[test]
    fn pipe_into_nodiscard_static_method_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = r#"<?php
            class C { #[NoDiscard] public static function val(int $i): int { return $i; } }
            function f(): void { 5 |> C::val(...); }"#;
        assert_eq!(
            codes_version(src, run_static_method_no_discard, v85),
            ["staticMethod.resultDiscarded"]
        );
    }

    #[test]
    fn void_cast_pipe_into_plain_static_method_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = r#"<?php
            class C { public static function val(int $i): int { return $i; } }
            function f(): void { (void) (5 |> C::val(...)); }"#;
        assert_eq!(
            codes_version(src, run_static_method_no_discard, v85),
            ["staticMethod.inVoidCast"]
        );
    }

    #[test]
    fn pipe_arrow_into_nodiscard_static_method_is_flagged_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = r#"<?php
            class C { #[NoDiscard] public static function val(int $i): int { return $i; } }
            function f(): void { 5 |> (fn($x) => C::val($x)); }"#;
        assert_eq!(
            codes_version(src, run_static_method_no_discard, v85),
            ["staticMethod.resultDiscarded"]
        );
    }

    #[test]
    fn dynamic_class_static_method_is_flagged_when_class_string_is_exact_on_php85() {
        let v85 = PhpVersion::parse("8.5").unwrap();
        let src = r#"<?php
            class C { #[NoDiscard] public static function val(): int { return 1; } }
            function f(): void { $class = C::class; $class::val(); }"#;
        assert_eq!(
            codes_version(src, run_static_method_no_discard, v85),
            ["staticMethod.resultDiscarded"]
        );
    }

    #[test]
    fn abstract_method_in_non_abstract_class() {
        let src = "<?php class C { abstract function f(); }";
        assert_eq!(
            codes(src, run_abstract_in_non_abstract),
            ["method.abstract"]
        );
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
        assert_eq!(
            codes(src, run_visibility_in_interface),
            ["method.visibility"]
        );
    }

    #[test]
    fn public_interface_method_clean() {
        let src = "<?php interface I { public function f(); }";
        assert!(codes(src, run_visibility_in_interface).is_empty());
    }

    #[test]
    fn constructor_with_return_type_flagged() {
        let src = "<?php class C { public function __construct(): void {} }";
        assert_eq!(
            codes(src, run_constructor_return_type),
            ["constructor.returnType"]
        );
    }

    #[test]
    fn constructor_without_return_type_clean() {
        let src = "<?php class C { public function __construct() {} }";
        assert!(codes(src, run_constructor_return_type).is_empty());
    }

    #[test]
    fn static_constructor_flagged() {
        let src = "<?php class C { public static function __construct() {} }";
        assert_eq!(
            codes(src, run_constructor_modifiers),
            ["method.staticConstructor"]
        );
    }

    #[test]
    fn duplicate_parameter_flagged() {
        let src = "<?php class C { public function f($a, $a) {} }";
        assert_eq!(
            codes(src, run_duplicate_parameter),
            ["method.duplicateParameter"]
        );
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
        assert_eq!(
            codes(src, run_missing_implementation),
            ["method.missingImplementation"]
        );
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
    fn covariant_method_return_override_is_clean() {
        let src = "<?php
            class Base { public function f(): int|float { return 1; } }
            class C extends Base { public function f(): int { return 1; } }";
        assert!(codes(src, run_overriding_method).is_empty());
    }

    #[test]
    fn incompatible_method_return_override_is_flagged() {
        let src = "<?php
            class Base { public function f(): int { return 1; } }
            class C extends Base { public function f(): string { return 'x'; } }";
        assert!(codes(src, run_overriding_method).contains(&"method.childReturnType"));
    }

    #[test]
    fn contravariant_method_parameter_override_is_clean() {
        let src = "<?php
            class Base { public function f(int $x): void {} }
            class C extends Base { public function f(int|float $x): void {} }";
        assert!(codes(src, run_overriding_method).is_empty());
    }

    #[test]
    fn constructor_has_no_prototype() {
        // PHP exempts __construct from LSP entirely: a child constructor may
        // freely change the signature AND narrow visibility (singletons).
        let src = "<?php
            class Base { public function __construct(array $attributes = []) {} }
            class C extends Base {
                protected function __construct(int $x) { parent::__construct(); }
            }";
        assert!(
            codes(src, run_overriding_method).is_empty(),
            "constructor signature/visibility must not be prototype-checked"
        );
    }

    #[test]
    fn final_parent_constructor_override_is_still_reported() {
        let src = "<?php
            class Base { final public function __construct() {} }
            class C extends Base { public function __construct() {} }";
        assert!(codes(src, run_overriding_method).contains(&"method.parentMethodFinal"));
    }

    #[test]
    fn narrowed_method_parameter_override_is_flagged() {
        let src = "<?php
            class Base { public function f(string $x): void {} }
            class C extends Base { public function f(int $x): void {} }";
        assert!(codes(src, run_overriding_method).contains(&"method.childParameterType"));
    }

    #[test]
    fn maybe_method_parameter_override_waits_for_report_maybes() {
        let src = "<?php
            class Base { public function f(int|string $x): void {} }
            class C extends Base { public function f(int $x): void {} }";
        assert!(codes_with(src, run_overriding_method, |fa| {
            fa.report_maybes = false;
        })
        .is_empty());
        assert!(codes(src, run_overriding_method).contains(&"method.childParameterType"));
    }

    #[test]
    fn explicit_mixed_method_return_override_waits_for_level_9() {
        let src = "<?php
            class Base { public function f(): int { return 1; } }
            class C extends Base { public function f(): mixed { return 1; } }";
        assert!(codes_with(src, run_overriding_method, |fa| {
            fa.check_explicit_mixed = false;
            fa.check_implicit_mixed = false;
        })
        .is_empty());
        assert!(codes_with(src, run_overriding_method, |fa| {
            fa.check_implicit_mixed = false;
        })
        .contains(&"method.childReturnType"));
    }

    #[test]
    fn implicit_mixed_method_return_override_waits_for_max() {
        let src = "<?php
            class Base { public function f(): int { return 1; } }
            class C extends Base { public function f() { return 1; } }";
        assert!(codes_with(src, run_overriding_method, |fa| {
            fa.check_implicit_mixed = false;
        })
        .is_empty());
        assert!(codes(src, run_overriding_method).contains(&"method.childReturnType"));
    }

    #[test]
    fn call_to_undefined_this_method_flagged() {
        let src =
            "<?php class C { public function a() { $this->missing(); } public function b() {} }";
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
        let src =
            "<?php class C { /** @return $this */ public function chain() { return $this; } }";
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
        assert_eq!(
            codes(src, run_missing_param_type),
            ["missingType.parameter"]
        );
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
    fn undefined_method_inside_closure_body_is_flagged() {
        let src = "<?php class C {} function f(): void { $c = new C(); $cb = function () use ($c): void { $c->missing(); }; }";
        assert!(codes(src, run_call_methods_typed).contains(&"method.notFound"));
    }

    #[test]
    fn undefined_method_inside_array_map_callback_is_flagged() {
        let src = r#"<?php
            class User {}
            /** @param list<User> $users */
            function f(array $users): void {
                array_map(fn($u) => $u->missing(), $users);
            }
        "#;
        assert!(codes(src, run_call_methods_typed).contains(&"method.notFound"));
    }

    #[test]
    fn undefined_method_inside_generator_foreach_is_flagged() {
        let src = r#"<?php
            class User {}
            /** @return \Generator<int, User, void, void> */
            function users(): \Generator { yield new User(); }
            function f(): void {
                foreach (users() as $u) {
                    $u->missing();
                }
            }
        "#;
        assert!(codes(src, run_call_methods_typed).contains(&"method.notFound"));
    }

    #[test]
    fn undefined_method_on_array_map_result_is_flagged() {
        let src = r#"<?php
            class Child {}
            class User { public function child(): Child {} }
            /** @param list<User> $users */
            function f(array $users): void {
                $children = array_map(fn(User $u) => $u->child(), $users);
                $children[0]->missing();
            }
        "#;
        assert!(codes(src, run_call_methods_typed).contains(&"method.notFound"));
    }

    #[test]
    fn undefined_method_on_array_map_method_callback_result_is_flagged() {
        let src = r#"<?php
            class Child {}
            class User {}
            class Factory { public function make(User $u): Child {} }
            /** @param list<User> $users */
            function f(Factory $factory, array $users): void {
                $children = array_map([$factory, 'make'], $users);
                $children[0]->missing();
            }
        "#;
        assert!(codes(src, run_call_methods_typed).contains(&"method.notFound"));
    }

    #[test]
    fn undefined_method_inside_collection_map_callback_is_flagged() {
        let src = r#"<?php
            class User {}
            /** @template T */
            class Collection {
                public function map(callable $callback) {}
            }
            /** @param Collection<User> $users */
            function f(Collection $users): void {
                $users->map(fn($u) => $u->missing());
            }
        "#;
        assert!(codes(src, run_call_methods_typed).contains(&"method.notFound"));
    }

    #[test]
    fn undefined_method_on_collection_map_result_is_flagged() {
        let src = r#"<?php
            class Child {}
            class User { public function child(): Child {} }
            /** @template T */
            class Collection {
                /** @return T */
                public function first() {}
                public function map(callable $callback) {}
            }
            /** @param Collection<User> $users */
            function f(Collection $users): void {
                $children = $users->map(fn($u) => $u->child());
                $children->first()->missing();
            }
        "#;
        assert!(codes(src, run_call_methods_typed).contains(&"method.notFound"));
    }

    #[test]
    fn existing_method_on_typed_local_clean() {
        let src = "<?php class C { public function a(): void {} } function f(): void { $c = new C(); $c->a(); }";
        assert!(codes(src, run_call_methods_typed).is_empty());
    }

    #[test]
    fn abstract_receiver_with_final_leaf_methods_is_clean() {
        let src = r#"<?php
            abstract class Number {}
            final class IntegerNumber extends Number { public function plus(Number $n): Number { return $this; } }
            final class DecimalNumber extends Number { public function plus(Number $n): Number { return $this; } }
            function add(Number $a, Number $b): Number {
                if ($a instanceof IntegerNumber) { return $a->plus($b); }
                if ($a instanceof DecimalNumber) { return $a->plus($b); }
                return $a->plus($b);
            }
        "#;
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

    #[test]
    fn nullable_method_call_is_flagged_at_strict_level() {
        let src =
            "<?php class C { public function ok(): void {} } function f(?C $c): void { $c->ok(); }";
        assert_eq!(codes(src, run_nullable_method_access), ["method.nonObject"]);
    }

    #[test]
    fn nullsafe_method_call_on_nullable_is_clean() {
        let src = "<?php class C { public function ok(): void {} } function f(?C $c): void { $c?->ok(); }";
        assert!(codes(src, run_nullable_method_access).is_empty());
    }

    #[test]
    fn narrowed_nullable_method_call_is_clean() {
        let src = "<?php class C { public function ok(): void {} } function f(?C $c): void { if ($c === null) { return; } $c->ok(); }";
        assert!(codes(src, run_nullable_method_access).is_empty());
    }

    #[test]
    fn nullable_method_call_suppresses_not_found_branch() {
        let src = "<?php class C {} function f(?C $c): void { $c->missing(); }";
        assert!(codes(src, run_call_methods_typed).is_empty());
    }

    #[test]
    fn union_method_call_missing_on_one_arm_is_flagged() {
        let src = "<?php class A { public function ok(): void {} } class B {} \
            /** @param A|B $x */ function f($x): void { $x->ok(); }";
        assert_eq!(codes(src, run_union_method_access), ["method.notFound"]);
    }

    #[test]
    fn union_method_call_present_on_all_arms_is_clean() {
        let src = "<?php class A { public function ok(): void {} } class B { public function ok(): void {} } \
            /** @param A|B $x */ function f($x): void { $x->ok(); }";
        assert!(codes(src, run_union_method_access).is_empty());
    }

    #[test]
    fn nullable_union_method_call_is_left_to_nullable_rule() {
        let src = "<?php class A { public function ok(): void {} } \
            /** @param A|null $x */ function f($x): void { $x->ok(); }";
        assert!(codes(src, run_union_method_access).is_empty());
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
        let src =
            "<?php class C { public function a(): void {} } function f(?C $c): void { $c?->a(); }";
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
        let src =
            "<?php class C { public function __construct() {} } function f(): void { new C(); }";
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
        let src =
            "<?php /** @consistent-constructor */ class C { private function __construct() {} }";
        assert!(codes(src, run_consistent_constructor_private)
            .contains(&"consistentConstructor.private"));
    }

    #[test]
    fn public_constructor_with_consistent_tag_clean() {
        let src =
            "<?php /** @consistent-constructor */ class C { public function __construct() {} }";
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

    // --- ConsistentConstructorRule ---------------------------------------

    #[test]
    fn consistent_constructor_missing_param_is_flagged() {
        let src = r#"<?php
            /** @phpstan-consistent-constructor */
            class Base { public function __construct(int $id) {} }
            class Child extends Base { public function __construct() {} }"#;
        assert_eq!(
            codes(src, run_consistent_constructor),
            ["parameter.missing"]
        );
    }

    #[test]
    fn consistent_constructor_extra_required_param_is_flagged_for_dummy_parent() {
        let src = r#"<?php
            /** @phpstan-consistent-constructor */
            class Base {}
            class Child extends Base { public function __construct(int $id) {} }"#;
        assert_eq!(
            codes(src, run_consistent_constructor),
            ["parameter.notOptional"]
        );
    }

    #[test]
    fn consistent_constructor_type_mismatch_is_flagged() {
        let src = r#"<?php
            /** @phpstan-consistent-constructor */
            class Base { public function __construct(int $id) {} }
            class Child extends Base { public function __construct(string $id) {} }"#;
        assert_eq!(
            codes(src, run_consistent_constructor),
            ["method.childParameterType"]
        );
    }

    #[test]
    fn consistent_constructor_visibility_narrowing_is_flagged() {
        let src = r#"<?php
            /** @consistent-constructor */
            class Base { public function __construct() {} }
            class Child extends Base { protected function __construct() {} }"#;
        assert_eq!(
            codes(src, run_consistent_constructor),
            ["method.visibility"]
        );
    }

    #[test]
    fn unmarked_parent_constructor_is_clean_for_consistency_rule() {
        let src = r#"<?php
            class Base { public function __construct(int $id) {} }
            class Child extends Base { public function __construct() {} }"#;
        assert!(codes(src, run_consistent_constructor).is_empty());
    }

    // --- MethodCallWithPossiblyRenamedNamedArgumentRule ------------------

    #[test]
    fn named_argument_renamed_in_subtype_is_flagged_on_parameter_receiver() {
        let src = r#"<?php
            class Base { public function send($payload): void {} }
            class Child extends Base { public function send($data): void {} }
            function f(Base $b): void { $b->send(payload: 1); }"#;
        assert_eq!(
            codes(src, run_renamed_named_argument_call),
            ["argument.parameterRenamedInSubtype"]
        );
    }

    #[test]
    fn renamed_named_argument_rule_skips_direct_new_receiver() {
        let src = r#"<?php
            class Base { public function send($payload): void {} }
            class Child extends Base { public function send($data): void {} }
            function f(): void { (new Base())->send(payload: 1); }"#;
        assert!(codes(src, run_renamed_named_argument_call).is_empty());
    }

    #[test]
    fn renamed_named_argument_rule_skips_no_named_arguments_doc() {
        let src = r#"<?php
            /** @no-named-arguments */
            class Base { public function send($payload): void {} }
            class Child extends Base { public function send($data): void {} }
            function f(Base $b): void { $b->send(payload: 1); }"#;
        assert!(codes(src, run_renamed_named_argument_call).is_empty());
    }

    #[test]
    fn same_parameter_name_in_subtype_is_clean_for_named_argument_rule() {
        let src = r#"<?php
            class Base { public function send($payload): void {} }
            class Child extends Base { public function send($payload): void {} }
            function f(Base $b): void { $b->send(payload: 1); }"#;
        assert!(codes(src, run_renamed_named_argument_call).is_empty());
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
