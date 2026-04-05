//! phpstan category **Classes** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Classes/` — 37 rule(s) at level(s) 0,1,2,4.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to `RULES`
//! (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented here (all level 0 — structural / name-resolution only):
//! - `unknown-symbol` — consolidated existence check (class/function/constant).
//! - **InstantiationRule** (`new.interface`/`new.trait`/`new.enum`/`new.abstract`)
//!   — `new X` where `X` is an interface/trait/enum/abstract class.
//! - **InstantiationCallableRule** (`callable.notSupported`) — `new X(...)`.
//! - **NewStaticRule** (`new.static`) — `new static()` in a non-final class.
//! - **ExistingClassInClassExtendsRule** (`class.extendsInterface`/`…Trait`/
//!   `…Enum`/`…Final`) — a class extends the wrong kind / a final class.
//! - **ExistingClassesInClassImplementsRule** (`classImplements.class`/`…trait`/
//!   `…enum`) — `implements` a non-interface.
//! - **ExistingClassesInInterfaceExtendsRule** (`interfaceExtends.class`/`…trait`/
//!   `…enum`) — an interface `extends` a non-interface.
//! - **ExistingClassInTraitUseRule** (`traitUse.class`/`…interface`/`…enum`,
//!   `interface.traitUse`) — `use` of a non-trait / `use` inside an interface.
//! - **ExistingClassInInstanceOfRule** (`instanceof.trait`/`…enum`) — RHS of
//!   `instanceof` is a trait/enum.
//! - **EnumSanityRule** (`enum.constructor`/`…destructor`/`…magicMethod`/
//!   `…methodRedeclaration`/`…backingType`/`…caseWithValue`/`…missingCase`).
//! - **DuplicateDeclarationRule** (`<kind>.duplicateMethod`/`…duplicateProperty`/
//!   `…duplicateConstant`/`…duplicateEnumCase`) — redeclared members in a class.
//! - **DuplicateClassDeclarationRule** (`<kind>.duplicate`) — a class-like
//!   declared more than once in the same file.
//! - **NonClassAttributeClassRule** (`attribute.<kind>`/`attribute.abstract`/
//!   `attribute.constructorNotPublic`) — `#[Attribute]` on a non-instantiable.
//! - **InvalidPromotedPropertiesRule** (`property.invalidPromoted`) — promoted
//!   properties outside a constructor / variadic promoted property.
//! - **ExistingClassesInEnumImplementsRule** (`enumImplements.class`/`…trait`/
//!   `…enum`) — an `enum` that `implements` a non-interface.
//! - **ClassConstantRule** (`outOfClass.self`/`…static`/`…parent`,
//!   `class.noParent`, `classConstant.onTrait`, `classConstant.notFound`,
//!   `classConstant.private`/`…protected`) — `Class::CONST` access checks.
//! - **AccessPrivateConstantThroughStaticRule**
//!   (`staticClassAccess.privateConstant`) — `static::PRIVATE_CONST` in a
//!   non-final class.
//! - **MixinRule** (`mixin.nonObject`/`mixin.trait`) — a `@mixin` PHPDoc tag
//!   naming a non-object / a trait.
//! - **NewStaticInAbstractClassStaticMethodRule**
//!   (`new.staticInAbstractClassStaticMethod`) — `new static()` in a static
//!   method of an abstract class.
//!
//! Deferred (need richer reflection / type-system bits we don't model yet):
//! - `ImpossibleInstanceOfRule` — needs the inferred type of the operand.
//! - `enum.caseType` / `enum.duplicateValue` — need constant-value evaluation of
//!   case expressions.
//! - `ReadOnlyClassRule` — purely a PHP-version gate (readonly classes need 8.2,
//!   readonly anonymous classes 8.3); we target 8.6, so it is always clean.
//! - `RequireExtendsRule` / `RequireImplementsRule` — need `@phpstan-require-*`
//!   tag reflection, not modelled.
//! - `AllowedSubTypesRule`, `MethodTag*`, `PropertyTag*`, `LocalTypeAliases*`,
//!   `ConsistentConstructor`, `UnusedConstructorParameters` — need richer
//!   reflection / type-alias / liveness analysis than is available here.

use crate::{unknown_symbols, walk, FileAnalysis, RuleEntry};
use php_ast::{
    AttributeGroup, ClassDecl, ClassKind, Expr, ExprKind, Member, MemberName, MethodDecl, Name,
    Param, Stmt, StmtKind, Visibility,
};
use php_diagnostics::Diagnostic;
use php_index::ProjectIndex;
use php_intern::Interner;
use php_reflect::attr_target;
use php_resolve::{for_each_region, Resolution, Scope};
use php_types::Type;
use std::collections::{HashMap, HashSet};

// Our consolidated existence check: emits `class.notFound` + `function.notFound`
// + `constant.notFound`. phpstan spreads these across Classes/, Functions/, and
// Constants/; we may split it as those categories are fleshed out.
fn run_unknown_symbols(fa: &FileAnalysis) -> Vec<Diagnostic> {
    unknown_symbols(fa.project, fa.resolved_refs)
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// The kind of a class-like name, looked up via the project index (which holds
/// user declarations + built-in stubs). `None` when the name resolves to a FQN
/// that the project doesn't know (existence is the `unknown-symbol` rule's job)
/// or to a non-FQN (`self`/`parent`/`static`, built-in scalar types).
fn resolved_kind(project: &ProjectIndex, scope: &Scope, name: &Name) -> Option<ClassKind> {
    let res = scope.resolve_class(name);
    let fqn = res.fqn()?;
    project.class(fqn).map(|c| c.kind)
}

/// Visit each class-like declaration in the program together with the [`Scope`]
/// of its enclosing namespace region. Descends into nested/conditional blocks so
/// classes declared inside `if`/`try`/loops are still seen.
fn for_each_class(program: &php_ast::Program, interner: &Interner, mut f: impl FnMut(&Scope, &ClassDecl)) {
    fn visit(scope: &Scope, st: &Stmt, f: &mut impl FnMut(&Scope, &ClassDecl)) {
        match &st.kind {
            StmtKind::Class(c) => f(scope, c),
            StmtKind::Block(b) => b.iter().for_each(|s| visit(scope, s, f)),
            StmtKind::If { then, elseifs, els, .. } => {
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
            StmtKind::Try { body, catches, finally } => {
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

/// A human label for the current class-like being declared (matching phpstan's
/// `Class %s` / `Interface %s` / `Trait %s` / `Enum %s`).
fn class_label(c: &ClassDecl, interner: &Interner) -> String {
    let kind = match c.kind {
        ClassKind::Class => "Class",
        ClassKind::Interface => "Interface",
        ClassKind::Trait => "Trait",
        ClassKind::Enum => "Enum",
    };
    match c.name {
        Some(n) => format!("{kind} {}", interner.resolve(n)),
        None => "Anonymous class".to_string(),
    }
}

/// A method with `__construct` (case-insensitive) name in a member list.
fn find_constructor<'a>(c: &'a ClassDecl, interner: &Interner) -> Option<&'a MethodDecl> {
    c.members.iter().find_map(|m| match m {
        Member::Method(md) if interner.resolve(md.name).eq_ignore_ascii_case("__construct") => Some(md),
        _ => None,
    })
}

// ---------------------------------------------------------------------------
// InstantiationRule — `new` of an interface/trait/enum/abstract class
// ---------------------------------------------------------------------------

/// `new X` where `X` is an interface, trait, enum, or abstract class.
///
/// Mirrors phpstan's `InstantiationRule` (the kind-specific subset). Existence
/// (`class.notFound`) is handled by `unknown-symbol`; here we only classify a
/// *known* class-like by kind. `new self`/`parent`/`static` are skipped (they
/// resolve to `LateStatic`, not a FQN).
fn run_instantiation(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            let mut visit = |e: &Expr| {
                let ExprKind::New { class, args } = &e.kind else { return };
                // First-class-callable instantiation `new X(...)` is its own rule.
                if args.iter().any(|a| a.placeholder) {
                    return;
                }
                let ExprKind::Name(name) = &class.kind else { return };
                let res = scope.resolve_class(name);
                let Some(fqn) = res.fqn() else { return };
                let Some(entry) = fa.project.class(fqn) else { return };
                let display = entry.fqn.clone();
                let (code, msg) = match entry.kind {
                    ClassKind::Interface => {
                        ("new.interface", format!("Cannot instantiate interface {display}."))
                    }
                    ClassKind::Trait => ("new.trait", format!("Cannot instantiate trait {display}.")),
                    ClassKind::Enum => ("new.enum", format!("Cannot instantiate enum {display}.")),
                    ClassKind::Class => {
                        // Abstract is tracked only by the reflection index.
                        if fa.reflection.class(fqn).is_some_and(|c| c.is_abstract) {
                            ("new.abstract", format!("Instantiated class {display} is abstract."))
                        } else {
                            return;
                        }
                    }
                };
                out.push(Diagnostic::error(class.span, msg).with_code(code));
            };
            // Walk the region's expressions. `walk` operates on a Program, so
            // descend manually via a per-statement closure collector.
            collect_exprs_in_stmt(st, &mut visit);
        }
    });
    out
}

/// Visit every expression inside one statement, keeping the caller's enclosing
/// namespace scope. The shared [`walk::for_each_expr`] takes a `Program`, so wrap
/// the statement in a one-element program (the clone is cheap relative to the
/// whole-program walks the other rules perform).
fn collect_exprs_in_stmt(st: &Stmt, f: &mut impl FnMut(&Expr)) {
    walk::for_each_expr(&php_ast::Program { stmts: vec![st.clone()] }, f);
}

// ---------------------------------------------------------------------------
// InstantiationCallableRule — `new X(...)`
// ---------------------------------------------------------------------------

/// `new X(...)` — a first-class callable cannot be created from `new`.
///
/// Mirrors phpstan's `InstantiationCallableRule`.
fn run_instantiation_callable(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        if let ExprKind::New { args, .. } = &e.kind {
            if args.iter().any(|a| a.placeholder) {
                out.push(
                    Diagnostic::error(e.span, "Cannot create callable from the new operator.")
                        .with_code("callable.notSupported"),
                );
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// NewStaticRule — `new static()` in a non-final class
// ---------------------------------------------------------------------------

/// `new static()` inside a non-final class.
///
/// Mirrors the core of phpstan's `NewStaticRule`: a `new static()` in a class
/// that is not `final` is unsafe (a subclass may make construction fail). We
/// emit when the enclosing class is not final; the consistent-constructor
/// refinement phpstan applies needs richer reflection and is omitted.
fn run_new_static(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |_scope, c| {
        if c.modifiers.is_final {
            return;
        }
        // Only classes (not interfaces/traits/enums) can host `new static()`.
        if c.kind != ClassKind::Class {
            return;
        }
        for m in &c.members {
            let Member::Method(md) = m else { continue };
            let Some(body) = &md.body else { continue };
            for st in body {
                find_new_static(st, &mut out);
            }
        }
    });
    out
}

fn find_new_static(st: &Stmt, out: &mut Vec<Diagnostic>) {
    walk::for_each_expr(&php_ast::Program { stmts: vec![st.clone()] }, &mut |e| {
        let ExprKind::New { class, .. } = &e.kind else { return };
        let ExprKind::Name(name) = &class.kind else { return };
        // `static` is recorded as a bare unqualified name.
        if name.text.eq_ignore_ascii_case("static") {
            out.push(
                Diagnostic::error(e.span, "Unsafe usage of new static().").with_code("new.static"),
            );
        }
    });
}

// ---------------------------------------------------------------------------
// extends / implements / interface-extends / trait-use — wrong kind
// ---------------------------------------------------------------------------

/// `extends` / `implements` / interface `extends` / `use` referencing the wrong
/// kind of symbol, or an interface using a trait.
///
/// Mirrors phpstan's `ExistingClassInClassExtendsRule`,
/// `ExistingClassesInClassImplementsRule`,
/// `ExistingClassesInInterfaceExtendsRule`, and `ExistingClassInTraitUseRule`
/// (the kind-mismatch subset; existence is `unknown-symbol`). A name that doesn't
/// resolve to a *known* symbol is left to the existence check.
fn run_inheritance_kinds(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |scope, c| {
        let label = class_label(c, fa.interner);

        // `extends` — a class extends 0..1 class; an interface extends 0..n
        // interfaces. We dispatch by the *declaring* kind.
        for parent in &c.extends {
            match c.kind {
                ClassKind::Class => check_class_extends(fa, scope, &label, parent, &mut out),
                ClassKind::Interface => check_interface_extends(fa, scope, &label, parent, &mut out),
                // Traits/enums can't use `extends`; if parsed, skip.
                _ => {}
            }
        }

        // `implements` — classes; each target must be an interface. (Enum
        // `implements` is owned by `run_enum_implements`, which uses phpstan's
        // dedicated `enumImplements.*` identifiers.)
        if c.kind == ClassKind::Class {
            for iface in &c.implements {
                check_implements(fa, scope, &label, iface, &mut out);
            }
        }

        // `use TraitName;` — each target must be a trait. An interface cannot use
        // any trait at all.
        for m in &c.members {
            let Member::TraitUse(tu) = m else { continue };
            for t in &tu.traits {
                if c.kind == ClassKind::Interface {
                    out.push(
                        Diagnostic::error(
                            t.span,
                            format!("{label} uses trait {}.", t.text),
                        )
                        .with_code("interface.traitUse"),
                    );
                    continue;
                }
                check_trait_use(fa, scope, &label, t, &mut out);
            }
        }
    });
    out
}

fn check_class_extends(fa: &FileAnalysis, scope: &Scope, label: &str, parent: &Name, out: &mut Vec<Diagnostic>) {
    let Some(kind) = resolved_kind(fa.project, scope, parent) else { return };
    let res = scope.resolve_class(parent);
    let display = res.fqn().unwrap_or(&parent.text).to_string();
    match kind {
        ClassKind::Interface => out.push(
            Diagnostic::error(parent.span, format!("{label} extends interface {display}."))
                .with_code("class.extendsInterface"),
        ),
        ClassKind::Trait => out.push(
            Diagnostic::error(parent.span, format!("{label} extends trait {display}."))
                .with_code("class.extendsTrait"),
        ),
        ClassKind::Enum => out.push(
            Diagnostic::error(parent.span, format!("{label} extends enum {display}."))
                .with_code("class.extendsEnum"),
        ),
        ClassKind::Class => {
            // A class extending a `final` class. `final` is only known for user
            // declarations (the reflection index); built-ins aren't flagged.
            if fa.reflection.class(&display).is_some_and(|c| c.is_final) {
                out.push(
                    Diagnostic::error(parent.span, format!("{label} extends final class {display}."))
                        .with_code("class.extendsFinal"),
                );
            }
        }
    }
}

fn check_interface_extends(fa: &FileAnalysis, scope: &Scope, label: &str, parent: &Name, out: &mut Vec<Diagnostic>) {
    let Some(kind) = resolved_kind(fa.project, scope, parent) else { return };
    let res = scope.resolve_class(parent);
    let display = res.fqn().unwrap_or(&parent.text).to_string();
    let (code, word) = match kind {
        ClassKind::Class => ("interfaceExtends.class", "class"),
        ClassKind::Trait => ("interfaceExtends.trait", "trait"),
        ClassKind::Enum => ("interfaceExtends.enum", "enum"),
        ClassKind::Interface => return,
    };
    out.push(
        Diagnostic::error(parent.span, format!("{label} extends {word} {display}.")).with_code(code),
    );
}

fn check_implements(fa: &FileAnalysis, scope: &Scope, label: &str, iface: &Name, out: &mut Vec<Diagnostic>) {
    let Some(kind) = resolved_kind(fa.project, scope, iface) else { return };
    let res = scope.resolve_class(iface);
    let display = res.fqn().unwrap_or(&iface.text).to_string();
    let (code, word) = match kind {
        ClassKind::Class => ("classImplements.class", "class"),
        ClassKind::Trait => ("classImplements.trait", "trait"),
        ClassKind::Enum => ("classImplements.enum", "enum"),
        ClassKind::Interface => return,
    };
    out.push(
        Diagnostic::error(iface.span, format!("{label} implements {word} {display}.")).with_code(code),
    );
}

fn check_trait_use(fa: &FileAnalysis, scope: &Scope, label: &str, t: &Name, out: &mut Vec<Diagnostic>) {
    let Some(kind) = resolved_kind(fa.project, scope, t) else { return };
    let res = scope.resolve_class(t);
    let display = res.fqn().unwrap_or(&t.text).to_string();
    let (code, word) = match kind {
        ClassKind::Class => ("traitUse.class", "class"),
        ClassKind::Interface => ("traitUse.interface", "interface"),
        ClassKind::Enum => ("traitUse.enum", "enum"),
        ClassKind::Trait => return,
    };
    out.push(
        Diagnostic::error(t.span, format!("{label} uses {word} {display}.")).with_code(code),
    );
}

// ---------------------------------------------------------------------------
// ExistingClassInInstanceOfRule — `instanceof Trait` / `instanceof Enum`
// ---------------------------------------------------------------------------

/// `$x instanceof X` where `X` is a trait or enum.
///
/// Mirrors the kind-mismatch subset of phpstan's `ExistingClassInInstanceOfRule`.
fn run_instanceof_kind(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            collect_exprs_in_stmt(st, &mut |e| {
                let ExprKind::Instanceof { class, .. } = &e.kind else { return };
                let ExprKind::Name(name) = &class.kind else { return };
                let Some(kind) = resolved_kind(fa.project, scope, name) else { return };
                // Only a trait is an invalid `instanceof` target here; enums and
                // classes/interfaces are all valid operands.
                if kind != ClassKind::Trait {
                    return;
                }
                let res = scope.resolve_class(name);
                let display = res.fqn().unwrap_or(&name.text).to_string();
                out.push(
                    Diagnostic::error(class.span, format!("Class {display} is a trait."))
                        .with_code("instanceof.trait"),
                );
            });
        }
    });
    out
}

// ---------------------------------------------------------------------------
// EnumSanityRule
// ---------------------------------------------------------------------------

const ALLOWED_ENUM_MAGIC: &[&str] = &["__call", "__callstatic", "__invoke"];

/// Structural sanity checks for `enum` declarations.
///
/// Mirrors phpstan's `EnumSanityRule` for the cases expressible without type
/// inference: forbidden `__construct`/`__destruct`/magic methods, redeclaring
/// `cases`/`from`/`tryFrom`, an invalid backing type, and case-value presence
/// vs. the backing. (`enum.caseType` / `enum.duplicateValue` need value
/// evaluation and are deferred.)
fn run_enum_sanity(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |_scope, c| {
        if c.kind != ClassKind::Enum {
            return;
        }
        let display = c.name.map(|n| fa.interner.resolve(n).to_string()).unwrap_or_default();
        let is_backed = c.backing.is_some();
        // The backing type's textual name (`int`/`string` are valid).
        let backing_name = c.backing.as_ref().and_then(|t| match &t.kind {
            php_ast::TypeKind::Simple(n) => Some(n.text.clone()),
            _ => None,
        });

        for m in &c.members {
            let Member::Method(md) = m else { continue };
            let name = fa.interner.resolve(md.name);
            let lower = name.to_ascii_lowercase();
            // Magic methods.
            if lower.starts_with("__") {
                if lower == "__construct" {
                    out.push(
                        Diagnostic::error(enum_member_span(c), format!("Enum {display} contains constructor."))
                            .with_code("enum.constructor"),
                    );
                } else if lower == "__destruct" {
                    out.push(
                        Diagnostic::error(enum_member_span(c), format!("Enum {display} contains destructor."))
                            .with_code("enum.destructor"),
                    );
                } else if is_magic_method(&lower) && !ALLOWED_ENUM_MAGIC.contains(&lower.as_str()) {
                    out.push(
                        Diagnostic::error(
                            enum_member_span(c),
                            format!("Enum {display} contains magic method {name}()."),
                        )
                        .with_code("enum.magicMethod"),
                    );
                }
            }
            // Native methods that may not be redeclared.
            if lower == "cases" || (is_backed && (lower == "from" || lower == "tryfrom")) {
                out.push(
                    Diagnostic::error(
                        enum_member_span(c),
                        format!("Enum {display} cannot redeclare native method {name}()."),
                    )
                    .with_code("enum.methodRedeclaration"),
                );
            }
        }

        // Backing type must be int or string.
        if let Some(bt) = &backing_name {
            let stripped = bt.trim_start_matches('\\');
            if !stripped.eq_ignore_ascii_case("int") && !stripped.eq_ignore_ascii_case("string") {
                out.push(
                    Diagnostic::error(
                        c.backing.as_ref().unwrap().span,
                        format!("Backed enum {display} can have only \"int\" or \"string\" type."),
                    )
                    .with_code("enum.backingType"),
                );
            }
        }

        // Per-case value presence vs. backing.
        for m in &c.members {
            let Member::EnumCase(ec) = m else { continue };
            let case_name = fa.interner.resolve(ec.name);
            if !is_backed {
                if let Some(v) = &ec.value {
                    out.push(
                        Diagnostic::error(
                            v.span,
                            format!("Enum {display} is not backed, but case {case_name} has value."),
                        )
                        .with_code("enum.caseWithValue"),
                    );
                }
            } else if ec.value.is_none() {
                let bt = backing_name.as_deref().unwrap_or("int");
                out.push(
                    Diagnostic::error(
                        ec_span(ec),
                        format!(
                            "Enum case {display}::{case_name} does not have a value but the enum is backed with the \"{bt}\" type."
                        ),
                    )
                    .with_code("enum.missingCase"),
                );
            }
        }
    });
    out
}

/// All recognised PHP magic methods (those that get special treatment); used to
/// distinguish a method merely starting with `__` from an actual magic method.
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

fn ec_span(ec: &php_ast::EnumCaseDecl) -> php_span::Span {
    // EnumCaseDecl has no span; if it has a value, point at the value, else fall
    // back to a zero span (the diagnostic message still names the case).
    ec.value.as_ref().map(|v| v.span).unwrap_or(php_span::Span::new(0, 0))
}

fn enum_member_span(c: &ClassDecl) -> php_span::Span {
    // Use the enum's name token span when available; otherwise the backing type;
    // otherwise a zero span.
    c.backing
        .as_ref()
        .map(|t| t.span)
        .or_else(|| c.extends.first().map(|n| n.span))
        .unwrap_or(php_span::Span::new(0, 0))
}

// ---------------------------------------------------------------------------
// DuplicateDeclarationRule — redeclared members within a class-like
// ---------------------------------------------------------------------------

/// Redeclared methods / properties / constants / enum-cases within one
/// class-like declaration.
///
/// Mirrors phpstan's `DuplicateDeclarationRule` + `DuplicateDeclarationHelper`.
/// Method names are case-insensitive; properties, constants and enum cases are
/// case-sensitive. Constructor-promoted properties count as property
/// declarations.
fn run_duplicate_declaration(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |_scope, c| {
        let display = c.name.map(|n| fa.interner.resolve(n).to_string()).unwrap_or_default();

        // Constants and enum cases share one namespace in phpstan's helper.
        let mut consts_cases: HashSet<String> = HashSet::new();
        for m in &c.members {
            match m {
                Member::EnumCase(ec) => {
                    let name = fa.interner.resolve(ec.name).to_string();
                    if !consts_cases.insert(name.clone()) {
                        out.push(
                            Diagnostic::error(
                                ec_span(ec),
                                format!("Cannot redeclare enum case {display}::{name}."),
                            )
                            .with_code(dup_code(c.kind, "EnumCase")),
                        );
                    }
                }
                Member::ClassConst(cd) => {
                    for ce in &cd.consts {
                        let name = fa.interner.resolve(ce.name).to_string();
                        if !consts_cases.insert(name.clone()) {
                            out.push(
                                Diagnostic::error(
                                    ce.value.span,
                                    format!("Cannot redeclare constant {display}::{name}."),
                                )
                                .with_code(dup_code(c.kind, "Constant")),
                            );
                        }
                    }
                }
                _ => {}
            }
        }

        // Properties (declared + constructor-promoted), case-sensitive.
        let mut props: HashSet<String> = HashSet::new();
        for m in &c.members {
            if let Member::Property(pd) = m {
                for pe in &pd.props {
                    let name = fa.interner.resolve(pe.name).to_string();
                    let span = pe.default.as_ref().map(|d| d.span).unwrap_or(enum_member_span(c));
                    if !props.insert(name.clone()) {
                        out.push(
                            Diagnostic::error(span, format!("Cannot redeclare property {display}::${name}."))
                                .with_code(dup_code(c.kind, "Property")),
                        );
                    }
                }
            }
        }
        if let Some(ctor) = find_constructor(c, fa.interner) {
            for p in &ctor.params {
                if p.modifiers.is_empty() {
                    continue; // not promoted
                }
                let name = fa.interner.resolve(p.name).to_string();
                if !props.insert(name.clone()) {
                    out.push(
                        Diagnostic::error(
                            p.default.as_ref().map(|d| d.span).unwrap_or(enum_member_span(c)),
                            format!("Cannot redeclare property {display}::${name}."),
                        )
                        .with_code(dup_code(c.kind, "Property")),
                    );
                }
            }
        }

        // Methods, case-insensitive.
        let mut methods: HashSet<String> = HashSet::new();
        for m in &c.members {
            if let Member::Method(md) = m {
                let raw = fa.interner.resolve(md.name).to_string();
                let key = raw.to_ascii_lowercase();
                if !methods.insert(key) {
                    out.push(
                        Diagnostic::error(
                            enum_member_span(c),
                            format!("Cannot redeclare method {display}::{raw}()."),
                        )
                        .with_code(dup_code(c.kind, "Method")),
                    );
                }
            }
        }
    });
    out
}

/// `<kind>.duplicate<What>` — e.g. `class.duplicateMethod`, `enum.duplicateEnumCase`.
fn dup_code(kind: ClassKind, what: &str) -> &'static str {
    match (kind, what) {
        (ClassKind::Class, "Method") => "class.duplicateMethod",
        (ClassKind::Class, "Property") => "class.duplicateProperty",
        (ClassKind::Class, "Constant") => "class.duplicateConstant",
        (ClassKind::Class, "EnumCase") => "class.duplicateEnumCase",
        (ClassKind::Interface, "Method") => "interface.duplicateMethod",
        (ClassKind::Interface, "Property") => "interface.duplicateProperty",
        (ClassKind::Interface, "Constant") => "interface.duplicateConstant",
        (ClassKind::Interface, "EnumCase") => "interface.duplicateEnumCase",
        (ClassKind::Trait, "Method") => "trait.duplicateMethod",
        (ClassKind::Trait, "Property") => "trait.duplicateProperty",
        (ClassKind::Trait, "Constant") => "trait.duplicateConstant",
        (ClassKind::Trait, "EnumCase") => "trait.duplicateEnumCase",
        (ClassKind::Enum, "Method") => "enum.duplicateMethod",
        (ClassKind::Enum, "Property") => "enum.duplicateProperty",
        (ClassKind::Enum, "Constant") => "enum.duplicateConstant",
        (ClassKind::Enum, "EnumCase") => "enum.duplicateEnumCase",
        _ => "class.duplicateMethod",
    }
}

// ---------------------------------------------------------------------------
// DuplicateClassDeclarationRule — a class-like declared multiple times per file
// ---------------------------------------------------------------------------

/// A class/interface/trait/enum declared more than once in the same file.
///
/// Mirrors phpstan's `DuplicateClassDeclarationRule` at the per-file scope (the
/// project index also exposes cross-file duplicates via `duplicate_classes`).
fn run_duplicate_class(fa: &FileAnalysis) -> Vec<Diagnostic> {
    // Record each declaration: lowercased FQN key, original-case display, kind, span.
    let mut order: Vec<(String, String, ClassKind, php_span::Span)> = Vec::new();
    for_each_class(fa.program, fa.interner, |scope, c| {
        let Some(n) = c.name else { return };
        let display = scope.qualify(fa.interner.resolve(n));
        order.push((display.to_ascii_lowercase(), display, c.kind, enum_member_span(c)));
    });

    // Total per (lowercased) name.
    let mut totals: HashMap<String, usize> = HashMap::new();
    for (key, ..) in &order {
        *totals.entry(key.clone()).or_insert(0) += 1;
    }

    let mut out = Vec::new();
    let mut emitted: HashSet<String> = HashSet::new();
    for (key, display, kind, span) in &order {
        if totals.get(key).copied().unwrap_or(0) < 2 {
            continue;
        }
        if !emitted.insert(key.clone()) {
            continue; // one diagnostic per duplicated name
        }
        out.push(
            Diagnostic::error(*span, format!("{} {display} declared multiple times.", kind_title(*kind)))
                .with_code(dup_class_code(*kind)),
        );
    }
    out
}

/// Title-cased class-like kind for messages (`Class`/`Interface`/`Trait`/`Enum`).
fn kind_title(kind: ClassKind) -> &'static str {
    match kind {
        ClassKind::Class => "Class",
        ClassKind::Interface => "Interface",
        ClassKind::Trait => "Trait",
        ClassKind::Enum => "Enum",
    }
}

fn dup_class_code(kind: ClassKind) -> &'static str {
    match kind {
        ClassKind::Class => "class.duplicate",
        ClassKind::Interface => "interface.duplicate",
        ClassKind::Trait => "trait.duplicate",
        ClassKind::Enum => "enum.duplicate",
    }
}

// ---------------------------------------------------------------------------
// NonClassAttributeClassRule — `#[Attribute]` on a non-instantiable
// ---------------------------------------------------------------------------

/// A `#[Attribute]` on an interface/trait/enum, an abstract class, or a class
/// whose constructor isn't public.
///
/// Mirrors phpstan's `NonClassAttributeClassRule`.
fn run_non_class_attribute(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |_scope, c| {
        // Does any attribute group name an `Attribute`? (case-insensitive, last
        // segment).
        let has_attribute = c.attrs.iter().any(|g| {
            g.attrs.iter().any(|a| {
                let text = a.name.text.trim_start_matches('\\');
                let last = text.rsplit('\\').next().unwrap_or(text);
                last.eq_ignore_ascii_case("Attribute")
            })
        });
        if !has_attribute {
            return;
        }
        let display = c.name.map(|n| fa.interner.resolve(n).to_string()).unwrap_or_default();
        match c.kind {
            ClassKind::Interface | ClassKind::Trait | ClassKind::Enum => {
                out.push(
                    Diagnostic::error(
                        enum_member_span(c),
                        format!("{} cannot be an Attribute class.", kind_title(c.kind)),
                    )
                    .with_code(attribute_kind_code(c.kind)),
                );
                return;
            }
            ClassKind::Class => {}
        }
        if c.modifiers.is_abstract {
            out.push(
                Diagnostic::error(
                    enum_member_span(c),
                    format!("Abstract class {display} cannot be an Attribute class."),
                )
                .with_code("attribute.abstract"),
            );
            return;
        }
        if let Some(ctor) = find_constructor(c, fa.interner) {
            let vis = ctor.modifiers.visibility.unwrap_or(Visibility::Public);
            if vis != Visibility::Public {
                out.push(
                    Diagnostic::error(
                        enum_member_span(c),
                        format!("Attribute class {display} constructor must be public."),
                    )
                    .with_code("attribute.constructorNotPublic"),
                );
            }
        }
    });
    out
}

fn attribute_kind_code(kind: ClassKind) -> &'static str {
    match kind {
        ClassKind::Interface => "attribute.interface",
        ClassKind::Trait => "attribute.trait",
        ClassKind::Enum => "attribute.enum",
        ClassKind::Class => "attribute.class",
    }
}

// ---------------------------------------------------------------------------
// Attribute *usage* checks — Class/Function/Method/Property/ClassConstant/
// EnumCase/Param AttributesRule family (via attribute-target reflection)
// ---------------------------------------------------------------------------

/// For each attribute applied to a declaration, look the attribute class up in
/// the reflection index and check it against the usage site: that the class is
/// actually an `#[Attribute]` (`attribute.notAttribute`), allows this target
/// (`attribute.target`), and — unless `IS_REPEATABLE` — isn't repeated
/// (`attribute.nonRepeatable`). A *missing* attribute class is left to the
/// existing `class.notFound` rule; built-in attributes (not in the reflection
/// index, only names) are skipped — keeping us false-positive-free.
fn run_attribute_usages(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            collect_attr_targets(scope, fa, st, &mut out);
        }
        // Closures / arrow-fns (expression position) — their attributes target a
        // function. Attribute names resolve in the lexical (namespace) scope.
        let prog = php_ast::Program { stmts: region.to_vec() };
        walk::for_each_expr(&prog, &mut |e| {
            let attrs = match &e.kind {
                ExprKind::Closure(c) => &c.attrs,
                ExprKind::ArrowFn(a) => &a.attrs,
                _ => return,
            };
            check_attr_usage(scope, fa, attrs, attr_target::FUNCTION, "function", &mut out);
        });
    });
    out
}

fn collect_attr_targets(scope: &Scope, fa: &FileAnalysis, st: &Stmt, out: &mut Vec<Diagnostic>) {
    match &st.kind {
        StmtKind::Function(f) => {
            check_attr_usage(scope, fa, &f.attrs, attr_target::FUNCTION, "function", out);
            for p in &f.params {
                check_attr_usage(scope, fa, &p.attrs, attr_target::PARAMETER, "parameter", out);
            }
        }
        StmtKind::Class(c) => {
            check_attr_usage(scope, fa, &c.attrs, attr_target::CLASS, "class", out);
            for m in &c.members {
                match m {
                    Member::Method(md) => {
                        check_attr_usage(scope, fa, &md.attrs, attr_target::METHOD, "method", out);
                        for p in &md.params {
                            check_attr_usage(scope, fa, &p.attrs, attr_target::PARAMETER, "parameter", out);
                        }
                    }
                    Member::Property(pd) => {
                        check_attr_usage(scope, fa, &pd.attrs, attr_target::PROPERTY, "property", out)
                    }
                    Member::ClassConst(cc) => check_attr_usage(
                        scope, fa, &cc.attrs, attr_target::CLASS_CONSTANT, "class constant", out,
                    ),
                    Member::EnumCase(ec) => check_attr_usage(
                        scope, fa, &ec.attrs, attr_target::CLASS_CONSTANT, "enum case", out,
                    ),
                    _ => {}
                }
            }
        }
        StmtKind::Namespace { body: Some(b), .. } => {
            for s in b {
                collect_attr_targets(scope, fa, s, out);
            }
        }
        _ => {}
    }
}

fn check_attr_usage(
    scope: &Scope,
    fa: &FileAnalysis,
    attrs: &[AttributeGroup],
    target: u32,
    target_name: &str,
    out: &mut Vec<Diagnostic>,
) {
    let mut seen: HashSet<String> = HashSet::new();
    for g in attrs {
        for a in &g.attrs {
            let Resolution::Fqn(fqn) = scope.resolve_class(&a.name) else { continue };
            // Only user attribute classes are reflected; builtins/missing are
            // handled elsewhere (names-only index / class.notFound).
            let Some(cr) = fa.reflection.class(&fqn) else { continue };
            let display = &cr.fqn;
            match cr.attribute {
                None => out.push(
                    Diagnostic::error(
                        a.name.span,
                        format!("Class {display} is not an Attribute class."),
                    )
                    .with_code("attribute.notAttribute"),
                ),
                Some(spec) => {
                    if spec.targets & target == 0 {
                        out.push(
                            Diagnostic::error(
                                a.name.span,
                                format!("Attribute class {display} does not have the {target_name} target."),
                            )
                            .with_code("attribute.target"),
                        );
                    }
                    if !spec.repeatable && !seen.insert(fqn.to_ascii_lowercase()) {
                        out.push(
                            Diagnostic::error(
                                a.name.span,
                                format!("Attribute class {display} is not repeatable but is already present above the {target_name}."),
                            )
                            .with_code("attribute.nonRepeatable"),
                        );
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// InvalidPromotedPropertiesRule
// ---------------------------------------------------------------------------

/// Constructor property promotion used outside a constructor, or a variadic
/// promoted property.
///
/// Mirrors phpstan's `InvalidPromotedPropertiesRule` for PHP 8.0+ (we target
/// 8.6, so the "supported only on …" version gate never fires). A promoted
/// param outside `__construct` is invalid; a variadic promoted param is invalid.
fn run_invalid_promoted(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |_scope, c| {
        for m in &c.members {
            let Member::Method(md) = m else { continue };
            let is_ctor = fa.interner.resolve(md.name).eq_ignore_ascii_case("__construct");
            check_promoted_params(&md.params, is_ctor, md.body.is_some(), fa, &mut out);
        }
    });
    out
}

fn check_promoted_params(
    params: &[Param],
    is_ctor: bool,
    has_body: bool,
    fa: &FileAnalysis,
    out: &mut Vec<Diagnostic>,
) {
    let has_promoted = params.iter().any(|p| !p.modifiers.is_empty() || !p.hooks.is_empty());
    if !has_promoted {
        return;
    }
    if !is_ctor {
        out.push(
            Diagnostic::error(
                promoted_span(params),
                "Promoted properties can be in constructor only.",
            )
            .with_code("property.invalidPromoted"),
        );
        return;
    }
    if !has_body {
        out.push(
            Diagnostic::error(
                promoted_span(params),
                "Promoted properties are not allowed in abstract constructors.",
            )
            .with_code("property.invalidPromoted"),
        );
        return;
    }
    for p in params {
        if p.modifiers.is_empty() {
            continue;
        }
        if p.variadic {
            let name = fa.interner.resolve(p.name);
            out.push(
                Diagnostic::error(
                    p.default.as_ref().map(|d| d.span).unwrap_or(promoted_span(params)),
                    format!("Promoted property parameter ${name} can not be variadic."),
                )
                .with_code("property.invalidPromoted"),
            );
        }
    }
}

/// A best-effort span for a promoted parameter list (params carry no span; use a
/// default's span if present, else a zero span).
fn promoted_span(params: &[Param]) -> php_span::Span {
    params
        .iter()
        .find_map(|p| p.default.as_ref().map(|d| d.span))
        .unwrap_or(php_span::Span::new(0, 0))
}

// ---------------------------------------------------------------------------
// ExistingClassesInEnumImplementsRule — `enum E implements <non-interface>`
// ---------------------------------------------------------------------------

/// An `enum` that `implements` a class / trait / enum (only an interface is
/// valid). Mirrors phpstan's `ExistingClassesInEnumImplementsRule`. Existence
/// (`interface.notFound`) stays with the `unknown-symbol` rule; here we only
/// classify a *known* implemented symbol by kind, using phpstan's dedicated
/// `enumImplements.*` identifiers (distinct from a class's `classImplements.*`).
fn run_enum_implements(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |scope, c| {
        if c.kind != ClassKind::Enum {
            return;
        }
        let enum_name = c.name.map(|n| scope.qualify(fa.interner.resolve(n))).unwrap_or_default();
        for iface in &c.implements {
            let Some(kind) = resolved_kind(fa.project, scope, iface) else { continue };
            let res = scope.resolve_class(iface);
            let display = res.fqn().unwrap_or(&iface.text).to_string();
            let (code, word) = match kind {
                ClassKind::Class => ("enumImplements.class", "class"),
                ClassKind::Trait => ("enumImplements.trait", "trait"),
                ClassKind::Enum => ("enumImplements.enum", "enum"),
                ClassKind::Interface => continue,
            };
            out.push(
                Diagnostic::error(
                    iface.span,
                    format!("Enum {enum_name} implements {word} {display}."),
                )
                .with_code(code),
            );
        }
    });
    out
}

// ---------------------------------------------------------------------------
// ClassConstantRule — `Class::CONST` access (existence / visibility / scope)
// ---------------------------------------------------------------------------

/// What a class-const / static class operand resolves to inside a class body.
enum ClassTarget {
    /// A concrete class FQN (resolved via `self`/`static`/`parent` or a name).
    Fqn(String),
    /// `self`/`static`/`parent` used outside any class (phpstan `outOfClass.*`).
    OutOfClass(&'static str),
    /// `parent::` but the enclosing class has no parent (`class.noParent`).
    NoParent,
    /// Not statically resolvable (a variable/expression class operand, or a name
    /// the project doesn't know) — skip to stay false-positive-free.
    Unknown,
}

/// Resolve the class operand of a `::` access. `self_fqn`/`parent_fqn` describe
/// the enclosing class (both `None` when not in a class body).
fn resolve_class_target(
    class: &Expr,
    scope: &Scope,
    self_fqn: Option<&str>,
    parent_fqn: Option<&str>,
) -> ClassTarget {
    let ExprKind::Name(n) = &class.kind else { return ClassTarget::Unknown };
    match scope.resolve_class(n) {
        Resolution::LateStatic(which) => match which.as_str() {
            "self" | "static" => match self_fqn {
                Some(f) => ClassTarget::Fqn(f.to_string()),
                None => ClassTarget::OutOfClass(if which == "self" { "self" } else { "static" }),
            },
            "parent" => {
                if self_fqn.is_none() {
                    ClassTarget::OutOfClass("parent")
                } else {
                    match parent_fqn {
                        Some(p) => ClassTarget::Fqn(p.to_string()),
                        None => ClassTarget::NoParent,
                    }
                }
            }
            _ => ClassTarget::Unknown,
        },
        r => match r.fqn() {
            Some(f) => ClassTarget::Fqn(f.to_string()),
            None => ClassTarget::Unknown,
        },
    }
}

/// `Class::CONST` checks: `self`/`static`/`parent` outside a class, `parent`
/// without a parent class, accessing a constant on a trait, an undefined
/// constant, and private/protected visibility violations.
///
/// Mirrors phpstan's `ClassConstantRule` for the statically-resolvable subset.
/// `::class` is never flagged (it always exists). A constant on an unknown /
/// unindexed / built-in class is left alone (existence is `class.notFound`'s
/// job; built-ins lack full reflection) — keeping us false-positive-free.
fn run_class_constant(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();

    // (1) Class member bodies, with the enclosing class's `self`/`parent` context.
    // `for_each_class` discovers classes through control-flow nesting too.
    for_each_class(fa.program, fa.interner, |scope, c| {
        let self_fqn = c.name.map(|n| scope.qualify(fa.interner.resolve(n)));
        let parent_fqn = c.extends.first().map(|p| {
            scope.resolve_class(p).fqn().map(str::to_string).unwrap_or_else(|| p.text.clone())
        });
        for m in &c.members {
            let Member::Method(md) = m else { continue };
            let Some(body) = &md.body else { continue };
            for st in body {
                scan_const_fetches(st, scope, fa, self_fqn.as_deref(), parent_fqn.as_deref(), &mut out);
            }
        }
    });

    // (2) Everything outside a class body — region top-level + named-function
    // bodies — with no class context. `for_each_expr_in_scope` covers one scope's
    // expressions (crossing control flow but stopping at every function/class
    // boundary), so we scan each scope exactly once and descend separately to
    // discover nested function bodies. No double-reporting.
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            scan_const_fetches(st, scope, fa, None, None, &mut out);
            find_nested_function_bodies(st, scope, fa, &mut out);
        }
    });

    out
}

/// Scan the const fetches *directly within one scope* of statement `st` (does
/// not cross function/class boundaries), with the given class context.
fn scan_const_fetches(
    st: &Stmt,
    scope: &Scope,
    fa: &FileAnalysis,
    self_fqn: Option<&str>,
    parent_fqn: Option<&str>,
    out: &mut Vec<Diagnostic>,
) {
    walk::for_each_expr_in_scope(st, &mut |e| {
        if let ExprKind::ClassConst { class, name } = &e.kind {
            check_one_class_const(e, class, name, scope, fa, self_fqn, parent_fqn, out);
        }
    });
}

/// Descend through control flow (without re-scanning expressions — the enclosing
/// scope's [`scan_const_fetches`] already covered them) to find named-function
/// declarations, and scan each function body as its own scope (no class context).
/// Class declarations are skipped (their member bodies are handled separately).
fn find_nested_function_bodies(st: &Stmt, scope: &Scope, fa: &FileAnalysis, out: &mut Vec<Diagnostic>) {
    match &st.kind {
        StmtKind::Function(f) => {
            for s in &f.body {
                scan_const_fetches(s, scope, fa, None, None, out);
                find_nested_function_bodies(s, scope, fa, out);
            }
        }
        StmtKind::Block(b) => b.iter().for_each(|s| find_nested_function_bodies(s, scope, fa, out)),
        StmtKind::If { then, elseifs, els, .. } => {
            find_nested_function_bodies(then, scope, fa, out);
            for e in elseifs {
                find_nested_function_bodies(&e.body, scope, fa, out);
            }
            if let Some(e) = els {
                find_nested_function_bodies(e, scope, fa, out);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => find_nested_function_bodies(body, scope, fa, out),
        StmtKind::Try { body, catches, finally } => {
            body.iter().for_each(|s| find_nested_function_bodies(s, scope, fa, out));
            for c in catches {
                c.body.iter().for_each(|s| find_nested_function_bodies(s, scope, fa, out));
            }
            if let Some(fin) = finally {
                fin.iter().for_each(|s| find_nested_function_bodies(s, scope, fa, out));
            }
        }
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                c.body.iter().for_each(|s| find_nested_function_bodies(s, scope, fa, out));
            }
        }
        StmtKind::Declare { body: Some(b), .. } => find_nested_function_bodies(b, scope, fa, out),
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn check_one_class_const(
    e: &Expr,
    class: &Expr,
    name: &MemberName,
    scope: &Scope,
    fa: &FileAnalysis,
    self_fqn: Option<&str>,
    parent_fqn: Option<&str>,
    out: &mut Vec<Diagnostic>,
) {
    // Only a literal `::IDENT` constant fetch (computed `::{expr}` / `::$var` are
    // not constant fetches we can resolve statically).
    let MemberName::Ident(const_sym) = name else { return };
    let const_name = fa.interner.resolve(*const_sym);
    // `::class` always exists; never flagged here.
    if const_name.eq_ignore_ascii_case("class") {
        return;
    }
    let fqn = match resolve_class_target(class, scope, self_fqn, parent_fqn) {
        ClassTarget::Fqn(f) => f,
        ClassTarget::OutOfClass(which) => {
            out.push(
                Diagnostic::error(class.span, format!("Using {which} outside of class scope."))
                    .with_code(match which {
                        "self" => "outOfClass.self",
                        "static" => "outOfClass.static",
                        _ => "outOfClass.parent",
                    }),
            );
            return;
        }
        ClassTarget::NoParent => {
            // Name the enclosing class (phpstan: "but %s does not extend any class").
            let here = self_fqn.unwrap_or("").trim_start_matches('\\');
            out.push(
                Diagnostic::error(
                    e.span,
                    format!("Access to parent::{const_name} but {here} does not extend any class."),
                )
                .with_code("class.noParent"),
            );
            return;
        }
        ClassTarget::Unknown => return,
    };

    // The class must be a *known, indexed* class-like with full reflection.
    let Some(cr) = fa.reflection.class(&fqn) else { return };
    let display = cr.fqn.trim_start_matches('\\').to_string();

    // Accessing a constant on a trait is invalid (other than `::class`).
    if cr.kind == ClassKind::Trait {
        out.push(
            Diagnostic::error(
                e.span,
                format!("Cannot access constant {const_name} on trait {display}."),
            )
            .with_code("classConstant.onTrait"),
        );
        return;
    }
    // Enum cases are constants too; phpstan models them via reflection. If the
    // class has a `__get`-less magic-const story we can't see, only flag when the
    // hierarchy is fully indexed (no unknown parents) — otherwise skip.
    if has_unknown_ancestor(fa, &fqn) {
        return;
    }
    let found = fa.reflection.find_constant(&fqn, const_name);
    // Enum cases resolve as constants in phpstan; our reflection stores enum
    // cases separately, so treat a known enum case name as existing.
    let is_enum_case = cr.kind == ClassKind::Enum && enum_has_case(fa, &fqn, const_name);
    let Some(found) = found else {
        if is_enum_case {
            return;
        }
        out.push(
            Diagnostic::error(
                e.span,
                format!("Access to undefined constant {display}::{const_name}."),
            )
            .with_code("classConstant.notFound"),
        );
        return;
    };

    // Visibility: a private/protected constant accessed from outside the allowed
    // scope. We only emit a *confident* violation: a private constant accessed
    // from a different class (or top-level), or a protected constant accessed
    // from an unrelated class. Same-class / subclass access is allowed.
    let decl = found.declaring_class.trim_start_matches('\\').to_string();
    let accessible = match found.member.visibility {
        Visibility::Public => true,
        Visibility::Private => self_fqn.is_some_and(|s| {
            s.trim_start_matches('\\').eq_ignore_ascii_case(&decl)
        }),
        Visibility::Protected => self_fqn.is_some_and(|s| {
            let s = s.trim_start_matches('\\');
            s.eq_ignore_ascii_case(&decl)
                || fa.reflection.is_subclass_of(s, &decl)
                || fa.reflection.is_subclass_of(&decl, s)
        }),
    };
    if !accessible {
        let (word, code) = match found.member.visibility {
            Visibility::Private => ("private", "classConstant.private"),
            _ => ("protected", "classConstant.protected"),
        };
        out.push(
            Diagnostic::error(
                e.span,
                format!("Access to {word} constant {const_name} of class {decl}."),
            )
            .with_code(code),
        );
    }
}

/// Whether `fqn`'s ancestor chain references a class the reflection index does
/// not know — in which case a constant could be inherited from it and we must
/// not claim it's undefined.
fn has_unknown_ancestor(fa: &FileAnalysis, fqn: &str) -> bool {
    fn walk(fa: &FileAnalysis, fqn: &str, seen: &mut Vec<String>) -> bool {
        let key = fqn.trim_start_matches('\\').to_ascii_lowercase();
        if seen.contains(&key) {
            return false;
        }
        seen.push(key);
        let Some(cr) = fa.reflection.class(fqn) else { return true };
        cr.parents.iter().chain(&cr.interfaces).chain(&cr.traits).any(|p| match p {
            Type::Named { fqn, .. } => walk(fa, fqn, seen),
            _ => false,
        })
    }
    let mut seen = Vec::new();
    // The class itself is known (checked by the caller); test only its ancestors.
    let Some(cr) = fa.reflection.class(fqn) else { return true };
    cr.parents
        .iter()
        .chain(&cr.interfaces)
        .chain(&cr.traits)
        .any(|p| matches!(p, Type::Named { fqn, .. } if walk(fa, fqn, &mut seen)))
}

/// Whether the enum at `fqn` declares a case named `name` (case-sensitive).
fn enum_has_case(fa: &FileAnalysis, fqn: &str, name: &str) -> bool {
    // Reflection doesn't expose enum cases directly; re-scan the declaration.
    let mut found = false;
    for_each_class(fa.program, fa.interner, |scope, c| {
        if found || c.kind != ClassKind::Enum {
            return;
        }
        let Some(n) = c.name else { return };
        if !scope.qualify(fa.interner.resolve(n)).trim_start_matches('\\').eq_ignore_ascii_case(fqn.trim_start_matches('\\')) {
            return;
        }
        for m in &c.members {
            if let Member::EnumCase(ec) = m {
                if fa.interner.resolve(ec.name) == name {
                    found = true;
                }
            }
        }
    });
    found
}

// ---------------------------------------------------------------------------
// AccessPrivateConstantThroughStaticRule — `static::PRIVATE_CONST`
// ---------------------------------------------------------------------------

/// `static::PRIVATE_CONST` inside a non-final class — unsafe, because a subclass
/// can't see the parent's private constant through late static binding.
///
/// Mirrors phpstan's `AccessPrivateConstantThroughStaticRule`. We only flag when
/// the enclosing class is known, not final, and the named constant resolves to a
/// private one on the class (or an ancestor).
fn run_private_const_through_static(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |scope, c| {
        if c.kind != ClassKind::Class || c.modifiers.is_final {
            return;
        }
        let Some(n) = c.name else { return };
        let self_fqn = scope.qualify(fa.interner.resolve(n));
        for m in &c.members {
            let Member::Method(md) = m else { continue };
            let Some(body) = &md.body else { continue };
            for st in body {
                collect_exprs_in_stmt(st, &mut |e| {
                    let ExprKind::ClassConst { class, name } = &e.kind else { return };
                    let ExprKind::Name(cn) = &class.kind else { return };
                    if !cn.text.eq_ignore_ascii_case("static") {
                        return;
                    }
                    let MemberName::Ident(sym) = name else { return };
                    let const_name = fa.interner.resolve(*sym);
                    if const_name.eq_ignore_ascii_case("class") {
                        return;
                    }
                    let Some(found) = fa.reflection.find_constant(&self_fqn, const_name) else {
                        return;
                    };
                    if found.member.visibility != Visibility::Private {
                        return;
                    }
                    let decl = found.declaring_class.trim_start_matches('\\');
                    out.push(
                        Diagnostic::error(
                            e.span,
                            format!(
                                "Unsafe access to private constant {decl}::{const_name} through static::."
                            ),
                        )
                        .with_code("staticClassAccess.privateConstant"),
                    );
                });
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// MixinRule — `@mixin` PHPDoc tag pointing at a non-object / a trait
// ---------------------------------------------------------------------------

/// A class `@mixin` PHPDoc tag whose type is a non-object (`mixin.nonObject`) or
/// a trait (`mixin.trait`).
///
/// Mirrors the statically-checkable subset of phpstan's `MixinRule`/`MixinCheck`.
/// An *unknown* mixin class is left to `class.notFound`; generics/typehint
/// completeness checks are out of scope. The `@mixin` targets are taken from the
/// reflection layer (which resolves the class docblock's `@mixin` tags).
fn run_mixin(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |scope, c| {
        let Some(n) = c.name else { return };
        let fqn = scope.qualify(fa.interner.resolve(n));
        let Some(cr) = fa.reflection.class(&fqn) else { return };
        for mixin in &cr.mixins {
            match mixin {
                Type::Named { fqn: mfqn, .. } => {
                    // A known trait is invalid; an unknown class is class.notFound's job.
                    if let Some(mcr) = fa.reflection.class(mfqn) {
                        if mcr.kind == ClassKind::Trait {
                            out.push(
                                Diagnostic::error(
                                    enum_member_span(c),
                                    format!(
                                        "PHPDoc tag @mixin contains invalid type {}.",
                                        mfqn.trim_start_matches('\\')
                                    ),
                                )
                                .with_code("mixin.trait"),
                            );
                        }
                    }
                }
                // `self`/`static`/`parent` are object types — valid.
                Type::SelfType | Type::StaticType | Type::Parent => {}
                // Anything else (scalars, arrays, callables, …) is a non-object.
                other => out.push(
                    Diagnostic::error(
                        enum_member_span(c),
                        format!("PHPDoc tag @mixin contains non-object type {other}."),
                    )
                    .with_code("mixin.nonObject"),
                ),
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// NewStaticInAbstractClassStaticMethodRule
// ---------------------------------------------------------------------------

/// `new static()` inside a *static* method of an *abstract* class — a direct
/// `Abstract::method()` call would crash (an abstract class can't be
/// instantiated).
///
/// Mirrors phpstan's `NewStaticInAbstractClassStaticMethodRule`. (The broader
/// `new static()`-in-non-final-class warning is `run_new_static`.)
fn run_new_static_abstract(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class(fa.program, fa.interner, |scope, c| {
        if c.kind != ClassKind::Class || !c.modifiers.is_abstract {
            return;
        }
        let display = c.name.map(|n| scope.qualify(fa.interner.resolve(n))).unwrap_or_default();
        let display = display.trim_start_matches('\\').to_string();
        for m in &c.members {
            let Member::Method(md) = m else { continue };
            if !md.modifiers.is_static {
                continue;
            }
            let method = fa.interner.resolve(md.name).to_string();
            let Some(body) = &md.body else { continue };
            for st in body {
                collect_exprs_in_stmt(st, &mut |e| {
                    let ExprKind::New { class, .. } = &e.kind else { return };
                    let ExprKind::Name(name) = &class.kind else { return };
                    if name.text.eq_ignore_ascii_case("static") {
                        out.push(
                            Diagnostic::error(
                                e.span,
                                format!(
                                    "Unsafe usage of new static() in abstract class {display} in static method {method}()."
                                ),
                            )
                            .with_code("new.staticInAbstractClassStaticMethod"),
                        );
                    }
                });
            }
        }
    });
    out
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "unknown-symbol", level: 0, run: run_unknown_symbols },
    RuleEntry { name: "instantiation", level: 0, run: run_instantiation },
    RuleEntry { name: "instantiation.callable", level: 0, run: run_instantiation_callable },
    RuleEntry { name: "new.static", level: 0, run: run_new_static },
    RuleEntry { name: "inheritance.kinds", level: 0, run: run_inheritance_kinds },
    RuleEntry { name: "instanceof.kind", level: 0, run: run_instanceof_kind },
    RuleEntry { name: "enum.sanity", level: 0, run: run_enum_sanity },
    RuleEntry { name: "duplicate.declaration", level: 0, run: run_duplicate_declaration },
    RuleEntry { name: "duplicate.class", level: 0, run: run_duplicate_class },
    RuleEntry { name: "attribute.class", level: 0, run: run_non_class_attribute },
    RuleEntry { name: "attribute.usage", level: 0, run: run_attribute_usages },
    RuleEntry { name: "property.invalidPromoted", level: 0, run: run_invalid_promoted },
    RuleEntry { name: "enum.implements", level: 0, run: run_enum_implements },
    RuleEntry { name: "class.constant", level: 0, run: run_class_constant },
    RuleEntry {
        name: "new.staticInAbstractClassStaticMethod",
        level: 0,
        run: run_new_static_abstract,
    },
    RuleEntry {
        name: "staticClassAccess.privateConstant",
        level: 2,
        run: run_private_const_through_static,
    },
    RuleEntry { name: "mixin", level: 2, run: run_mixin },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- attribute usage (target / repeatable / not-an-attribute) --------

    #[test]
    fn attribute_used_on_wrong_target_is_flagged() {
        // #[A] allows only TARGET_PROPERTY but is used on a class.
        let src = "<?php \
            #[\\Attribute(\\Attribute::TARGET_PROPERTY)] class A {} \
            #[A] class B {}";
        assert_eq!(codes(src, run_attribute_usages), ["attribute.target"]);
    }

    #[test]
    fn attribute_on_closure_wrong_target_is_flagged() {
        let src = "<?php \
            #[\\Attribute(\\Attribute::TARGET_PROPERTY)] class A {} \
            $f = #[A] function () {};";
        assert_eq!(codes(src, run_attribute_usages), ["attribute.target"]);
    }

    #[test]
    fn attribute_on_closure_function_target_is_clean() {
        let src = "<?php \
            #[\\Attribute(\\Attribute::TARGET_FUNCTION)] class A {} \
            $f = #[A] fn () => 1;";
        assert!(codes(src, run_attribute_usages).is_empty());
    }

    #[test]
    fn attribute_on_allowed_target_is_clean() {
        let src = "<?php \
            #[\\Attribute(\\Attribute::TARGET_CLASS)] class A {} \
            #[A] class B {}";
        assert!(codes(src, run_attribute_usages).is_empty());
    }

    #[test]
    fn attribute_all_target_is_clean() {
        // No args ⇒ TARGET_ALL.
        let src = "<?php #[\\Attribute] class A {} #[A] class B {}";
        assert!(codes(src, run_attribute_usages).is_empty());
    }

    #[test]
    fn non_attribute_class_used_as_attribute_is_flagged() {
        let src = "<?php class A {} #[A] class B {}";
        assert_eq!(codes(src, run_attribute_usages), ["attribute.notAttribute"]);
    }

    #[test]
    fn non_repeatable_attribute_used_twice_is_flagged() {
        let src = "<?php \
            #[\\Attribute(\\Attribute::TARGET_CLASS)] class A {} \
            #[A] #[A] class B {}";
        assert_eq!(codes(src, run_attribute_usages), ["attribute.nonRepeatable"]);
    }

    #[test]
    fn repeatable_attribute_used_twice_is_clean() {
        let src = "<?php \
            #[\\Attribute(\\Attribute::TARGET_CLASS | \\Attribute::IS_REPEATABLE)] class A {} \
            #[A] #[A] class B {}";
        assert!(codes(src, run_attribute_usages).is_empty());
    }

    #[test]
    fn attribute_on_method_target_check() {
        let src = "<?php \
            #[\\Attribute(\\Attribute::TARGET_CLASS)] class A {} \
            class B { #[A] public function m() {} }";
        assert_eq!(codes(src, run_attribute_usages), ["attribute.target"]);
    }

    #[test]
    fn unknown_attribute_class_is_not_flagged_here() {
        // Missing class -> class.notFound (a different rule), not attribute.*.
        let src = "<?php #[Nonexistent] class B {}";
        assert!(codes(src, run_attribute_usages).is_empty());
    }

    // --- instantiation ---------------------------------------------------

    #[test]
    fn new_interface_is_flagged() {
        let src = "<?php interface I {} new I();";
        assert_eq!(codes(src, run_instantiation), ["new.interface"]);
    }

    #[test]
    fn new_trait_is_flagged() {
        let src = "<?php trait T {} new T();";
        assert_eq!(codes(src, run_instantiation), ["new.trait"]);
    }

    #[test]
    fn new_enum_is_flagged() {
        let src = "<?php enum E {} new E();";
        assert_eq!(codes(src, run_instantiation), ["new.enum"]);
    }

    #[test]
    fn new_abstract_is_flagged() {
        let src = "<?php abstract class A {} new A();";
        assert_eq!(codes(src, run_instantiation), ["new.abstract"]);
    }

    #[test]
    fn new_concrete_class_is_clean() {
        let src = "<?php class C {} new C();";
        assert!(codes(src, run_instantiation).is_empty());
    }

    #[test]
    fn new_unknown_class_is_left_to_existence_check() {
        let src = "<?php new TotallyUnknown();";
        assert!(codes(src, run_instantiation).is_empty());
    }

    #[test]
    fn new_first_class_callable_is_not_instantiation() {
        // `new C(...)` is the callable rule's territory, not the kind rule's.
        let src = "<?php class C {} $f = new C(...);";
        assert!(codes(src, run_instantiation).is_empty());
        assert_eq!(codes(src, run_instantiation_callable), ["callable.notSupported"]);
    }

    // --- new static ------------------------------------------------------

    #[test]
    fn new_static_in_non_final_class_is_flagged() {
        let src = "<?php class C { public function make() { return new static(); } }";
        assert_eq!(codes(src, run_new_static), ["new.static"]);
    }

    #[test]
    fn new_static_in_final_class_is_clean() {
        let src = "<?php final class C { public function make() { return new static(); } }";
        assert!(codes(src, run_new_static).is_empty());
    }

    // --- extends / implements / use --------------------------------------

    #[test]
    fn class_extends_interface_is_flagged() {
        let src = "<?php interface I {} class C extends I {}";
        assert_eq!(codes(src, run_inheritance_kinds), ["class.extendsInterface"]);
    }

    #[test]
    fn class_extends_trait_is_flagged() {
        let src = "<?php trait T {} class C extends T {}";
        assert_eq!(codes(src, run_inheritance_kinds), ["class.extendsTrait"]);
    }

    #[test]
    fn class_extends_final_class_is_flagged() {
        let src = "<?php final class B {} class C extends B {}";
        assert_eq!(codes(src, run_inheritance_kinds), ["class.extendsFinal"]);
    }

    #[test]
    fn class_extends_normal_class_is_clean() {
        let src = "<?php class B {} class C extends B {}";
        assert!(codes(src, run_inheritance_kinds).is_empty());
    }

    #[test]
    fn class_implements_class_is_flagged() {
        let src = "<?php class B {} class C implements B {}";
        assert_eq!(codes(src, run_inheritance_kinds), ["classImplements.class"]);
    }

    #[test]
    fn class_implements_interface_is_clean() {
        let src = "<?php interface I {} class C implements I {}";
        assert!(codes(src, run_inheritance_kinds).is_empty());
    }

    #[test]
    fn interface_extends_class_is_flagged() {
        let src = "<?php class B {} interface I extends B {}";
        assert_eq!(codes(src, run_inheritance_kinds), ["interfaceExtends.class"]);
    }

    #[test]
    fn use_non_trait_is_flagged() {
        let src = "<?php class B {} class C { use B; }";
        assert_eq!(codes(src, run_inheritance_kinds), ["traitUse.class"]);
    }

    #[test]
    fn use_trait_is_clean() {
        let src = "<?php trait T {} class C { use T; }";
        assert!(codes(src, run_inheritance_kinds).is_empty());
    }

    #[test]
    fn interface_using_trait_is_flagged() {
        let src = "<?php trait T {} interface I { use T; }";
        assert_eq!(codes(src, run_inheritance_kinds), ["interface.traitUse"]);
    }

    // --- instanceof ------------------------------------------------------

    #[test]
    fn instanceof_trait_is_flagged() {
        let src = "<?php trait T {} function f($x) { return $x instanceof T; }";
        assert_eq!(codes(src, run_instanceof_kind), ["instanceof.trait"]);
    }

    #[test]
    fn instanceof_class_is_clean() {
        let src = "<?php class C {} function f($x) { return $x instanceof C; }";
        assert!(codes(src, run_instanceof_kind).is_empty());
    }

    // --- enum sanity -----------------------------------------------------

    #[test]
    fn enum_with_constructor_is_flagged() {
        let src = "<?php enum E { public function __construct() {} }";
        assert_eq!(codes(src, run_enum_sanity), ["enum.constructor"]);
    }

    #[test]
    fn enum_redeclaring_cases_is_flagged() {
        let src = "<?php enum E { public function cases(): array { return []; } }";
        assert_eq!(codes(src, run_enum_sanity), ["enum.methodRedeclaration"]);
    }

    #[test]
    fn enum_bad_backing_type_is_flagged() {
        let src = "<?php enum E: float { case A; }";
        // backingType + missing-value checks may both fire; backingType must appear.
        assert!(codes(src, run_enum_sanity).contains(&"enum.backingType"));
    }

    #[test]
    fn unbacked_enum_with_case_value_is_flagged() {
        let src = "<?php enum E { case A = 1; }";
        assert_eq!(codes(src, run_enum_sanity), ["enum.caseWithValue"]);
    }

    #[test]
    fn backed_enum_missing_value_is_flagged() {
        let src = "<?php enum E: int { case A; }";
        assert_eq!(codes(src, run_enum_sanity), ["enum.missingCase"]);
    }

    #[test]
    fn well_formed_backed_enum_is_clean() {
        let src = "<?php enum E: int { case A = 1; case B = 2; }";
        assert!(codes(src, run_enum_sanity).is_empty());
    }

    #[test]
    fn enum_allowed_magic_invoke_is_clean() {
        let src = "<?php enum E { public function __invoke() {} }";
        assert!(codes(src, run_enum_sanity).is_empty());
    }

    // --- duplicate member declaration ------------------------------------

    #[test]
    fn duplicate_method_is_flagged() {
        let src = "<?php class C { function f() {} function F() {} }";
        assert_eq!(codes(src, run_duplicate_declaration), ["class.duplicateMethod"]);
    }

    #[test]
    fn duplicate_property_is_flagged() {
        let src = "<?php class C { public $x; public $x; }";
        assert_eq!(codes(src, run_duplicate_declaration), ["class.duplicateProperty"]);
    }

    #[test]
    fn duplicate_constant_is_flagged() {
        let src = "<?php class C { const A = 1; const A = 2; }";
        assert_eq!(codes(src, run_duplicate_declaration), ["class.duplicateConstant"]);
    }

    #[test]
    fn duplicate_enum_case_is_flagged() {
        let src = "<?php enum E { case A; case A; }";
        assert_eq!(codes(src, run_duplicate_declaration), ["enum.duplicateEnumCase"]);
    }

    #[test]
    fn promoted_property_redeclaration_is_flagged() {
        let src = "<?php class C { public int $x; public function __construct(public int $x) {} }";
        assert_eq!(codes(src, run_duplicate_declaration), ["class.duplicateProperty"]);
    }

    #[test]
    fn distinct_members_are_clean() {
        let src = "<?php class C { function a() {} function b() {} public $x; public $y; }";
        assert!(codes(src, run_duplicate_declaration).is_empty());
    }

    // --- duplicate class declaration -------------------------------------

    #[test]
    fn duplicate_class_in_file_is_flagged() {
        let src = "<?php class C {} class C {}";
        assert_eq!(codes(src, run_duplicate_class), ["class.duplicate"]);
    }

    #[test]
    fn single_class_is_clean() {
        let src = "<?php class C {} class D {}";
        assert!(codes(src, run_duplicate_class).is_empty());
    }

    // --- #[Attribute] ----------------------------------------------------

    #[test]
    fn attribute_on_interface_is_flagged() {
        let src = "<?php #[Attribute] interface I {}";
        assert_eq!(codes(src, run_non_class_attribute), ["attribute.interface"]);
    }

    #[test]
    fn attribute_on_abstract_class_is_flagged() {
        let src = "<?php #[Attribute] abstract class A {}";
        assert_eq!(codes(src, run_non_class_attribute), ["attribute.abstract"]);
    }

    #[test]
    fn attribute_with_private_ctor_is_flagged() {
        let src = "<?php #[Attribute] class A { private function __construct() {} }";
        assert_eq!(codes(src, run_non_class_attribute), ["attribute.constructorNotPublic"]);
    }

    #[test]
    fn attribute_on_plain_class_is_clean() {
        let src = "<?php #[Attribute] class A { public function __construct() {} }";
        assert!(codes(src, run_non_class_attribute).is_empty());
    }

    // --- invalid promoted properties -------------------------------------

    #[test]
    fn promoted_outside_constructor_is_flagged() {
        let src = "<?php class C { public function set(public int $x) {} }";
        assert_eq!(codes(src, run_invalid_promoted), ["property.invalidPromoted"]);
    }

    #[test]
    fn variadic_promoted_property_is_flagged() {
        let src = "<?php class C { public function __construct(public int ...$x) {} }";
        assert_eq!(codes(src, run_invalid_promoted), ["property.invalidPromoted"]);
    }

    #[test]
    fn normal_promoted_property_is_clean() {
        let src = "<?php class C { public function __construct(public int $x) {} }";
        assert!(codes(src, run_invalid_promoted).is_empty());
    }

    // --- enum implements -------------------------------------------------

    #[test]
    fn enum_implements_class_is_flagged() {
        let src = "<?php class C {} enum E implements C {}";
        assert_eq!(codes(src, run_enum_implements), ["enumImplements.class"]);
    }

    #[test]
    fn enum_implements_trait_is_flagged() {
        let src = "<?php trait T {} enum E implements T {}";
        assert_eq!(codes(src, run_enum_implements), ["enumImplements.trait"]);
    }

    #[test]
    fn enum_implements_enum_is_flagged() {
        let src = "<?php enum F {} enum E implements F {}";
        assert_eq!(codes(src, run_enum_implements), ["enumImplements.enum"]);
    }

    #[test]
    fn enum_implements_interface_is_clean() {
        let src = "<?php interface I {} enum E implements I {}";
        assert!(codes(src, run_enum_implements).is_empty());
    }

    #[test]
    fn enum_implements_unknown_is_left_to_existence_check() {
        let src = "<?php enum E implements TotallyUnknown {}";
        assert!(codes(src, run_enum_implements).is_empty());
    }

    // --- class constant access -------------------------------------------

    #[test]
    fn undefined_class_constant_is_flagged() {
        let src = "<?php class C { const A = 1; } echo C::B;";
        assert_eq!(codes(src, run_class_constant), ["classConstant.notFound"]);
    }

    #[test]
    fn defined_class_constant_is_clean() {
        let src = "<?php class C { const A = 1; } echo C::A;";
        assert!(codes(src, run_class_constant).is_empty());
    }

    #[test]
    fn inherited_class_constant_is_clean() {
        let src = "<?php class B { const A = 1; } class C extends B {} echo C::A;";
        assert!(codes(src, run_class_constant).is_empty());
    }

    #[test]
    fn class_keyword_constant_is_never_flagged() {
        let src = "<?php class C {} echo C::class;";
        assert!(codes(src, run_class_constant).is_empty());
    }

    #[test]
    fn self_outside_class_is_flagged() {
        let src = "<?php echo self::FOO;";
        assert_eq!(codes(src, run_class_constant), ["outOfClass.self"]);
    }

    #[test]
    fn static_outside_class_is_flagged() {
        let src = "<?php echo static::FOO;";
        assert_eq!(codes(src, run_class_constant), ["outOfClass.static"]);
    }

    #[test]
    fn parent_outside_class_is_flagged() {
        let src = "<?php echo parent::FOO;";
        assert_eq!(codes(src, run_class_constant), ["outOfClass.parent"]);
    }

    #[test]
    fn parent_without_parent_class_is_flagged() {
        let src = "<?php class C { const X = 1; function f() { return parent::X; } }";
        assert_eq!(codes(src, run_class_constant), ["class.noParent"]);
    }

    #[test]
    fn constant_on_trait_is_flagged() {
        let src = "<?php trait T { const A = 1; } echo T::A;";
        assert_eq!(codes(src, run_class_constant), ["classConstant.onTrait"]);
    }

    #[test]
    fn private_constant_accessed_from_outside_is_flagged() {
        let src = "<?php class C { private const A = 1; } echo C::A;";
        assert_eq!(codes(src, run_class_constant), ["classConstant.private"]);
    }

    #[test]
    fn protected_constant_accessed_from_outside_is_flagged() {
        let src = "<?php class C { protected const A = 1; } echo C::A;";
        assert_eq!(codes(src, run_class_constant), ["classConstant.protected"]);
    }

    #[test]
    fn private_constant_accessed_from_same_class_is_clean() {
        let src = "<?php class C { private const A = 1; function f() { return self::A; } }";
        assert!(codes(src, run_class_constant).is_empty());
    }

    #[test]
    fn protected_constant_accessed_from_subclass_is_clean() {
        let src = "<?php class B { protected const A = 1; } \
            class C extends B { function f() { return self::A; } }";
        assert!(codes(src, run_class_constant).is_empty());
    }

    #[test]
    fn enum_case_access_is_clean() {
        let src = "<?php enum E { case A; } echo E::A->name;";
        assert!(codes(src, run_class_constant).is_empty());
    }

    #[test]
    fn class_constant_on_unknown_class_is_left_alone() {
        // Existence is class.notFound's job, not this rule's.
        let src = "<?php echo Unknown::FOO;";
        assert!(codes(src, run_class_constant).is_empty());
    }

    #[test]
    fn class_constant_with_unknown_parent_is_not_flagged() {
        // The constant could be inherited from the unindexed parent.
        let src = "<?php class C extends \\SomeBuiltinUnknown { } echo C::WHATEVER;";
        assert!(codes(src, run_class_constant).is_empty());
    }

    // --- private constant through static ---------------------------------

    #[test]
    fn private_const_through_static_in_non_final_is_flagged() {
        let src = "<?php class C { private const A = 1; \
            function f() { return static::A; } }";
        assert_eq!(
            codes(src, run_private_const_through_static),
            ["staticClassAccess.privateConstant"]
        );
    }

    #[test]
    fn private_const_through_static_in_final_is_clean() {
        let src = "<?php final class C { private const A = 1; \
            function f() { return static::A; } }";
        assert!(codes(src, run_private_const_through_static).is_empty());
    }

    #[test]
    fn public_const_through_static_is_clean() {
        let src = "<?php class C { public const A = 1; \
            function f() { return static::A; } }";
        assert!(codes(src, run_private_const_through_static).is_empty());
    }

    #[test]
    fn private_const_through_self_is_not_this_rule() {
        // `self::` is fine — only `static::` is unsafe for private constants.
        let src = "<?php class C { private const A = 1; \
            function f() { return self::A; } }";
        assert!(codes(src, run_private_const_through_static).is_empty());
    }

    // --- @mixin ----------------------------------------------------------

    #[test]
    fn mixin_non_object_is_flagged() {
        let src = "<?php /** @mixin int */ class C {}";
        assert_eq!(codes(src, run_mixin), ["mixin.nonObject"]);
    }

    #[test]
    fn mixin_trait_is_flagged() {
        let src = "<?php trait T {} /** @mixin T */ class C {}";
        assert_eq!(codes(src, run_mixin), ["mixin.trait"]);
    }

    #[test]
    fn mixin_class_is_clean() {
        let src = "<?php class M {} /** @mixin M */ class C {}";
        assert!(codes(src, run_mixin).is_empty());
    }

    #[test]
    fn mixin_unknown_class_is_left_to_existence_check() {
        let src = "<?php /** @mixin Unknown */ class C {}";
        assert!(codes(src, run_mixin).is_empty());
    }

    // --- new static() in abstract static method --------------------------

    #[test]
    fn new_static_in_abstract_static_method_is_flagged() {
        let src = "<?php abstract class C { \
            public static function make() { return new static(); } }";
        assert_eq!(
            codes(src, run_new_static_abstract),
            ["new.staticInAbstractClassStaticMethod"]
        );
    }

    #[test]
    fn new_static_in_abstract_instance_method_is_clean() {
        // Only static methods of abstract classes are unsafe in this rule.
        let src = "<?php abstract class C { \
            public function make() { return new static(); } }";
        assert!(codes(src, run_new_static_abstract).is_empty());
    }

    #[test]
    fn new_static_in_concrete_static_method_is_clean() {
        let src = "<?php class C { \
            public static function make() { return new static(); } }";
        assert!(codes(src, run_new_static_abstract).is_empty());
    }
}
