//! phpstan category **Properties** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Properties/`. These mirror phpstan's
//! property-declaration sanity checks (`ClassPropertyNode` rules), the
//! property-hook attribute target check (`InPropertyHookNode`), the override
//! compatibility checks (`OverridingPropertyRule`), undefined `$this->prop`
//! access (`AccessPropertiesRule`), and writes to a readonly property outside
//! the constructor (`ReadOnlyPropertyAssignRule`).
//!
//! All declaration-shape rules are purely syntactic over the AST (level 0):
//! readonly/static/default/visibility/abstract/final/hook conflicts that PHP's
//! compiler itself rejects. Access + readonly-assign use name resolution +
//! `reflection`, conservatively (only flag when the class + its full hierarchy
//! are known so we never produce a false positive on an unresolved type).
//!
//! Identifiers and messages match phpstan's wording wherever our AST allows.
//!
//! DEFERRED:
//! - `TypesAssignedToPropertiesRule` / `DefaultValueTypesAssignedToPropertiesRule`
//!   (`assign.propertyType`, `property.defaultValue`) — need inference of an
//!   assigned/default expression's TYPE vs the property type.
//! - `MissingReadOnlyPropertyAssignRule` (`property.uninitializedReadonly`) —
//!   needs constructor-flow analysis (which assignments definitely happen).
//! - `ReadOnlyByPhpDocPropertyRule` (`property.readOnlyByPhpDocDefaultValue`) —
//!   needs the parsed `@readonly` PHPDoc + `isAllowedPrivateMutation` flow.
//! - `PropertyAttributesRule` attribute-target body (`property.overrideAttribute`)
//!   — needs the (possibly cross-file) `#[Attribute(flags)]` of the attribute
//!   class to know its allowed targets. (We do the hook `nodiscard` variant,
//!   which is purely syntactic.)
//! - `OverridingPropertyRule` type parts (`property.nativeType`,
//!   `property.missingNativeType`, `property.parentPropertyFinalByPhpDoc`) —
//!   need native-type equality / PHPDoc `@final`. (We do the static / readonly /
//!   visibility / `#[\Override]` parts.)
//! - `SetPropertyHookParameterRule` (`propertySetHook.nativeParameterType`) —
//!   the real rule checks set-param type vs property type; needs the type system
//!   (variadic/by-ref params are rejected by PHP's own parser, not this rule).
//! - `NullsafePropertyFetchRule` (`nullsafe.neverNull`) — needs the receiver
//!   type (is it ever null?).
//! - `MissingPropertyTypehintRule` (`missingType.property`) — needs the merged
//!   readable type / explicit-mixed distinction from the type system.
//! - `AccessStaticPropertiesRule` / `ReadingWriteOnlyPropertiesRule` /
//!   property-hook get/set body rules — need expression-type inference of the
//!   access receiver / value, or virtual-property hook semantics beyond the AST.

use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{
    AttributeGroup, ClassDecl, ClassKind, Expr, ExprKind, HookBody, Member, MemberName, Name,
    Program, PropElem, PropertyDecl, Stmt, StmtKind, Visibility,
};
use php_diagnostics::Diagnostic;
use php_phpdoc::PropertyAccess;
use php_span::Span;
use php_types::Type;

// --- shared helpers --------------------------------------------------------

/// Does the property element carry a (possibly empty) hook block?
fn has_hooks(p: &PropElem) -> bool {
    p.hooks.as_ref().is_some_and(|h| !h.is_empty())
}

/// Best-effort span for a property element: its default's span, else its first
/// hook's short-body span, else a dummy span (PropElem has no span field; tests
/// assert identifiers, and locations matter only for rendering).
fn span_of(p: &PropElem) -> Span {
    if let Some(d) = &p.default {
        d.span
    } else if let Some(HookBody::Short(e)) = p.hooks.as_ref().and_then(|hs| hs.first()).map(|h| &h.body) {
        e.span
    } else {
        Span::DUMMY
    }
}

/// Walk every property declaration in the program together with the class it
/// belongs to. Property decls only live directly in class member lists, so we
/// recurse over statements (including conditional/nested classes) collecting
/// `(class, prop)` pairs.
fn for_each_property(program: &Program, f: &mut impl FnMut(&ClassDecl, &PropertyDecl)) {
    fn visit_stmts(stmts: &[Stmt], f: &mut impl FnMut(&ClassDecl, &PropertyDecl)) {
        for s in stmts {
            visit_stmt(s, f);
        }
    }
    fn visit_stmt(s: &Stmt, f: &mut impl FnMut(&ClassDecl, &PropertyDecl)) {
        match &s.kind {
            StmtKind::Class(c) => {
                for m in &c.members {
                    if let Member::Property(pd) = m {
                        f(c, pd);
                    }
                }
            }
            StmtKind::Namespace { body: Some(b), .. } => visit_stmts(b, f),
            StmtKind::Block(b) => visit_stmts(b, f),
            StmtKind::If { then, elseifs, els, .. } => {
                visit_stmt(then, f);
                for ei in elseifs {
                    visit_stmt(&ei.body, f);
                }
                if let Some(e) = els {
                    visit_stmt(e, f);
                }
            }
            StmtKind::Function(fd) => visit_stmts(&fd.body, f),
            _ => {}
        }
    }
    visit_stmts(&program.stmts, f);
}

// --- ReadOnlyPropertyRule (level 0) ----------------------------------------

/// phpstan `ReadOnlyPropertyRule`: a `readonly` property must have a native
/// type, must not have a default value, and must not be static.
fn run_readonly_property(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_property(fa.program, &mut |_class, pd| {
        if !pd.modifiers.is_readonly {
            return;
        }
        let span = pd.props.first().map(span_of).unwrap_or(Span::DUMMY);
        if pd.ty.is_none() {
            out.push(
                Diagnostic::error(span, "Readonly property must have a native type.")
                    .with_code("property.readOnlyNoNativeType"),
            );
        }
        if pd.modifiers.is_static {
            out.push(
                Diagnostic::error(span, "Readonly property cannot be static.")
                    .with_code("property.readOnlyStatic"),
            );
        }
        for elem in &pd.props {
            if let Some(d) = &elem.default {
                out.push(
                    Diagnostic::error(d.span, "Readonly property cannot have a default value.")
                        .with_code("property.readOnlyDefaultValue"),
                );
            }
        }
    });
    out
}

// --- PropertyInClassRule (level 0) -----------------------------------------

/// phpstan `PropertyInClassRule` (the AST-decidable subset): modifier conflicts
/// on a property *in a class* (not interface). Covers abstract/final/private,
/// abstract-vs-hooks, readonly/static-vs-hooks, and virtual default-value.
fn run_property_in_class(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_property(fa.program, &mut |class, pd| {
        if class.kind != ClassKind::Class {
            return; // interfaces handled by run_properties_in_interface
        }
        let m = &pd.modifiers;
        let any_hooks = pd.props.iter().any(has_hooks);
        let span = pd.props.first().map(span_of).unwrap_or(Span::DUMMY);

        if m.is_abstract {
            if !any_hooks {
                out.push(
                    Diagnostic::error(span, "Only hooked properties can be declared abstract.")
                        .with_code("property.abstractNonHooked"),
                );
            } else if !at_least_one_hook_abstract(pd) {
                out.push(
                    Diagnostic::error(
                        span,
                        "Abstract properties must specify at least one abstract hook.",
                    )
                    .with_code("property.abstractWithoutAbstractHook"),
                );
            } else if !class.modifiers.is_abstract {
                out.push(
                    Diagnostic::error(
                        span,
                        "Non-abstract classes cannot include abstract properties.",
                    )
                    .with_code("property.abstract"),
                );
            }
        } else if any_hooks && !all_hooks_have_body(pd) {
            out.push(
                Diagnostic::error(
                    span,
                    "Non-abstract properties cannot include hooks without bodies.",
                )
                .with_code("property.hookWithoutBody"),
            );
        }

        if m.visibility == Some(Visibility::Private) {
            if m.is_abstract {
                out.push(
                    Diagnostic::error(span, "Property cannot be both abstract and private.")
                        .with_code("property.abstractPrivate"),
                );
            }
            if m.is_final {
                out.push(
                    Diagnostic::error(span, "Property cannot be both final and private.")
                        .with_code("property.finalPrivate"),
                );
            }
            if any_final_hook(pd) {
                out.push(
                    Diagnostic::error(span, "Private property cannot have a final hook.")
                        .with_code("property.finalPrivateHook"),
                );
            }
        }

        if m.is_abstract && m.is_final {
            out.push(
                Diagnostic::error(span, "Property cannot be both abstract and final.")
                    .with_code("property.abstractFinal"),
            );
        }

        if m.is_readonly && any_hooks {
            out.push(
                Diagnostic::error(span, "Hooked properties cannot be readonly.")
                    .with_code("property.hookReadOnly"),
            );
        }

        if m.is_static && any_hooks {
            out.push(
                Diagnostic::error(span, "Hooked properties cannot be static.")
                    .with_code("property.hookedStatic"),
            );
        }

        // A hooked (virtual) property cannot have a default value.
        for elem in &pd.props {
            if has_hooks(elem) {
                if let Some(d) = &elem.default {
                    out.push(
                        Diagnostic::error(
                            d.span,
                            "Virtual hooked properties cannot have a default value.",
                        )
                        .with_code("property.virtualDefault"),
                    );
                }
            }
        }
    });
    out
}

fn at_least_one_hook_abstract(pd: &PropertyDecl) -> bool {
    pd.props.iter().any(|p| {
        p.hooks
            .as_ref()
            .is_some_and(|hs| hs.iter().any(|h| matches!(h.body, HookBody::Abstract)))
    })
}

fn all_hooks_have_body(pd: &PropertyDecl) -> bool {
    pd.props.iter().all(|p| {
        p.hooks
            .as_ref()
            .is_none_or(|hs| hs.iter().all(|h| !matches!(h.body, HookBody::Abstract)))
    })
}

fn any_final_hook(pd: &PropertyDecl) -> bool {
    pd.props
        .iter()
        .any(|p| p.hooks.as_ref().is_some_and(|hs| hs.iter().any(|h| h.modifiers.is_final)))
}

fn any_hook_has_body(pd: &PropertyDecl) -> bool {
    pd.props.iter().any(|p| {
        p.hooks
            .as_ref()
            .is_some_and(|hs| hs.iter().any(|h| !matches!(h.body, HookBody::Abstract)))
    })
}

// --- PropertiesInInterfaceRule (level 0) -----------------------------------

/// phpstan `PropertiesInInterfaceRule`: properties in an interface must be
/// hooked, public, non-readonly, non-static, not explicitly abstract/final, and
/// their hooks must have no bodies. (PHP 8.4+ — we always target 8.6.) phpstan
/// returns on the FIRST matching error per property, in this exact order.
fn run_properties_in_interface(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_property(fa.program, &mut |class, pd| {
        if class.kind != ClassKind::Interface {
            return;
        }
        let m = &pd.modifiers;
        let any_hooks = pd.props.iter().any(has_hooks);
        let span = pd.props.first().map(span_of).unwrap_or(Span::DUMMY);

        if !any_hooks {
            out.push(
                Diagnostic::error(span, "Interfaces can only include hooked properties.")
                    .with_code("property.nonHookedInInterface"),
            );
            return;
        }
        if m.visibility.is_some_and(|v| v != Visibility::Public) {
            out.push(
                Diagnostic::error(span, "Interfaces cannot include non-public properties.")
                    .with_code("property.nonPublicInInterface"),
            );
            return;
        }
        if m.is_readonly {
            out.push(
                Diagnostic::error(span, "Interfaces cannot include readonly hooked properties.")
                    .with_code("property.readOnlyInInterface"),
            );
            return;
        }
        if m.is_static {
            out.push(
                Diagnostic::error(span, "Hooked properties cannot be static.")
                    .with_code("property.hookedStatic"),
            );
            return;
        }
        if m.is_abstract {
            out.push(
                Diagnostic::error(span, "Property in interface cannot be explicitly abstract.")
                    .with_code("property.abstractInInterface"),
            );
            return;
        }
        if m.is_final {
            out.push(
                Diagnostic::error(span, "Interfaces cannot include final properties.")
                    .with_code("property.finalInInterface"),
            );
            return;
        }
        if any_final_hook(pd) {
            out.push(
                Diagnostic::error(span, "Property hook cannot be both abstract and final.")
                    .with_code("property.abstractFinalHook"),
            );
            return;
        }
        if any_hook_has_body(pd) {
            out.push(
                Diagnostic::error(span, "Interfaces cannot include property hooks with bodies.")
                    .with_code("property.hookBodyInInterface"),
            );
        }
    });
    out
}

// --- PropertyHookAttributesRule (level 0, partial) -------------------------

/// phpstan `PropertyHookAttributesRule` (the syntactic part): the `#[NoDiscard]`
/// attribute cannot be used on property hooks. (The general TARGET_METHOD
/// attribute check needs the attribute class's reflection and is deferred.)
fn run_property_hook_attributes(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_property(fa.program, &mut |_class, pd| {
        for elem in &pd.props {
            let Some(hooks) = &elem.hooks else { continue };
            for hook in hooks {
                for group in &hook.attrs {
                    for attr in &group.attrs {
                        let name = attr.name.text.trim_start_matches('\\');
                        if name.eq_ignore_ascii_case("nodiscard") {
                            out.push(
                                Diagnostic::error(
                                    attr.name.span,
                                    format!(
                                        "Attribute class {name} cannot be used on property hooks."
                                    ),
                                )
                                .with_code("attribute.target"),
                            );
                        }
                    }
                }
            }
        }
    });
    out
}

// --- OverridingPropertyRule (level 0) --------------------------------------

/// phpstan `OverridingPropertyRule` (the AST + reflection-decidable subset): a
/// property that overrides a property of a parent class must keep the parent's
/// static-ness, readonly-ness, and not narrow its visibility; an `#[\Override]`
/// attribute must override something. The native-type-equality / `@final`-by-
/// PHPDoc parts (which need type comparison) are deferred.
///
/// The prototype is looked up in the parent class's hierarchy (`find_property`
/// ascends own-first, so we search each parent rather than the class itself).
fn run_overriding_property(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_property(fa.program, &mut |class, pd| {
        // Resolve the parent property (prototype) once per declaration name.
        for elem in &pd.props {
            let prop = fa.interner.resolve(elem.name).to_string();
            let proto = class
                .extends
                .iter()
                .find_map(|p| fa.reflection.find_property(p.text.trim_start_matches('\\'), &prop));
            let has_override = has_override_attr(&pd.attrs);
            let span = span_of(elem);

            let Some(proto) = proto else {
                if has_override {
                    out.push(
                        Diagnostic::error(
                            span,
                            format!(
                                "Property {}::${prop} has #[\\Override] attribute but does not override any property.",
                                class_name(class, fa)
                            ),
                        )
                        .with_code("property.override"),
                    );
                }
                continue;
            };
            let parent = &proto.declaring_class;

            if has_override_should_be_present(class, has_override) {
                out.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "Property {}::${prop} overrides property {parent}::${prop} but is missing the #[\\Override] attribute.",
                            class_name(class, fa)
                        ),
                    )
                    .with_code("property.missingOverride"),
                );
            }

            let m = &pd.modifiers;
            if proto.member.is_static && !m.is_static {
                out.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "Non-static property {}::${prop} overrides static property {parent}::${prop}.",
                            class_name(class, fa)
                        ),
                    )
                    .with_code("property.nonStatic"),
                );
            } else if !proto.member.is_static && m.is_static {
                out.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "Static property {}::${prop} overrides non-static property {parent}::${prop}.",
                            class_name(class, fa)
                        ),
                    )
                    .with_code("property.static"),
                );
            }

            if proto.member.is_readonly && !m.is_readonly {
                out.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "Readwrite property {}::${prop} overrides readonly property {parent}::${prop}.",
                            class_name(class, fa)
                        ),
                    )
                    .with_code("property.readWrite"),
                );
            } else if !proto.member.is_readonly && m.is_readonly {
                out.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "Readonly property {}::${prop} overrides readwrite property {parent}::${prop}.",
                            class_name(class, fa)
                        ),
                    )
                    .with_code("property.readOnly"),
                );
            }

            // Visibility may not be narrowed.
            let own_vis = m.visibility.unwrap_or(Visibility::Public);
            if proto.member.visibility == Visibility::Public && own_vis != Visibility::Public {
                let kind = if own_vis == Visibility::Private { "Private" } else { "Protected" };
                out.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "{kind} property {}::${prop} overriding public property {parent}::${prop} should also be public.",
                            class_name(class, fa)
                        ),
                    )
                    .with_code("property.visibility"),
                );
            } else if proto.member.visibility == Visibility::Protected
                && own_vis == Visibility::Private
            {
                out.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "Private property {}::${prop} overriding protected property {parent}::${prop} should be protected or public.",
                            class_name(class, fa)
                        ),
                    )
                    .with_code("property.visibility"),
                );
            }
        }
    });
    out
}

fn has_override_attr(attrs: &[AttributeGroup]) -> bool {
    attrs.iter().any(|g| {
        g.attrs
            .iter()
            .any(|a| a.name.text.trim_start_matches('\\').eq_ignore_ascii_case("Override"))
    })
}

/// phpstan reports `missingOverride` only when the overriding class is not a
/// trait and the `#[\Override]` attribute is absent. (The configurable
/// `checkMissingOverrideMethodAttribute` defaults to on for our target version.)
fn has_override_should_be_present(class: &ClassDecl, has_override: bool) -> bool {
    class.kind != ClassKind::Trait && !has_override
}

fn class_name(class: &ClassDecl, fa: &FileAnalysis) -> String {
    class.name.map(|n| fa.interner.resolve(n).to_string()).unwrap_or_else(|| "class@anonymous".into())
}

// --- AccessPropertiesRule (level 0, $this only) ----------------------------

/// phpstan `AccessPropertiesRule` (conservative subset): `$this->prop` where the
/// enclosing class is fully known and `prop` is not defined anywhere in its
/// hierarchy. Only fires when the class + all of its ancestors are present in
/// the reflection index and the class has no `__get` magic accessor — so an
/// unresolved type never yields a false positive.
fn run_access_properties(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk_scoped(&fa.program.stmts, None, "", fa, &mut out, &mut |class, e, fa, out| {
        if let ExprKind::Prop { base, name, .. } = &e.kind {
            if let (ExprKind::Variable(v), MemberName::Ident(p)) = (&base.kind, name) {
                if fa.interner.resolve(*v) == "this" {
                    let prop = fa.interner.resolve(*p);
                    if class_is_fully_known(class, fa)
                        && fa.reflection.find_property(class, prop).is_none()
                        && fa.reflection.find_method(class, "__get").is_none()
                    {
                        out.push(
                            Diagnostic::error(
                                e.span,
                                format!("Access to an undefined property {class}::${prop}."),
                            )
                            .with_code("property.notFound"),
                        );
                    }
                }
            }
        }
    });
    out
}

// --- ReadOnlyPropertyAssignRule (level 3, $this outside ctor) --------------

/// phpstan `ReadOnlyPropertyAssignRule` (conservative subset): assigning to a
/// `readonly` property `$this->p` from a method other than the constructor of
/// the declaring class. Only fires when the property is known-readonly via
/// reflection.
fn run_readonly_property_assign(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk_scoped_methods(&fa.program.stmts, None, false, "", fa, &mut out, &mut |class, in_ctor, e, fa, out| {
        if in_ctor {
            return;
        }
        let target = match &e.kind {
            ExprKind::Assign { target, .. }
            | ExprKind::AssignRef { target, .. }
            | ExprKind::AssignOp { target, .. } => target,
            _ => return,
        };
        if let ExprKind::Prop { base, name, .. } = &target.kind {
            if let (ExprKind::Variable(v), MemberName::Ident(p)) = (&base.kind, name) {
                if fa.interner.resolve(*v) == "this" {
                    let prop = fa.interner.resolve(*p);
                    if let Some(found) = fa.reflection.find_property(class, prop) {
                        if found.member.is_readonly {
                            out.push(
                                Diagnostic::error(
                                    e.span,
                                    format!(
                                        "Readonly property {}::${prop} is assigned outside of the constructor.",
                                        found.declaring_class
                                    ),
                                )
                                .with_code("property.readOnlyAssignNotInConstructor"),
                            );
                        }
                    }
                }
            }
        }
    });
    out
}

// --- scope-tracking traversal for the `$this`-based rules ------------------

/// Walk statements, tracking the enclosing class name (so `$this` resolves), and
/// invoke `on_expr(class, expr, fa, out)` for every expression inside a method
/// body of a *named* class. Closures inherit `$this`; nested functions/classes
/// reset the scope.
/// Qualify a class's declared (unqualified) name with the current namespace to
/// the FQN under which it is stored in the reflection index. Class *declarations*
/// are unaffected by `use` imports, so this is a plain namespace prefix.
fn qualify_fqn(ns: &str, name: &str) -> String {
    if ns.is_empty() {
        name.to_string()
    } else {
        format!("{ns}\\{name}")
    }
}

/// The namespace name a `namespace` statement introduces (sans leading `\`).
fn ns_of(name: &Option<Name>) -> String {
    name.as_ref().map(|n| n.text.trim_start_matches('\\').to_string()).unwrap_or_default()
}

fn walk_scoped(
    stmts: &[Stmt],
    cur_class: Option<&str>,
    ns: &str,
    fa: &FileAnalysis,
    out: &mut Vec<Diagnostic>,
    on_expr: &mut impl FnMut(&str, &Expr, &FileAnalysis, &mut Vec<Diagnostic>),
) {
    // The unbraced `namespace Foo;` form applies to its following siblings.
    let mut cur_ns = ns.to_string();
    for s in stmts {
        match &s.kind {
            StmtKind::Class(c) => {
                let fqn = c.name.map(|n| qualify_fqn(&cur_ns, fa.interner.resolve(n)));
                for m in &c.members {
                    if let Member::Method(md) = m {
                        if let Some(body) = &md.body {
                            walk_scoped(body, fqn.as_deref(), &cur_ns, fa, out, on_expr);
                        }
                    }
                }
            }
            StmtKind::Namespace { name, body: Some(b) } => {
                walk_scoped(b, None, &ns_of(name), fa, out, on_expr)
            }
            StmtKind::Namespace { name, body: None } => cur_ns = ns_of(name),
            StmtKind::Function(fd) => walk_scoped(&fd.body, None, &cur_ns, fa, out, on_expr),
            _ => {
                if let Some(class) = cur_class {
                    stmt_exprs(s, &mut |e| on_expr(class, e, fa, out));
                }
            }
        }
    }
}

/// Like [`walk_scoped`] but also tracks whether the current method is the
/// constructor.
fn walk_scoped_methods(
    stmts: &[Stmt],
    cur_class: Option<&str>,
    in_ctor: bool,
    ns: &str,
    fa: &FileAnalysis,
    out: &mut Vec<Diagnostic>,
    on_expr: &mut impl FnMut(&str, bool, &Expr, &FileAnalysis, &mut Vec<Diagnostic>),
) {
    let mut cur_ns = ns.to_string();
    for s in stmts {
        match &s.kind {
            StmtKind::Class(c) => {
                let fqn = c.name.map(|n| qualify_fqn(&cur_ns, fa.interner.resolve(n)));
                for m in &c.members {
                    if let Member::Method(md) = m {
                        if let Some(body) = &md.body {
                            let is_ctor =
                                fa.interner.resolve(md.name).eq_ignore_ascii_case("__construct");
                            walk_scoped_methods(body, fqn.as_deref(), is_ctor, &cur_ns, fa, out, on_expr);
                        }
                    }
                }
            }
            StmtKind::Namespace { name, body: Some(b) } => {
                walk_scoped_methods(b, None, in_ctor, &ns_of(name), fa, out, on_expr)
            }
            StmtKind::Namespace { name, body: None } => cur_ns = ns_of(name),
            StmtKind::Function(fd) => {
                walk_scoped_methods(&fd.body, None, false, &cur_ns, fa, out, on_expr)
            }
            _ => {
                if let Some(class) = cur_class {
                    stmt_exprs(s, &mut |e| on_expr(class, in_ctor, e, fa, out));
                }
            }
        }
    }
}

/// Visit every expression in a single statement (and its nested non-declaration
/// statements), descending into closures/arrow-fns (they inherit `$this`) but
/// NOT into nested class/function declarations (which change the `$this` scope —
/// those are handled by the scope-tracking caller).
fn stmt_exprs(s: &Stmt, on_expr: &mut impl FnMut(&Expr)) {
    match &s.kind {
        StmtKind::Class(_) | StmtKind::Function(_) => {}
        StmtKind::Expr(e) => walk_expr_local(e, on_expr),
        StmtKind::Echo(es) | StmtKind::Global(es) | StmtKind::Unset(es) => {
            es.iter().for_each(|e| walk_expr_local(e, on_expr))
        }
        StmtKind::Return(Some(e)) => walk_expr_local(e, on_expr),
        StmtKind::Block(b) => b.iter().for_each(|st| stmt_exprs(st, on_expr)),
        StmtKind::If { cond, then, elseifs, els } => {
            walk_expr_local(cond, on_expr);
            stmt_exprs(then, on_expr);
            for ei in elseifs {
                walk_expr_local(&ei.cond, on_expr);
                stmt_exprs(&ei.body, on_expr);
            }
            if let Some(e) = els {
                stmt_exprs(e, on_expr);
            }
        }
        StmtKind::While { cond, body } => {
            walk_expr_local(cond, on_expr);
            stmt_exprs(body, on_expr);
        }
        StmtKind::DoWhile { body, cond } => {
            stmt_exprs(body, on_expr);
            walk_expr_local(cond, on_expr);
        }
        StmtKind::For { init, cond, update, body } => {
            for e in init.iter().chain(cond).chain(update) {
                walk_expr_local(e, on_expr);
            }
            stmt_exprs(body, on_expr);
        }
        StmtKind::Foreach { subject, key, value, body, .. } => {
            walk_expr_local(subject, on_expr);
            if let Some(k) = key {
                walk_expr_local(k, on_expr);
            }
            walk_expr_local(value, on_expr);
            stmt_exprs(body, on_expr);
        }
        StmtKind::Switch { subject, cases } => {
            walk_expr_local(subject, on_expr);
            for c in cases {
                if let Some(t) = &c.test {
                    walk_expr_local(t, on_expr);
                }
                c.body.iter().for_each(|st| stmt_exprs(st, on_expr));
            }
        }
        StmtKind::Try { body, catches, finally } => {
            body.iter().for_each(|st| stmt_exprs(st, on_expr));
            for c in catches {
                c.body.iter().for_each(|st| stmt_exprs(st, on_expr));
            }
            if let Some(f) = finally {
                f.iter().for_each(|st| stmt_exprs(st, on_expr));
            }
        }
        _ => {}
    }
}

/// Visit `e` and every sub-expression, descending into closures/arrow-fns but
/// not into nested class/function declarations.
fn walk_expr_local(e: &Expr, on_expr: &mut impl FnMut(&Expr)) {
    on_expr(e);
    let mut go = |x: &Expr| walk_expr_local(x, on_expr);
    match &e.kind {
        ExprKind::Interpolated(parts) | ExprKind::ShellExec(parts) | ExprKind::Isset(parts) => {
            parts.iter().for_each(&mut go)
        }
        ExprKind::VariableVariable(x) | ExprKind::DollarBrace(x) | ExprKind::Paren(x) => go(x),
        ExprKind::Array { items, .. } => {
            for it in items {
                if let Some(k) = &it.key {
                    go(k);
                }
                if let Some(v) = &it.value {
                    go(v);
                }
            }
        }
        ExprKind::Call { callee, args } => {
            go(callee);
            args.iter().for_each(|a| go(&a.value));
        }
        ExprKind::MethodCall { recv, args, .. } => {
            go(recv);
            args.iter().for_each(|a| go(&a.value));
        }
        ExprKind::StaticCall { class, args, .. } => {
            go(class);
            args.iter().for_each(|a| go(&a.value));
        }
        ExprKind::New { class, args } => {
            go(class);
            args.iter().for_each(|a| go(&a.value));
        }
        ExprKind::Index { base, index } => {
            go(base);
            if let Some(i) = index {
                go(i);
            }
        }
        ExprKind::Prop { base, .. } => go(base),
        ExprKind::StaticProp { class, .. } | ExprKind::ClassConst { class, .. } => go(class),
        ExprKind::Unary { expr, .. } | ExprKind::Cast { expr, .. } => go(expr),
        ExprKind::Binary { lhs, rhs, .. }
        | ExprKind::Assign { target: lhs, rhs }
        | ExprKind::AssignOp { target: lhs, rhs, .. }
        | ExprKind::AssignRef { target: lhs, rhs }
        | ExprKind::Coalesce { lhs, rhs } => {
            go(lhs);
            go(rhs);
        }
        ExprKind::Ternary { cond, then, els } => {
            go(cond);
            if let Some(t) = then {
                go(t);
            }
            go(els);
        }
        ExprKind::PreInc(x) | ExprKind::PreDec(x) | ExprKind::PostInc(x) | ExprKind::PostDec(x) => {
            go(x)
        }
        ExprKind::Instanceof { expr, class } => {
            go(expr);
            go(class);
        }
        ExprKind::Clone(x)
        | ExprKind::Print(x)
        | ExprKind::Throw(x)
        | ExprKind::ErrorSuppress(x)
        | ExprKind::YieldFrom(x)
        | ExprKind::Eval(x)
        | ExprKind::Empty(x) => go(x),
        ExprKind::Yield { key, value } => {
            if let Some(k) = key {
                go(k);
            }
            if let Some(v) = value {
                go(v);
            }
        }
        ExprKind::Exit(Some(x)) => go(x),
        ExprKind::Match { subject, arms } => {
            go(subject);
            for arm in arms {
                if let Some(conds) = &arm.conds {
                    conds.iter().for_each(&mut go);
                }
                go(&arm.body);
            }
        }
        ExprKind::Include { expr, .. } => go(expr),
        ExprKind::Closure(c) => {
            c.body.iter().for_each(|st| stmt_exprs(st, on_expr));
        }
        ExprKind::ArrowFn(a) => {
            walk_expr_local(&a.body, on_expr);
        }
        _ => {}
    }
}

/// Conservative: the class and every ancestor it names are present in the
/// reflection index (no unknown parent/interface/trait/mixin that might declare
/// the property).
fn class_is_fully_known(fqn: &str, fa: &FileAnalysis) -> bool {
    fn known(fqn: &str, fa: &FileAnalysis, seen: &mut Vec<String>) -> bool {
        let key = fqn.trim_start_matches('\\').to_ascii_lowercase();
        if seen.contains(&key) {
            return true;
        }
        seen.push(key);
        let Some(c) = fa.reflection.class(fqn) else { return false };
        c.parents
            .iter()
            .chain(&c.interfaces)
            .chain(&c.traits)
            .chain(&c.mixins)
            .all(|t| match t {
                php_types::Type::Named { fqn, .. } => known(fqn, fa, seen),
                _ => true,
            })
    }
    known(fqn, fa, &mut Vec::new())
}

// --- type helpers (general property access) ---------------------------------

/// If `ty` denotes a single, concrete object class (directly or under one level
/// of nullable/parens), return its FQN (sans leading `\`). Returns `None` for
/// unions of classes, `mixed`/`object`/unknown, scalars, generics-bound vars,
/// `self`/`static`/`parent`, etc. — anything we cannot pin to one named class.
/// This is what keeps the access rules false-positive-free: we only judge a
/// receiver whose class is unambiguous.
fn sole_class(ty: &Type) -> Option<String> {
    match ty {
        Type::Named { fqn, .. } => Some(fqn.trim_start_matches('\\').to_string()),
        // `?C` / `C|null`: the access itself is a *different* (nullable) problem;
        // for member existence we still know the non-null part is exactly `C`.
        Type::Nullable(inner) => sole_class(inner),
        _ => None,
    }
}

/// Conservative: the class and *every* ancestor it names are present in the
/// reflection index (so no unknown parent/interface/trait/mixin can secretly
/// declare the member). Shared with the `$this` rule's notion above.
fn known_class_tree(fqn: &str, fa: &FileAnalysis) -> bool {
    class_is_fully_known(fqn, fa)
}

/// Does `class_fqn` (or its hierarchy) declare a magic `__get`/`__set` that would
/// make any property access legal? If so we never flag undefined properties.
fn has_magic_accessor(fqn: &str, fa: &FileAnalysis, write: bool) -> bool {
    let getset = if write { "__set" } else { "__get" };
    fa.reflection.find_method(fqn, getset).is_some()
}

// --- AccessPropertiesRule (level 0, general receiver) ----------------------

/// phpstan `AccessPropertiesRule` (`AccessPropertiesCheck`), the FP-safe subset
/// for an *arbitrary* receiver `$obj->prop`: when `$obj` has a single, concrete,
/// fully-known class and the property is absent from its hierarchy (and there is
/// no `__get`), emit `property.notFound`.
///
/// This complements [`run_access_properties`] (which only covers `$this->p`) by
/// using inferred receiver types. `$this` receivers are skipped here (handled by
/// that rule) so we don't double-report. Visibility (`property.private`/
/// `.protected`) is deferred — see [`check_property_access`].
fn run_access_properties_general(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    // Property fetches that are assignment targets are checked (as writes) by
    // run_access_properties_in_assign — exclude them here so we don't
    // double-report (mirrors phpstan's `isInExpressionAssign` skip).
    let assign_targets = assignment_target_spans(fa.program);
    walk::for_each_expr(fa.program, &mut |e: &Expr| {
        if let ExprKind::Prop { base, name, nullsafe } = &e.kind {
            let r = e.span.range();
            if assign_targets.contains(&(r.start as u32, r.end as u32)) {
                return;
            }
            check_property_access(fa, e, base, name, *nullsafe, false, &mut out);
        }
    });
    out
}

/// Spans of every property fetch used as a plain assignment / assign-ref target
/// (these are pure writes, checked by run_access_properties_in_assign). Compound
/// assignments (`+=`) are reads too, so they are NOT excluded here.
fn assignment_target_spans(program: &Program) -> Vec<(u32, u32)> {
    let mut spans = Vec::new();
    walk::for_each_expr(program, &mut |e: &Expr| {
        let (ExprKind::Assign { target, .. } | ExprKind::AssignRef { target, .. }) = &e.kind else {
            return;
        };
        if matches!(&target.kind, ExprKind::Prop { .. }) {
            let r = target.span.range();
            spans.push((r.start as u32, r.end as u32));
        }
    });
    spans
}

/// The write-side (`AccessPropertiesInAssignRule`): same check, but on the target
/// of an assignment, judging *write* access (so a `private(set)`-ish member could
/// differ — but our model has no asymmetric-visibility split, so for writes we
/// only report `notFound`, never private/protected, to stay FP-safe).
fn run_access_properties_in_assign(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    // Walk every assignment whose target is a (non-`$this`) property fetch.
    walk::for_each_expr(fa.program, &mut |e: &Expr| {
        let (ExprKind::Assign { target, .. } | ExprKind::AssignRef { target, .. }) = &e.kind else {
            return;
        };
        if let ExprKind::Prop { base, name, nullsafe } = &target.kind {
            check_property_access(fa, target, base, name, *nullsafe, true, &mut out);
        }
    });
    out
}

/// The shared per-fetch check: when `base` has a single, fully-known concrete
/// class and `prop` is absent from its hierarchy (and there is no `__get`/`__set`
/// magic accessor for the access direction), emit `property.notFound`.
///
/// Visibility (`property.private`/`property.protected`) is intentionally NOT
/// reported here: deciding it correctly needs the enclosing-class context to know
/// whether the access is inside the hierarchy, and getting that wrong produces
/// false positives. We only emit the unambiguous `notFound`. `$this->p` is
/// handled by [`run_access_properties`] and skipped here to avoid duplicates.
#[allow(clippy::too_many_arguments)]
fn check_property_access(
    fa: &FileAnalysis,
    fetch: &Expr,
    base: &Expr,
    name: &MemberName,
    _nullsafe: bool,
    write: bool,
    out: &mut Vec<Diagnostic>,
) {
    if matches!(&base.kind, ExprKind::Variable(v) if fa.interner.resolve(*v) == "this") {
        return;
    }
    let MemberName::Ident(p) = name else { return }; // dynamic `$o->$x` — skip.
    let prop = fa.interner.resolve(*p);

    let Some(class) = sole_class(&fa.type_of(base)) else { return };
    if !known_class_tree(&class, fa) {
        return; // unresolved hierarchy → no judgement.
    }
    if fa.reflection.find_property(&class, prop).is_some() || has_magic_accessor(&class, fa, write) {
        return;
    }
    out.push(
        Diagnostic::error(
            fetch.span,
            format!("Access to an undefined property {}::${prop}.", class.trim_start_matches('\\')),
        )
        .with_code("property.notFound"),
    );
}

// --- AccessStaticPropertiesRule (level 0) ----------------------------------

/// phpstan `AccessStaticPropertiesRule` (`AccessStaticPropertiesCheck`), FP-safe
/// subset: `Foo::$bar` where `Foo` resolves to a single, fully-known class and
/// `$bar` is absent from its hierarchy → `staticProperty.notFound`. `self`/
/// `static`/`parent` and dynamic names are skipped (they need richer scope).
fn run_access_static_properties(fa: &FileAnalysis) -> Vec<Diagnostic> {
    use php_resolve::for_each_region;
    let mut out = Vec::new();
    // Static-property fetches that are plain assignment targets are checked (as
    // writes) by run_access_static_properties_in_assign — exclude them here so we
    // don't double-report (mirrors phpstan's read/assign rule split).
    let assign_targets = static_assign_target_spans(fa.program);
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for s in region {
            walk_region_exprs(s, &mut |e: &Expr| {
                let ExprKind::StaticProp { .. } = &e.kind else { return };
                let r = e.span.range();
                if assign_targets.contains(&(r.start as u32, r.end as u32)) {
                    return;
                }
                if let Some(d) = check_static_property(fa, scope, e) {
                    out.push(d);
                }
            });
        }
    });
    out
}

/// Spans of every static-property fetch used as a plain assignment / assign-ref
/// target (pure writes, checked by run_access_static_properties_in_assign).
/// Compound assignments (`+=`) are reads too, so they are NOT excluded.
fn static_assign_target_spans(program: &Program) -> Vec<(u32, u32)> {
    let mut spans = Vec::new();
    walk::for_each_expr(program, &mut |e: &Expr| {
        let (ExprKind::Assign { target, .. } | ExprKind::AssignRef { target, .. }) = &e.kind else {
            return;
        };
        if matches!(&target.kind, ExprKind::StaticProp { .. }) {
            let r = target.span.range();
            spans.push((r.start as u32, r.end as u32));
        }
    });
    spans
}

/// Shared per-fetch check for `C::$prop`: when `C` resolves to a single,
/// fully-known class and `$prop` is absent from its hierarchy, return a
/// `staticProperty.notFound` diagnostic. `self`/`static`/`parent` and dynamic
/// names are skipped (they need richer enclosing-class scope).
fn check_static_property(
    fa: &FileAnalysis,
    scope: &php_resolve::Scope,
    e: &Expr,
) -> Option<Diagnostic> {
    use php_resolve::Resolution;
    let ExprKind::StaticProp { class, name } = &e.kind else { return None };
    // `C::$b` — the static-property name is the `$b` variable token.
    let MemberName::Var(p) = name else { return None };
    let ExprKind::Name(n) = &class.kind else { return None };
    // Skip self/static/parent — need enclosing-class context.
    let fqn = match scope.resolve_class(n) {
        Resolution::Fqn(f) => f.trim_start_matches('\\').to_string(),
        _ => return None,
    };
    if !known_class_tree(&fqn, fa) {
        return None;
    }
    let prop = fa.interner.resolve(*p);
    if fa.reflection.find_property(&fqn, prop).is_some() {
        return None;
    }
    Some(
        Diagnostic::error(
            e.span,
            format!(
                "Access to an undefined static property {}::${prop}.",
                fqn.trim_start_matches('\\')
            ),
        )
        .with_code("staticProperty.notFound"),
    )
}

// --- AccessStaticPropertiesInAssignRule (level 0) --------------------------

/// phpstan `AccessStaticPropertiesInAssignRule` (`staticProperty.notFound`): the
/// write-side counterpart of [`run_access_static_properties`]. A plain assignment
/// `C::$bar = …` whose target static property is undefined on a fully-known class.
/// Compound assignments (`+=`) are skipped (phpstan's `isAssignOp()` guard) — they
/// are reads, already covered by the read rule. FP-safe via `known_class_tree`.
fn run_access_static_properties_in_assign(fa: &FileAnalysis) -> Vec<Diagnostic> {
    use php_resolve::for_each_region;
    let mut out = Vec::new();
    // Collect the spans of static-prop assignment targets first; then judge each in
    // its region scope (so `C` resolves with the file's imports).
    let targets = static_assign_target_spans(fa.program);
    if targets.is_empty() {
        return out;
    }
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for s in region {
            walk_region_exprs(s, &mut |e: &Expr| {
                let ExprKind::StaticProp { .. } = &e.kind else { return };
                let r = e.span.range();
                if !targets.contains(&(r.start as u32, r.end as u32)) {
                    return;
                }
                if let Some(d) = check_static_property(fa, scope, e) {
                    out.push(d);
                }
            });
        }
    });
    out
}

/// Walk every expression inside a statement (region-level), descending into all
/// bodies via the shared cross-scope walker semantics. We only need expressions,
/// so reuse `walk_expr_local`/`stmt_exprs` which already descend into closures.
fn walk_region_exprs(s: &Stmt, on_expr: &mut impl FnMut(&Expr)) {
    // Top-level declarations (class/function) hold their own bodies; descend.
    match &s.kind {
        StmtKind::Class(c) => {
            for m in &c.members {
                match m {
                    Member::Method(md) => {
                        if let Some(body) = &md.body {
                            body.iter().for_each(|st| walk_region_exprs(st, on_expr));
                        }
                    }
                    Member::Property(pd) => {
                        for elem in &pd.props {
                            if let Some(d) = &elem.default {
                                walk_expr_local(d, on_expr);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        StmtKind::Function(fd) => fd.body.iter().for_each(|st| walk_region_exprs(st, on_expr)),
        StmtKind::Namespace { body: Some(b), .. } => {
            b.iter().for_each(|st| walk_region_exprs(st, on_expr))
        }
        _ => stmt_exprs(s, on_expr),
    }
}

// --- NullsafePropertyFetchRule (level 4) -----------------------------------

/// phpstan `NullsafePropertyFetchRule` (`nullsafe.neverNull`): using `?->` on a
/// receiver whose type is never null is redundant — use `->`. FP-safe: only fires
/// when the receiver's inferred type is a concrete, non-nullable object class
/// (`Type::Named`). Unknown/mixed/nullable/union receivers are left alone.
fn run_nullsafe_property_fetch(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e: &Expr| {
        let ExprKind::Prop { base, nullsafe: true, .. } = &e.kind else { return };
        let recv = fa.type_of(base);
        // Only when we are SURE it's never null: a concrete named object type.
        if matches!(recv, Type::Named { .. }) {
            let desc = type_desc(&recv);
            out.push(
                Diagnostic::error(
                    e.span,
                    format!(
                        "Using nullsafe property access on non-nullable type {desc}. Use -> instead."
                    ),
                )
                .with_code("nullsafe.neverNull"),
            );
        }
    });
    out
}

fn type_desc(ty: &Type) -> String {
    match ty {
        Type::Named { fqn, .. } => fqn.trim_start_matches('\\').to_string(),
        other => format!("{other}"),
    }
}

// --- ReadingWriteOnlyPropertiesRule (level 0) ------------------------------

/// phpstan `ReadingWriteOnlyPropertiesRule` (`property.writeOnly`): reading a
/// magic property declared `@property-write` only. FP-safe: only fires on a
/// concrete known class with a magic property whose access is `WriteOnly`, and
/// only in a read position (not the LHS of an assignment).
fn run_reading_write_only(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    // Collect spans of property fetches that are assignment *targets* (writes),
    // so we can exclude them from the read check.
    let mut write_targets: Vec<(u32, u32)> = Vec::new();
    walk::for_each_expr(fa.program, &mut |e: &Expr| {
        if let ExprKind::Assign { target, .. } | ExprKind::AssignRef { target, .. } = &e.kind {
            if matches!(&target.kind, ExprKind::Prop { .. }) {
                let r = target.span.range();
                write_targets.push((r.start as u32, r.end as u32));
            }
        }
    });

    walk::for_each_expr(fa.program, &mut |e: &Expr| {
        let ExprKind::Prop { base, name, .. } = &e.kind else { return };
        let MemberName::Ident(p) = name else { return };
        let r = e.span.range();
        if write_targets.contains(&(r.start as u32, r.end as u32)) {
            return; // it's a write, not a read.
        }
        let Some(class) = receiver_class(fa, base) else { return };
        if !known_class_tree(&class, fa) {
            return;
        }
        let prop = fa.interner.resolve(*p);
        if let Some(found) = fa.reflection.find_property(&class, prop) {
            if found.member.magic && found.member.access == PropertyAccess::WriteOnly {
                out.push(
                    Diagnostic::error(
                        e.span,
                        format!(
                            "Property {}::${prop} is not readable.",
                            found.declaring_class.trim_start_matches('\\')
                        ),
                    )
                    .with_code("property.writeOnly"),
                );
            }
        }
    });
    out
}

// --- WritingToReadOnlyPropertiesRule (level 0) -----------------------------

/// phpstan `WritingToReadOnlyPropertiesRule` (`assign.propertyReadOnly`): writing
/// to a magic property declared `@property-read` only. FP-safe: concrete known
/// class, magic property whose access is `ReadOnly`. (Distinct from native
/// `readonly` properties — those are `ReadOnlyPropertyAssignRule`.)
fn run_writing_to_read_only(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e: &Expr| {
        let (ExprKind::Assign { target, .. } | ExprKind::AssignOp { target, .. }) = &e.kind else {
            return;
        };
        let ExprKind::Prop { base, name, .. } = &target.kind else { return };
        let MemberName::Ident(p) = name else { return };
        let Some(class) = receiver_class(fa, base) else { return };
        if !known_class_tree(&class, fa) {
            return;
        }
        let prop = fa.interner.resolve(*p);
        if let Some(found) = fa.reflection.find_property(&class, prop) {
            if found.member.magic && found.member.access == PropertyAccess::ReadOnly {
                out.push(
                    Diagnostic::error(
                        target.span,
                        format!(
                            "Property {}::${prop} is not writable.",
                            found.declaring_class.trim_start_matches('\\')
                        ),
                    )
                    .with_code("assign.propertyReadOnly"),
                );
            }
        }
    });
    out
}

/// Resolve a property-fetch receiver expression to a single concrete class FQN,
/// covering both `$this` (via the inferred type, which the type map seeds) and an
/// arbitrary inferred object type.
fn receiver_class(fa: &FileAnalysis, base: &Expr) -> Option<String> {
    sole_class(&fa.type_of(base))
}

// --- InvalidCallablePropertyTypeRule (level 0) -----------------------------

/// phpstan `InvalidCallablePropertyTypeRule` (`property.callableType`): PHP does
/// not allow `callable` as a (native) property type. Fires when the property's
/// native type mentions `callable` anywhere — directly, inside a union, or inside
/// an intersection — matching phpstan's `TypeTraverser` over the native type.
/// Purely syntactic over the AST (no reflection / inference). Promoted properties
/// are ctor params, not `Member::Property`, so they're naturally excluded.
fn run_invalid_callable_property_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_property(fa.program, &mut |class, pd| {
        let Some(ty) = &pd.ty else { return };
        if !type_mentions_callable(ty) {
            return;
        }
        let cname = class_name(class, fa);
        // One diagnostic per declared name (phpstan emits one per ClassPropertyNode,
        // and a multi-property declaration `public callable $a, $b;` is several).
        for elem in &pd.props {
            let prop = fa.interner.resolve(elem.name);
            out.push(
                Diagnostic::error(
                    ty.span,
                    format!(
                        "Property {cname}::${prop} cannot have callable in its type declaration."
                    ),
                )
                .with_code("property.callableType"),
            );
        }
    });
    out
}

/// Does this native type (possibly under nullable / union / intersection) mention
/// the reserved `callable` pseudo-type? (`Callable` is the only spelling PHP
/// rejects as a property type; `Closure` is a real class and is allowed.)
fn type_mentions_callable(ty: &php_ast::Type) -> bool {
    match &ty.kind {
        php_ast::TypeKind::Simple(n) => {
            n.text.trim_start_matches('\\').eq_ignore_ascii_case("callable")
        }
        php_ast::TypeKind::Nullable(inner) => type_mentions_callable(inner),
        php_ast::TypeKind::Union(parts) | php_ast::TypeKind::Intersection(parts) => {
            parts.iter().any(type_mentions_callable)
        }
    }
}

// --- MissingPropertyTypehintRule (level 6) ---------------------------------

/// phpstan `MissingPropertyTypehintRule` (`missingType.property`): a property with
/// neither a native type nor a `@var` PHPDoc type. Mirrors
/// `MissingFunctionParameterTypehintRule`: native type absent AND the docblock has
/// no `@var` tag. Conservative `@var` scan (any occurrence suppresses) keeps us
/// false-positive-free. Promoted properties (ctor params) are excluded by virtue
/// of not being `Member::Property`.
fn run_missing_property_typehint(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_property(fa.program, &mut |class, pd| {
        if pd.ty.is_some() {
            return; // has a native type.
        }
        if doc_has_var(pd.doc.as_deref()) {
            return; // an `@var` PHPDoc type counts as "specified".
        }
        let cname = class_name(class, fa);
        for elem in &pd.props {
            let prop = fa.interner.resolve(elem.name);
            out.push(
                Diagnostic::error(
                    span_of(elem),
                    format!("Property {cname}::${prop} has no type specified."),
                )
                .with_code("missingType.property"),
            );
        }
    });
    out
}

/// Conservative scan of a raw docblock for an `@var` tag. Any occurrence — even
/// partial — counts as "type specified", to avoid false positives.
fn doc_has_var(doc: Option<&str>) -> bool {
    doc.is_some_and(|d| d.contains("@var"))
}

// --- registry --------------------------------------------------------------

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "property.readOnly", level: 0, run: run_readonly_property },
    RuleEntry { name: "property.inClass", level: 0, run: run_property_in_class },
    RuleEntry { name: "property.inInterface", level: 0, run: run_properties_in_interface },
    RuleEntry { name: "property.hookAttributes", level: 0, run: run_property_hook_attributes },
    RuleEntry { name: "property.overriding", level: 0, run: run_overriding_property },
    RuleEntry { name: "property.accessUndefined", level: 0, run: run_access_properties },
    RuleEntry { name: "property.readOnlyAssign", level: 3, run: run_readonly_property_assign },
    RuleEntry { name: "property.access", level: 0, run: run_access_properties_general },
    RuleEntry { name: "property.accessInAssign", level: 0, run: run_access_properties_in_assign },
    RuleEntry { name: "staticProperty.access", level: 0, run: run_access_static_properties },
    RuleEntry {
        name: "staticProperty.accessInAssign",
        level: 0,
        run: run_access_static_properties_in_assign,
    },
    RuleEntry { name: "property.nullsafeNeverNull", level: 4, run: run_nullsafe_property_fetch },
    RuleEntry { name: "property.readingWriteOnly", level: 0, run: run_reading_write_only },
    RuleEntry { name: "property.writingToReadOnly", level: 0, run: run_writing_to_read_only },
    RuleEntry { name: "property.callableType", level: 0, run: run_invalid_callable_property_type },
    RuleEntry { name: "property.missingType", level: 6, run: run_missing_property_typehint },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- ReadOnlyPropertyRule -------------------------------------------

    #[test]
    fn readonly_without_type_is_flagged() {
        let src = "<?php class C { public readonly $x; }";
        assert_eq!(codes(src, run_readonly_property), ["property.readOnlyNoNativeType"]);
    }

    #[test]
    fn readonly_with_type_is_clean() {
        let src = "<?php class C { public readonly int $x; }";
        assert!(codes(src, run_readonly_property).is_empty());
    }

    #[test]
    fn readonly_static_is_flagged() {
        let src = "<?php class C { public static readonly int $x; }";
        assert_eq!(codes(src, run_readonly_property), ["property.readOnlyStatic"]);
    }

    #[test]
    fn readonly_with_default_is_flagged() {
        let src = "<?php class C { public readonly int $x = 1; }";
        assert_eq!(codes(src, run_readonly_property), ["property.readOnlyDefaultValue"]);
    }

    #[test]
    fn non_readonly_is_clean() {
        let src = "<?php class C { public int $x = 1; public static int $y = 2; }";
        assert!(codes(src, run_readonly_property).is_empty());
    }

    // --- PropertyInClassRule --------------------------------------------

    #[test]
    fn abstract_non_hooked_property_is_flagged() {
        let src = "<?php abstract class C { abstract public int $x; }";
        assert_eq!(codes(src, run_property_in_class), ["property.abstractNonHooked"]);
    }

    #[test]
    fn abstract_and_final_property_is_flagged() {
        let src = "<?php abstract class C { abstract final public int $x { get; } }";
        assert!(codes(src, run_property_in_class).contains(&"property.abstractFinal"));
    }

    #[test]
    fn abstract_private_property_is_flagged() {
        let src = "<?php abstract class C { abstract private int $x { get; } }";
        assert!(codes(src, run_property_in_class).contains(&"property.abstractPrivate"));
    }

    #[test]
    fn final_private_property_is_flagged() {
        let src = "<?php class C { final private int $x; }";
        assert_eq!(codes(src, run_property_in_class), ["property.finalPrivate"]);
    }

    #[test]
    fn readonly_hooked_property_is_flagged() {
        let src = "<?php class C { public readonly int $x { get => 1; } }";
        assert!(codes(src, run_property_in_class).contains(&"property.hookReadOnly"));
    }

    #[test]
    fn static_hooked_property_is_flagged() {
        let src = "<?php class C { public static int $x { get => 1; } }";
        assert!(codes(src, run_property_in_class).contains(&"property.hookedStatic"));
    }

    #[test]
    fn plain_property_in_class_is_clean() {
        let src = "<?php class C { public int $x = 1; private string $y; }";
        assert!(codes(src, run_property_in_class).is_empty());
    }

    // --- PropertiesInInterfaceRule --------------------------------------

    #[test]
    fn non_hooked_property_in_interface_is_flagged() {
        let src = "<?php interface I { public int $x; }";
        assert_eq!(codes(src, run_properties_in_interface), ["property.nonHookedInInterface"]);
    }

    #[test]
    fn hooked_public_property_in_interface_is_clean() {
        let src = "<?php interface I { public int $x { get; } }";
        assert!(codes(src, run_properties_in_interface).is_empty());
    }

    #[test]
    fn non_public_hooked_property_in_interface_is_flagged() {
        let src = "<?php interface I { protected int $x { get; } }";
        assert_eq!(codes(src, run_properties_in_interface), ["property.nonPublicInInterface"]);
    }

    #[test]
    fn hook_with_body_in_interface_is_flagged() {
        let src = "<?php interface I { public int $x { get => 1; } }";
        assert_eq!(codes(src, run_properties_in_interface), ["property.hookBodyInInterface"]);
    }

    #[test]
    fn class_property_not_flagged_by_interface_rule() {
        let src = "<?php class C { public int $x; }";
        assert!(codes(src, run_properties_in_interface).is_empty());
    }

    // --- PropertyHookAttributesRule -------------------------------------

    #[test]
    fn nodiscard_on_hook_is_flagged() {
        let src = "<?php class C { public int $x { #[NoDiscard] get => 1; } }";
        assert_eq!(codes(src, run_property_hook_attributes), ["attribute.target"]);
    }

    #[test]
    fn other_attr_on_hook_is_clean() {
        let src = "<?php class C { public int $x { #[Other] get => 1; } }";
        assert!(codes(src, run_property_hook_attributes).is_empty());
    }

    // --- OverridingPropertyRule -----------------------------------------

    #[test]
    fn override_static_with_nonstatic_is_flagged() {
        let src = "<?php class B { public static int $x = 0; } class C extends B { public int $x = 0; }";
        let got = codes(src, run_overriding_property);
        assert!(got.contains(&"property.nonStatic"), "{got:?}");
    }

    #[test]
    fn override_readonly_with_readwrite_is_flagged() {
        let src = "<?php class B { public readonly int $x; } class C extends B { public int $x; }";
        let got = codes(src, run_overriding_property);
        assert!(got.contains(&"property.readWrite"), "{got:?}");
    }

    #[test]
    fn override_narrows_visibility_is_flagged() {
        let src = "<?php class B { public int $x = 0; } class C extends B { protected int $x = 0; }";
        let got = codes(src, run_overriding_property);
        assert!(got.contains(&"property.visibility"), "{got:?}");
    }

    #[test]
    fn override_missing_attribute_is_flagged() {
        let src = "<?php class B { public int $x = 0; } class C extends B { public int $x = 0; }";
        let got = codes(src, run_overriding_property);
        assert!(got.contains(&"property.missingOverride"), "{got:?}");
    }

    #[test]
    fn override_attribute_without_parent_is_flagged() {
        let src = "<?php class C { #[\\Override] public int $x = 0; }";
        let got = codes(src, run_overriding_property);
        assert!(got.contains(&"property.override"), "{got:?}");
    }

    #[test]
    fn non_overriding_property_is_clean() {
        let src = "<?php class C { public int $x = 0; }";
        assert!(codes(src, run_overriding_property).is_empty());
    }

    // --- AccessPropertiesRule -------------------------------------------

    #[test]
    fn access_undefined_property_on_this_is_flagged() {
        let src = "<?php class C { public int $a; function f() { return $this->b; } }";
        assert_eq!(codes(src, run_access_properties), ["property.notFound"]);
    }

    #[test]
    fn access_defined_property_on_this_is_clean() {
        let src = "<?php class C { public int $a; function f() { return $this->a; } }";
        assert!(codes(src, run_access_properties).is_empty());
    }

    #[test]
    fn access_property_with_unknown_parent_is_not_flagged() {
        // The parent is not in the index → conservative: no false positive.
        let src = "<?php class C extends Unknown { function f() { return $this->b; } }";
        assert!(codes(src, run_access_properties).is_empty());
    }

    #[test]
    fn access_property_with_magic_get_is_not_flagged() {
        let src =
            "<?php class C { function __get($n) { return 1; } function f() { return $this->b; } }";
        assert!(codes(src, run_access_properties).is_empty());
    }

    #[test]
    fn access_inherited_property_is_clean() {
        let src = "<?php class B { public int $a; } class C extends B { function f() { return $this->a; } }";
        assert!(codes(src, run_access_properties).is_empty());
    }

    // --- ReadOnlyPropertyAssignRule -------------------------------------

    #[test]
    fn readonly_assign_outside_ctor_is_flagged() {
        let src = "<?php class C { public readonly int $x; function f() { $this->x = 1; } }";
        assert_eq!(
            codes(src, run_readonly_property_assign),
            ["property.readOnlyAssignNotInConstructor"]
        );
    }

    #[test]
    fn readonly_assign_in_ctor_is_clean() {
        let src =
            "<?php class C { public readonly int $x; function __construct() { $this->x = 1; } }";
        assert!(codes(src, run_readonly_property_assign).is_empty());
    }

    #[test]
    fn non_readonly_assign_outside_ctor_is_clean() {
        let src = "<?php class C { public int $x; function f() { $this->x = 1; } }";
        assert!(codes(src, run_readonly_property_assign).is_empty());
    }

    // --- AccessPropertiesRule (general receiver) ------------------------

    #[test]
    fn access_undefined_property_on_new_is_flagged() {
        let src = "<?php class C { public int $a; } function f() { return (new C())->b; }";
        assert_eq!(codes(src, run_access_properties_general), ["property.notFound"]);
    }

    #[test]
    fn access_defined_property_on_new_is_clean() {
        let src = "<?php class C { public int $a; } function f() { return (new C())->a; }";
        assert!(codes(src, run_access_properties_general).is_empty());
    }

    #[test]
    fn access_property_on_unknown_class_is_clean() {
        // Receiver type unknown / not in index → conservative, no FP.
        let src = "<?php function f($x) { return $x->b; }";
        assert!(codes(src, run_access_properties_general).is_empty());
    }

    #[test]
    fn access_property_on_new_with_magic_get_is_clean() {
        let src = "<?php class C { function __get($n) { return 1; } } function f() { return (new C())->b; }";
        assert!(codes(src, run_access_properties_general).is_empty());
    }

    #[test]
    fn access_property_on_this_not_double_reported() {
        // $this is handled by run_access_properties, not the general rule.
        let src = "<?php class C { public int $a; function f() { return $this->b; } }";
        assert!(codes(src, run_access_properties_general).is_empty());
    }

    #[test]
    fn access_inherited_property_on_new_is_clean() {
        let src = "<?php class B { public int $a; } class C extends B {} function f() { return (new C())->a; }";
        assert!(codes(src, run_access_properties_general).is_empty());
    }

    // --- AccessPropertiesInAssignRule ----------------------------------

    #[test]
    fn assign_undefined_property_is_flagged() {
        let src = "<?php class C { public int $a; } function f() { (new C())->b = 1; }";
        assert_eq!(codes(src, run_access_properties_in_assign), ["property.notFound"]);
    }

    #[test]
    fn assign_defined_property_is_clean() {
        let src = "<?php class C { public int $a; } function f() { (new C())->a = 1; }";
        assert!(codes(src, run_access_properties_in_assign).is_empty());
    }

    // --- AccessStaticPropertiesRule ------------------------------------

    #[test]
    fn access_undefined_static_property_is_flagged() {
        let src = "<?php class C { public static int $a; } function f() { return C::$b; }";
        assert_eq!(codes(src, run_access_static_properties), ["staticProperty.notFound"]);
    }

    #[test]
    fn access_defined_static_property_is_clean() {
        let src = "<?php class C { public static int $a; } function f() { return C::$a; }";
        assert!(codes(src, run_access_static_properties).is_empty());
    }

    #[test]
    fn access_static_property_on_unknown_class_is_clean() {
        let src = "<?php function f() { return Unknown::$b; }";
        assert!(codes(src, run_access_static_properties).is_empty());
    }

    #[test]
    fn access_static_property_via_self_is_not_flagged() {
        // self/static/parent are skipped (need enclosing-class scope).
        let src = "<?php class C { public static int $a; function f() { return self::$b; } }";
        assert!(codes(src, run_access_static_properties).is_empty());
    }

    // --- NullsafePropertyFetchRule -------------------------------------

    #[test]
    fn nullsafe_on_nonnull_object_is_flagged() {
        let src = "<?php class C { public int $a; } function f() { return (new C())?->a; }";
        assert_eq!(codes(src, run_nullsafe_property_fetch), ["nullsafe.neverNull"]);
    }

    #[test]
    fn nullsafe_on_unknown_is_clean() {
        let src = "<?php function f($x) { return $x?->a; }";
        assert!(codes(src, run_nullsafe_property_fetch).is_empty());
    }

    #[test]
    fn nullsafe_on_nullable_is_clean() {
        let src = "<?php class C { public ?C $next; function f() { return $this->next?->next; } }";
        assert!(codes(src, run_nullsafe_property_fetch).is_empty());
    }

    #[test]
    fn plain_arrow_is_clean() {
        let src = "<?php class C { public int $a; } function f() { return (new C())->a; }";
        assert!(codes(src, run_nullsafe_property_fetch).is_empty());
    }

    // --- ReadingWriteOnlyPropertiesRule --------------------------------

    #[test]
    fn reading_write_only_magic_property_is_flagged() {
        let src = "<?php /** @property-write int $w */ class C {} function f() { return (new C())->w; }";
        assert_eq!(codes(src, run_reading_write_only), ["property.writeOnly"]);
    }

    #[test]
    fn writing_write_only_magic_property_is_clean() {
        let src = "<?php /** @property-write int $w */ class C {} function f() { (new C())->w = 1; }";
        assert!(codes(src, run_reading_write_only).is_empty());
    }

    #[test]
    fn reading_readwrite_magic_property_is_clean() {
        let src = "<?php /** @property int $p */ class C {} function f() { return (new C())->p; }";
        assert!(codes(src, run_reading_write_only).is_empty());
    }

    // --- WritingToReadOnlyPropertiesRule -------------------------------

    #[test]
    fn writing_read_only_magic_property_is_flagged() {
        let src = "<?php /** @property-read int $r */ class C {} function f() { (new C())->r = 1; }";
        assert_eq!(codes(src, run_writing_to_read_only), ["assign.propertyReadOnly"]);
    }

    #[test]
    fn reading_read_only_magic_property_is_clean() {
        let src = "<?php /** @property-read int $r */ class C {} function f() { return (new C())->r; }";
        assert!(codes(src, run_writing_to_read_only).is_empty());
    }

    #[test]
    fn writing_readwrite_magic_property_is_clean() {
        let src = "<?php /** @property int $p */ class C {} function f() { (new C())->p = 1; }";
        assert!(codes(src, run_writing_to_read_only).is_empty());
    }

    // --- AccessStaticPropertiesInAssignRule ----------------------------

    #[test]
    fn assign_undefined_static_property_is_flagged() {
        let src = "<?php class C { public static int $a; } function f() { C::$b = 1; }";
        assert_eq!(codes(src, run_access_static_properties_in_assign), ["staticProperty.notFound"]);
    }

    #[test]
    fn assign_defined_static_property_is_clean() {
        let src = "<?php class C { public static int $a; } function f() { C::$a = 1; }";
        assert!(codes(src, run_access_static_properties_in_assign).is_empty());
    }

    #[test]
    fn assign_static_property_on_unknown_class_is_clean() {
        let src = "<?php function f() { Unknown::$b = 1; }";
        assert!(codes(src, run_access_static_properties_in_assign).is_empty());
    }

    #[test]
    fn assign_static_property_via_self_is_not_flagged() {
        let src = "<?php class C { public static int $a; function f() { self::$b = 1; } }";
        assert!(codes(src, run_access_static_properties_in_assign).is_empty());
    }

    #[test]
    fn compound_assign_static_property_not_flagged_by_assign_rule() {
        // `+=` is a read+write; the read rule handles it, not the assign rule.
        let src = "<?php class C { public static int $b; } function f() { C::$b += 1; }";
        assert!(codes(src, run_access_static_properties_in_assign).is_empty());
    }

    #[test]
    fn assign_target_not_double_reported_by_read_rule() {
        // A plain `C::$b = 1` is reported only by the assign rule, not the read rule.
        let src = "<?php class C { public static int $a; } function f() { C::$b = 1; }";
        assert!(codes(src, run_access_static_properties).is_empty());
    }

    #[test]
    fn read_static_property_still_flagged_after_split() {
        let src = "<?php class C { public static int $a; } function f() { return C::$b; }";
        assert_eq!(codes(src, run_access_static_properties), ["staticProperty.notFound"]);
    }

    // --- InvalidCallablePropertyTypeRule -------------------------------

    #[test]
    fn callable_property_type_is_flagged() {
        let src = "<?php class C { public callable $cb; }";
        assert_eq!(codes(src, run_invalid_callable_property_type), ["property.callableType"]);
    }

    #[test]
    fn nullable_callable_property_type_is_flagged() {
        let src = "<?php class C { public ?callable $cb; }";
        assert_eq!(codes(src, run_invalid_callable_property_type), ["property.callableType"]);
    }

    #[test]
    fn callable_in_union_property_type_is_flagged() {
        let src = "<?php class C { public int|callable $cb; }";
        assert_eq!(codes(src, run_invalid_callable_property_type), ["property.callableType"]);
    }

    #[test]
    fn closure_property_type_is_clean() {
        // `Closure` is a real class — allowed as a property type.
        let src = "<?php class C { public \\Closure $cb; }";
        assert!(codes(src, run_invalid_callable_property_type).is_empty());
    }

    #[test]
    fn plain_typed_property_is_clean_of_callable_rule() {
        let src = "<?php class C { public int $x; public ?string $y; }";
        assert!(codes(src, run_invalid_callable_property_type).is_empty());
    }

    #[test]
    fn callable_multi_property_flags_each() {
        let src = "<?php class C { public callable $a, $b; }";
        assert_eq!(
            codes(src, run_invalid_callable_property_type),
            ["property.callableType", "property.callableType"]
        );
    }

    // --- MissingPropertyTypehintRule -----------------------------------

    #[test]
    fn untyped_property_is_flagged() {
        let src = "<?php class C { public $x; }";
        assert_eq!(codes(src, run_missing_property_typehint), ["missingType.property"]);
    }

    #[test]
    fn native_typed_property_is_clean() {
        let src = "<?php class C { public int $x; }";
        assert!(codes(src, run_missing_property_typehint).is_empty());
    }

    #[test]
    fn var_documented_property_is_clean() {
        let src = "<?php class C { /** @var int */ public $x; }";
        assert!(codes(src, run_missing_property_typehint).is_empty());
    }

    #[test]
    fn untyped_undocumented_property_in_interface_unaffected() {
        // for_each_property visits interface props too; an untyped (non-hooked)
        // interface property still has no type → flagged (phpstan reports it on the
        // ClassPropertyNode regardless of container; the interface-shape rule is
        // separate).
        let src = "<?php class C { /** something */ public $x; }";
        assert_eq!(codes(src, run_missing_property_typehint), ["missingType.property"]);
    }

    #[test]
    fn untyped_multi_property_flags_each() {
        let src = "<?php class C { public $a, $b; }";
        assert_eq!(
            codes(src, run_missing_property_typehint),
            ["missingType.property", "missingType.property"]
        );
    }
}
