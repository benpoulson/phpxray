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
//! - `MissingReadOnlyPropertyAssignRule` / `MissingReadOnlyByPhpDocPropertyAssignRule`
//!   full parity for branchy constructors / helper calls / configured additional
//!   constructors — current implementation is the straight-line, zero-FP subset.
//! - `PropertyAttributesRule` attribute-target body (`property.overrideAttribute`)
//!   — needs the (possibly cross-file) `#[Attribute(flags)]` of the attribute
//!   class to know its allowed targets. (We do the hook `nodiscard` variant,
//!   which is purely syntactic.)
//! - `OverridingPropertyRule` type parts (`property.nativeType`,
//!   `property.missingNativeType`, `property.parentPropertyFinalByPhpDoc`) —
//!   need native-type equality / PHPDoc `@final`. (We do the static / readonly /
//!   visibility / `#[\Override]` parts.)
//! - `SetPropertyHookParameterRule` (`propertySetHook.nativeParameterType`) —
//!   needs hook-param/property type contravariance plus the missing iterable /
//!   generic / callable signature checks.
//! - `NullsafePropertyFetchRule` (`nullsafe.neverNull`) — needs the receiver
//!   type (is it ever null?).
//! - `MissingPropertyTypehintRule` (`missingType.property`) — needs the merged
//!   readable type / explicit-mixed distinction from the type system.
//! - `AccessStaticPropertiesRule` / `ReadingWriteOnlyPropertiesRule` /
//!   property-hook get/set body rules — need expression-type inference of the
//!   access receiver / value, or virtual-property hook semantics beyond the AST.

use crate::{
    compat, decls,
    facts::AssignmentKind,
    members::{MemberAccessResolver, ResolveStatus},
    symbols, walk, FileAnalysis, RuleEntry,
};
use php_ast::{
    AttributeGroup, ClassDecl, ClassKind, Expr, ExprKind, HookBody, Member, MemberName, Name,
    Param, Program, PropElem, PropertyDecl, PropertyHook, Stmt, StmtKind, Visibility,
};
use php_diagnostics::Diagnostic;
use php_infer::TypeCtx;
use php_phpdoc::PropertyAccess;
use php_resolve::{for_each_region, Scope};
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
    // Point at the `$property` name token.
    p.name_span
}

/// Walk every property declaration in the file together with the class it
/// belongs to.
fn for_each_property(fa: &FileAnalysis, f: &mut impl FnMut(&ClassDecl, &PropertyDecl)) {
    decls::for_each_property(fa, |_, class, property| f(class, property));
}

fn for_each_property_elem(
    fa: &FileAnalysis,
    f: &mut impl FnMut(&str, &ClassDecl, &PropertyDecl, &PropElem),
) {
    decls::for_each_property_elem(fa, f);
}

// --- ReadOnlyPropertyRule (level 0) ----------------------------------------

/// phpstan `ReadOnlyPropertyRule`: a `readonly` property must have a native
/// type, must not have a default value, and must not be static.
fn run_readonly_property(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_property(fa, &mut |_class, pd| {
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

// --- ReadOnlyByPhpDocPropertyRule (level 0) --------------------------------

/// Whether a property docblock carries a `@readonly` tag (or its
/// `@phpstan-readonly`/`@psalm-readonly` variants).
fn has_readonly_doc(doc_raw: &str, base: &str) -> bool {
    php_phpdoc::parse_block(doc_raw).tags.iter().any(|t| {
        let n = t.name.as_str();
        match base {
            "readonly" => matches!(
                n,
                "readonly"
                    | "phan-read-only"
                    | "psalm-readonly"
                    | "phpstan-readonly"
                    | "phpstan-readonly-allow-private-mutation"
                    | "psalm-readonly-allow-private-mutation"
            ),
            "allow-private-mutation" => matches!(
                n,
                "phpstan-readonly-allow-private-mutation"
                    | "phpstan-allow-private-mutation"
                    | "psalm-readonly-allow-private-mutation"
                    | "psalm-allow-private-mutation"
            ),
            _ => {
                let n = n
                    .strip_prefix("phpstan-")
                    .or_else(|| n.strip_prefix("psalm-"))
                    .unwrap_or(n);
                n == base
            }
        }
    })
}

/// phpstan `ReadOnlyByPhpDocPropertyRule` (`property.readOnlyByPhpDocDefaultValue`):
/// a `@readonly` (PHPDoc, not native `readonly`) property may not have a default
/// value. We require the property-level `@readonly` tag, no native `readonly`
/// modifier (that case is `property.readOnlyDefaultValue`), and no
/// `@psalm-allow-private-mutation` opt-out (which lets the property be mutated).
fn run_readonly_phpdoc_property(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_property(fa, &mut |_class, pd| {
        if pd.modifiers.is_readonly {
            return; // native readonly — handled by run_readonly_property
        }
        let Some(doc) = &pd.doc else { return };
        if !has_readonly_doc(doc, "readonly") || has_readonly_doc(doc, "allow-private-mutation") {
            return;
        }
        for elem in &pd.props {
            if let Some(d) = &elem.default {
                out.push(
                    Diagnostic::error(d.span, "@readonly property cannot have a default value.")
                        .with_code("property.readOnlyByPhpDocDefaultValue"),
                );
            }
        }
    });
    out
}

#[derive(Clone, Debug)]
struct PropertyDeclInfo {
    declaring_class: String,
    visibility: Visibility,
    is_static: bool,
    is_native_readonly: bool,
    set_visibility: Option<Visibility>,
    doc_readonly: bool,
    doc_allow_private_mutation: bool,
    span: Span,
}

fn property_decl_info(
    fa: &FileAnalysis,
    receiver_class: &str,
    prop: &str,
) -> Option<PropertyDeclInfo> {
    let found = fa.reflection.find_property(receiver_class, prop)?;
    let mut info = PropertyDeclInfo {
        declaring_class: found.declaring_class.to_string(),
        visibility: found.member.visibility,
        is_static: found.member.is_static,
        is_native_readonly: found.member.is_readonly,
        set_visibility: None,
        doc_readonly: false,
        doc_allow_private_mutation: false,
        span: Span::DUMMY,
    };

    for_each_property_elem(fa, &mut |class_fqn, _class, pd, elem| {
        if !symbols::same_fqn(class_fqn, found.declaring_class) {
            return;
        }
        if fa.interner.resolve(elem.name) != prop {
            return;
        }
        let doc = pd.doc.as_deref();
        info.set_visibility = pd.modifiers.set_visibility;
        info.doc_readonly = doc.is_some_and(|d| has_readonly_doc(d, "readonly"));
        info.doc_allow_private_mutation =
            doc.is_some_and(|d| has_readonly_doc(d, "allow-private-mutation"));
        info.span = span_of(elem);
    });

    Some(info)
}

fn write_visibility(info: &PropertyDeclInfo) -> Visibility {
    info.set_visibility.unwrap_or(info.visibility)
}

fn write_visibility_label(info: &PropertyDeclInfo) -> &'static str {
    match info.set_visibility {
        Some(Visibility::Private) => "private(set)",
        Some(Visibility::Protected) => "protected(set)",
        _ => match info.visibility {
            Visibility::Private => "private",
            Visibility::Protected => "protected",
            Visibility::Public => "public",
        },
    }
}

fn can_write_property(
    fa: &FileAnalysis,
    current_class: Option<&str>,
    info: &PropertyDeclInfo,
) -> bool {
    match write_visibility(info) {
        Visibility::Public => true,
        Visibility::Private => {
            current_class.is_some_and(|c| symbols::same_fqn(c, &info.declaring_class))
        }
        Visibility::Protected => current_class.is_some_and(|c| {
            symbols::same_fqn(c, &info.declaring_class)
                || fa.reflection.is_subclass_of(c, &info.declaring_class)
        }),
    }
}

fn receiver_class_for_property_fetch(
    fa: &FileAnalysis,
    current_class: Option<&str>,
    base: &Expr,
) -> Option<String> {
    if matches!(&base.kind, ExprKind::Variable(v) if fa.interner.resolve(*v) == "this") {
        return current_class.map(|c| c.to_string());
    }
    sole_class(&fa.type_of(base))
}

fn property_fetch_parts<'a>(fa: &'a FileAnalysis, fetch: &'a Expr) -> Option<(&'a Expr, &'a str)> {
    let ExprKind::Prop {
        base,
        name: MemberName::Ident(p),
        ..
    } = &fetch.kind
    else {
        return None;
    };
    Some((base, fa.interner.resolve(*p)))
}

fn property_fetch_from_write_target(target: &Expr) -> Option<&Expr> {
    match &target.kind {
        ExprKind::Prop { .. } => Some(target),
        ExprKind::Index { base, .. } | ExprKind::Paren(base) => {
            property_fetch_from_write_target(base)
        }
        _ => None,
    }
}

// --- PropertyInClassRule (level 0) -----------------------------------------

/// phpstan `PropertyInClassRule` (the AST-decidable subset): modifier conflicts
/// on a property *in a class* (not interface). Covers abstract/final/private,
/// abstract-vs-hooks, readonly/static-vs-hooks, and virtual default-value.
fn run_property_in_class(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_property(fa, &mut |class, pd| {
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
    pd.props.iter().any(|p| {
        p.hooks
            .as_ref()
            .is_some_and(|hs| hs.iter().any(|h| h.modifiers.is_final))
    })
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
    for_each_property(fa, &mut |class, pd| {
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
                Diagnostic::error(
                    span,
                    "Interfaces cannot include readonly hooked properties.",
                )
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
                Diagnostic::error(
                    span,
                    "Interfaces cannot include property hooks with bodies.",
                )
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
    for_each_property(fa, &mut |_class, pd| {
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

// --- GetNonVirtualPropertyHookReadRule (level 3, conservative) ------------

/// phpstan `GetNonVirtualPropertyHookReadRule` (`propertyGetHook.noRead`): a
/// non-virtual property's `get` hook must read the backing value. We implement
/// the AST-decidable subset: the property is definitely backed when a `set`
/// hook is the short `set => expr` form (implicit backing assignment) or when a
/// hook body directly assigns `$this->sameProperty`.
fn run_get_non_virtual_property_hook_read(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_property_elem(fa, &mut |class_fqn, _class, _pd, elem| {
        let prop = fa.interner.resolve(elem.name);
        let Some(get_hook) = hook_named(elem, fa, "get") else {
            return;
        };
        if matches!(get_hook.body, HookBody::Abstract) {
            return;
        }
        if hook_body_reads_this_property(&get_hook.body, prop, fa) {
            return;
        }
        if !hooked_property_is_definitely_backed(elem, prop, fa) {
            return;
        }
        out.push(
            Diagnostic::error(
                hook_span(get_hook),
                format!(
                    "Get hook for non-virtual property {}::${prop} does not read its value.",
                    class_fqn.trim_start_matches('\\')
                ),
            )
            .with_code("propertyGetHook.noRead"),
        );
    });
    out
}

// --- SetNonVirtualPropertyHookAssignRule (level 3, conservative) ----------

/// phpstan `SetNonVirtualPropertyHookAssignRule` (`propertySetHook.noAssign`):
/// a non-virtual property's block `set` hook must assign the backing value. We
/// only report the unambiguous "does not assign" case: a block set hook for a
/// definitely-backed property that contains no direct `$this->sameProperty = ...`
/// assignment and no explicit terminator. The "does not always assign" branch
/// needs path-sensitive execution-end merging and is deferred.
fn run_set_non_virtual_property_hook_assign(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_property_elem(fa, &mut |class_fqn, _class, _pd, elem| {
        let prop = fa.interner.resolve(elem.name);
        let Some(set_hook) = hook_named(elem, fa, "set") else {
            return;
        };
        if !matches!(set_hook.body, HookBody::Block(_)) {
            return;
        }
        if !hooked_property_is_definitely_backed(elem, prop, fa) {
            return;
        }
        if hook_body_assigns_this_property(&set_hook.body, prop, fa) {
            return;
        }
        if hook_body_has_terminator(&set_hook.body) {
            return;
        }
        out.push(
            Diagnostic::error(
                hook_span(set_hook),
                format!(
                    "Set hook for non-virtual property {}::${prop} does not assign value to it.",
                    class_fqn.trim_start_matches('\\')
                ),
            )
            .with_code("propertySetHook.noAssign"),
        );
    });
    out
}

// --- SetPropertyHookParameterRule (level 0, conservative) -----------------

fn run_set_property_hook_parameter(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            check_set_property_hook_parameter_stmt(fa, scope, st, &mut out);
        }
    });
    out
}

fn check_set_property_hook_parameter_stmt(
    fa: &FileAnalysis,
    scope: &Scope,
    st: &Stmt,
    out: &mut Vec<Diagnostic>,
) {
    match &st.kind {
        StmtKind::Class(c) => {
            let fqn = c
                .name
                .map(|n| scope.qualify(fa.interner.resolve(n)))
                .unwrap_or_else(|| "class@anonymous".to_string());
            let reflected = fa.reflect_class(scope, &fqn, c);
            for m in &c.members {
                let Member::Property(pd) = m else { continue };
                for elem in &pd.props {
                    let prop = fa.interner.resolve(elem.name);
                    let Some(set_hook) = hook_named(elem, fa, "set") else {
                        continue;
                    };
                    let Some(params) = &set_hook.params else {
                        continue;
                    };
                    let Some(param) = params.first() else {
                        continue;
                    };
                    let Some(prop_refl) = reflected.properties.iter().find(|p| p.name == prop)
                    else {
                        continue;
                    };
                    let ctx = SetHookParameterContext {
                        fa,
                        scope,
                        class_name: fqn.trim_start_matches('\\'),
                        prop,
                        pd,
                        prop_type: &prop_refl.ty,
                        prop_native: &prop_refl.native_ty,
                    };
                    check_set_property_hook_parameter(&ctx, param, out);
                }
            }
        }
        StmtKind::Namespace { body: Some(b), .. } | StmtKind::Block(b) => {
            b.iter()
                .for_each(|s| check_set_property_hook_parameter_stmt(fa, scope, s, out));
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            check_set_property_hook_parameter_stmt(fa, scope, then, out);
            for e in elseifs {
                check_set_property_hook_parameter_stmt(fa, scope, &e.body, out);
            }
            if let Some(e) = els {
                check_set_property_hook_parameter_stmt(fa, scope, e, out);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => {
            check_set_property_hook_parameter_stmt(fa, scope, body, out)
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter()
                .for_each(|s| check_set_property_hook_parameter_stmt(fa, scope, s, out));
            for c in catches {
                c.body
                    .iter()
                    .for_each(|s| check_set_property_hook_parameter_stmt(fa, scope, s, out));
            }
            if let Some(fin) = finally {
                fin.iter()
                    .for_each(|s| check_set_property_hook_parameter_stmt(fa, scope, s, out));
            }
        }
        StmtKind::Switch { cases, .. } => {
            for case in cases {
                case.body
                    .iter()
                    .for_each(|s| check_set_property_hook_parameter_stmt(fa, scope, s, out));
            }
        }
        StmtKind::Declare { body: Some(b), .. } => {
            check_set_property_hook_parameter_stmt(fa, scope, b, out)
        }
        StmtKind::Function(fd) => {
            fd.body
                .iter()
                .for_each(|s| check_set_property_hook_parameter_stmt(fa, scope, s, out));
        }
        _ => {}
    }
}

struct SetHookParameterContext<'fa, 'ctx> {
    fa: &'ctx FileAnalysis<'fa>,
    scope: &'ctx Scope,
    class_name: &'ctx str,
    prop: &'ctx str,
    pd: &'ctx PropertyDecl,
    prop_type: &'ctx Type,
    prop_native: &'ctx Type,
}

fn check_set_property_hook_parameter(
    ctx: &SetHookParameterContext<'_, '_>,
    param: &Param,
    out: &mut Vec<Diagnostic>,
) {
    let fa = ctx.fa;
    let class_name = ctx.class_name;
    let prop = ctx.prop;
    let prop_type = ctx.prop_type;
    let prop_native = ctx.prop_native;
    let pname = fa.interner.resolve(param.name);
    let prop_has_native = ctx.pd.ty.is_some();
    let param_has_native = param.ty.is_some();
    let param_native = param
        .ty
        .as_ref()
        .map(|t| php_reflect::resolve_ast_type(ctx.scope, t))
        .unwrap_or(Type::Mixed);
    let mut native_failed = false;

    match (prop_has_native, param_has_native) {
        (false, true) => {
            native_failed = true;
            out.push(
                Diagnostic::error(
                    param.span,
                    format!(
                        "Parameter ${pname} of set hook has a native type but the property {class_name}::${prop} does not."
                    ),
                )
                .with_code("propertySetHook.nativeParameterType"),
            );
        }
        (true, false) => {
            native_failed = true;
            out.push(
                Diagnostic::error(
                    param.span,
                    format!(
                        "Parameter ${pname} of set hook does not have a native type but the property {class_name}::${prop} does."
                    ),
                )
                .with_code("propertySetHook.nativeParameterType"),
            );
        }
        (true, true)
            if native_hook_type_is_checkable(prop_native, fa)
                && native_hook_type_is_checkable(&param_native, fa)
                && !native_type_is_accepted_by_parameter(fa, prop_native, &param_native) =>
        {
            native_failed = true;
            out.push(
                Diagnostic::error(
                    param.span,
                    format!(
                        "Native type {param_native} of set hook parameter ${pname} is not contravariant with native type {prop_native} of property {class_name}::${prop}."
                    ),
                )
                .with_code("propertySetHook.nativeParameterType"),
            );
        }
        _ => {}
    }

    if native_failed {
        return;
    }

    if fa.treat_phpdoc_types_as_certain
        && property_readable_type_is_certain(fa, prop_type, prop_native)
        && !php_infer::is_assignable(fa.reflection, prop_type, &param_native)
    {
        out.push(
            Diagnostic::error(
                param.span,
                format!(
                    "Type {param_native} of set hook parameter ${pname} is not contravariant with type {prop_type} of property {class_name}::${prop}."
                ),
            )
            .with_code("propertySetHook.parameterType"),
        );
    }

    if param_native == *prop_type {
        return;
    }

    for word in bare_iterable_words(&param_native) {
        out.push(
            Diagnostic::error(
                param.span,
                format!(
                    "Set hook for property {class_name}::${prop} has parameter ${pname} with no value type specified in iterable type {word}."
                ),
            )
            .with_code("missingType.iterableValue"),
        );
    }

    for (name, templates) in non_generic_object_types_with_generic_class(fa, &param_native) {
        out.push(
            Diagnostic::error(
                param.span,
                format!(
                    "Set hook for property {class_name}::${prop} has parameter ${pname} with generic {name} but does not specify its types: {templates}"
                ),
            )
            .with_code("missingType.generics"),
        );
    }

    for callable in callables_with_missing_signature(&param_native) {
        out.push(
            Diagnostic::error(
                param.span,
                format!(
                    "Set hook for property {class_name}::${prop} has parameter ${pname} with no signature specified for {callable}."
                ),
            )
            .with_code("missingType.callable"),
        );
    }
}

fn native_hook_type_is_checkable(ty: &Type, fa: &FileAnalysis) -> bool {
    match ty {
        Type::Mixed
        | Type::ExplicitMixed
        | Type::Never
        | Type::Void
        | Type::SelfType
        | Type::StaticType
        | Type::Parent
        | Type::TemplateVar(_)
        | Type::Unknown(_)
        | Type::Conditional { .. }
        | Type::Intersection(_)
        | Type::List(_)
        | Type::Shape { .. }
        | Type::ClassString(_)
        | Type::LiteralInt(_)
        | Type::LiteralString(_)
        | Type::StringOf(_)
        | Type::EnumCase { .. }
        | Type::NonEmpty(_) => false,
        Type::Named { fqn, args } => args.is_empty() && fa.reflection.class(fqn).is_some(),
        Type::Nullable(inner) => native_hook_type_is_checkable(inner, fa),
        Type::Union(parts) => {
            !parts.is_empty() && parts.iter().all(|p| native_hook_type_is_checkable(p, fa))
        }
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            native_hook_type_is_checkable(&kv.0, fa) && native_hook_type_is_checkable(&kv.1, fa)
        }
        Type::Callable(Some(sig)) => {
            sig.params
                .iter()
                .all(|p| native_hook_type_is_checkable(p, fa))
                && native_hook_type_is_checkable(&sig.ret, fa)
        }
        Type::Null
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Int
        | Type::IntRange { .. }
        | Type::Float
        | Type::String
        | Type::Object
        | Type::Resource
        | Type::Array(None)
        | Type::Iterable(None)
        | Type::Callable(None) => true,
    }
}

fn native_type_is_accepted_by_parameter(fa: &FileAnalysis, value: &Type, target: &Type) -> bool {
    match value {
        Type::Union(parts) => {
            return parts
                .iter()
                .all(|p| native_type_is_accepted_by_parameter(fa, p, target));
        }
        Type::Nullable(inner) => {
            return native_type_is_accepted_by_parameter(fa, inner, target)
                && native_type_is_accepted_by_parameter(fa, &Type::Null, target);
        }
        _ => {}
    }

    match target {
        Type::Nullable(inner) => {
            matches!(value, Type::Null) || native_type_is_accepted_by_parameter(fa, value, inner)
        }
        Type::Union(parts) => parts
            .iter()
            .any(|p| native_type_is_accepted_by_parameter(fa, value, p)),
        _ => php_infer::is_assignable(fa.reflection, value, target),
    }
}

fn property_readable_type_is_certain(
    fa: &FileAnalysis,
    prop_type: &Type,
    prop_native: &Type,
) -> bool {
    prop_native.is_mixed()
        || (native_hook_type_is_checkable(prop_native, fa)
            && php_infer::is_assignable(fa.reflection, prop_type, prop_native))
}

fn bare_iterable_words(ty: &Type) -> Vec<&'static str> {
    crate::missing_type::type_iterable_words(ty)
}

fn non_generic_object_types_with_generic_class(
    fa: &FileAnalysis,
    ty: &Type,
) -> Vec<(String, String)> {
    crate::missing_type::type_generic_args_in_union(fa.reflection, ty)
}

fn callables_with_missing_signature(ty: &Type) -> Vec<String> {
    crate::missing_type::type_callable_signature_words(ty)
        .into_iter()
        .map(str::to_string)
        .collect()
}

fn hook_named<'a>(elem: &'a PropElem, fa: &FileAnalysis, name: &str) -> Option<&'a PropertyHook> {
    elem.hooks
        .as_ref()?
        .iter()
        .find(|h| fa.interner.resolve(h.name).eq_ignore_ascii_case(name))
}

fn hooked_property_is_definitely_backed(elem: &PropElem, prop: &str, fa: &FileAnalysis) -> bool {
    let Some(hooks) = &elem.hooks else {
        return false;
    };
    hooks.iter().any(|h| {
        if fa.interner.resolve(h.name).eq_ignore_ascii_case("set") {
            matches!(h.body, HookBody::Short(_))
                || hook_body_assigns_this_property(&h.body, prop, fa)
        } else {
            hook_body_reads_this_property(&h.body, prop, fa)
        }
    })
}

fn hook_span(hook: &PropertyHook) -> Span {
    // The hook-name token (`get` / `set`).
    hook.name_span
}

fn hook_body_reads_this_property(body: &HookBody, prop: &str, fa: &FileAnalysis) -> bool {
    let mut found = false;
    let write_targets = hook_body_plain_write_target_spans(body);
    hook_body_exprs(body, &mut |e| {
        if found {
            return;
        }
        let r = e.span.range();
        if expr_is_this_property(e, prop, fa)
            && !write_targets.contains(&(r.start as u32, r.end as u32))
        {
            found = true;
        }
    });
    found
}

fn hook_body_assigns_this_property(body: &HookBody, prop: &str, fa: &FileAnalysis) -> bool {
    let mut found = false;
    hook_body_exprs(body, &mut |e| {
        if found {
            return;
        }
        let (ExprKind::Assign { target, .. } | ExprKind::AssignRef { target, .. }) = &e.kind else {
            return;
        };
        if expr_is_this_property(target, prop, fa) {
            found = true;
        }
    });
    found
}

fn hook_body_plain_write_target_spans(body: &HookBody) -> Vec<(u32, u32)> {
    let mut spans = Vec::new();
    hook_body_exprs(body, &mut |e| {
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

fn hook_body_has_terminator(body: &HookBody) -> bool {
    let mut found = false;
    if let HookBody::Block(stmts) = body {
        for st in stmts {
            stmt_has_terminator(st, &mut found);
        }
    }
    found
}

fn stmt_has_terminator(st: &Stmt, found: &mut bool) {
    if *found {
        return;
    }
    match &st.kind {
        StmtKind::Return(_) => *found = true,
        StmtKind::Expr(e) => expr_has_terminator(e, found),
        StmtKind::Block(b) => b.iter().for_each(|s| stmt_has_terminator(s, found)),
        StmtKind::If {
            cond,
            then,
            elseifs,
            els,
        } => {
            expr_has_terminator(cond, found);
            stmt_has_terminator(then, found);
            for e in elseifs {
                expr_has_terminator(&e.cond, found);
                stmt_has_terminator(&e.body, found);
            }
            if let Some(e) = els {
                stmt_has_terminator(e, found);
            }
        }
        StmtKind::While { cond, body } => {
            expr_has_terminator(cond, found);
            stmt_has_terminator(body, found);
        }
        StmtKind::DoWhile { body, cond } => {
            stmt_has_terminator(body, found);
            expr_has_terminator(cond, found);
        }
        StmtKind::For {
            init,
            cond,
            update,
            body,
        } => {
            for e in init.iter().chain(cond).chain(update) {
                expr_has_terminator(e, found);
            }
            stmt_has_terminator(body, found);
        }
        StmtKind::Foreach {
            subject,
            key,
            value,
            body,
            ..
        } => {
            expr_has_terminator(subject, found);
            if let Some(k) = key {
                expr_has_terminator(k, found);
            }
            expr_has_terminator(value, found);
            stmt_has_terminator(body, found);
        }
        StmtKind::Switch { subject, cases } => {
            expr_has_terminator(subject, found);
            for c in cases {
                if let Some(t) = &c.test {
                    expr_has_terminator(t, found);
                }
                c.body.iter().for_each(|s| stmt_has_terminator(s, found));
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter().for_each(|s| stmt_has_terminator(s, found));
            for c in catches {
                c.body.iter().for_each(|s| stmt_has_terminator(s, found));
            }
            if let Some(f) = finally {
                f.iter().for_each(|s| stmt_has_terminator(s, found));
            }
        }
        _ => {}
    }
}

fn expr_has_terminator(e: &Expr, found: &mut bool) {
    walk_expr_local(e, &mut |inner| {
        if matches!(inner.kind, ExprKind::Throw(_) | ExprKind::Exit(_)) {
            *found = true;
        }
    });
}

fn hook_body_exprs(body: &HookBody, f: &mut impl FnMut(&Expr)) {
    match body {
        HookBody::Block(stmts) => stmts.iter().for_each(|s| stmt_exprs(s, f)),
        HookBody::Short(e) => walk_expr_local(e, f),
        HookBody::Abstract => {}
    }
}

fn expr_is_this_property(e: &Expr, prop: &str, fa: &FileAnalysis) -> bool {
    let ExprKind::Prop {
        base,
        name: MemberName::Ident(p),
        ..
    } = &e.kind
    else {
        return false;
    };
    matches!(&base.kind, ExprKind::Variable(v) if fa.interner.resolve(*v) == "this")
        && fa.interner.resolve(*p) == prop
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
    for_each_property_elem(fa, &mut |class_fqn, class, pd, elem| {
        let prop = fa.interner.resolve(elem.name).to_string();
        let proto = class.extends.iter().find_map(|p| {
            fa.reflection
                .find_property(p.text.trim_start_matches('\\'), &prop)
        });
        let has_override = has_override_attr(&pd.attrs);
        let span = span_of(elem);

        let proto = match proto {
            Some(proto) => proto,
            None => {
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
                return;
            }
        };
        let parent = proto.declaring_class;

        // `#[\Override]` on a *property* only exists in PHP ≥ 8.5, so phpstan
        // gates `property.missingOverride` on `supportsOverrideAttributeOnProperty()`
        // (versionId ≥ 80500). Below that target it reports nothing.
        if fa.php_version.at_least(80500) && has_override_should_be_present(class, has_override) {
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

        let child = fa
            .reflection
            .class(class_fqn)
            .and_then(|c| c.properties.iter().find(|p| p.name == prop));
        if let Some(child) = child {
            check_overriding_property_type(
                fa,
                PropertyOverrideType {
                    class,
                    pd,
                    elem,
                    prop: &prop,
                    proto: &proto,
                    child,
                },
                &mut out,
            );
        }

        // Visibility may not be narrowed.
        let own_vis = m.visibility.unwrap_or(Visibility::Public);
        if proto.member.visibility == Visibility::Public && own_vis != Visibility::Public {
            let kind = if own_vis == Visibility::Private {
                "Private"
            } else {
                "Protected"
            };
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
        } else if proto.member.visibility == Visibility::Protected && own_vis == Visibility::Private
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
    });
    out
}

fn has_native_decl(t: &Type) -> bool {
    !matches!(t, Type::Mixed)
}

struct PropertyOverrideType<'a> {
    class: &'a ClassDecl,
    pd: &'a PropertyDecl,
    elem: &'a PropElem,
    prop: &'a str,
    proto: &'a php_reflect::Found<'a, php_reflect::PropertyReflection>,
    child: &'a php_reflect::PropertyReflection,
}

fn check_overriding_property_type(
    fa: &FileAnalysis,
    ctx: PropertyOverrideType<'_>,
    out: &mut Vec<Diagnostic>,
) {
    let PropertyOverrideType {
        class,
        pd,
        elem,
        prop,
        proto,
        child,
    } = ctx;
    let parent = proto.declaring_class;
    let span = pd
        .ty
        .as_ref()
        .map(|t| t.span)
        .unwrap_or_else(|| span_of(elem));
    let child_has_native = has_native_decl(&child.native_ty);
    let parent_has_native = has_native_decl(&proto.member.native_ty);
    let child_name = class_name(class, fa);

    if parent_has_native && !child_has_native {
        out.push(
            Diagnostic::error(
                span,
                format!(
                    "Property {child_name}::${prop} overriding property {parent}::${prop} should have native type {}.",
                    proto.member.native_ty
                ),
            )
            .with_code("property.missingNativeType"),
        );
        return;
    }

    if !parent_has_native && child_has_native {
        out.push(
            Diagnostic::error(
                span,
                format!(
                    "Property {child_name}::${prop} has native type {} but overrides property {parent}::${prop} with no native type.",
                    child.native_ty
                ),
            )
            .with_code("property.extraNativeType"),
        );
        return;
    }

    if child_has_native
        && parent_has_native
        && (compat::declaration_mismatch(
            fa,
            &child.native_ty,
            &child.native_ty,
            &proto.member.native_ty,
            &proto.member.native_ty,
        ) || compat::declaration_mismatch(
            fa,
            &proto.member.native_ty,
            &proto.member.native_ty,
            &child.native_ty,
            &child.native_ty,
        ))
    {
        out.push(
            Diagnostic::error(
                span,
                format!(
                    "Native type {} of property {child_name}::${prop} is not invariant with native type {} of overridden property {parent}::${prop}.",
                    child.native_ty, proto.member.native_ty
                ),
            )
            .with_code("property.nativeType"),
        );
    }
}

fn has_override_attr(attrs: &[AttributeGroup]) -> bool {
    attrs.iter().any(|g| {
        g.attrs.iter().any(|a| {
            a.name
                .text
                .trim_start_matches('\\')
                .eq_ignore_ascii_case("Override")
        })
    })
}

/// phpstan reports `missingOverride` only when the overriding class is not a
/// trait and the `#[\Override]` attribute is absent. (The configurable
/// `checkMissingOverrideMethodAttribute` defaults to on for our target version.)
fn has_override_should_be_present(class: &ClassDecl, has_override: bool) -> bool {
    class.kind != ClassKind::Trait && !has_override
}

fn class_name(class: &ClassDecl, fa: &FileAnalysis) -> String {
    class
        .name
        .map(|n| fa.interner.resolve(n).to_string())
        .unwrap_or_else(|| "class@anonymous".into())
}

// --- AccessPropertiesRule (level 0, $this only) ----------------------------

/// phpstan `AccessPropertiesRule` (conservative subset): `$this->prop` where the
/// enclosing class is fully known and `prop` is not defined anywhere in its
/// hierarchy. Only fires when the class + all of its ancestors are present in
/// the reflection index and the class has no `__get` magic accessor — so an
/// unresolved type never yields a false positive.
fn run_access_properties(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk_scoped(
        &fa.program.stmts,
        None,
        "",
        fa,
        &mut out,
        &mut |class, e, fa, out| {
            if fa
                .reflection
                .class(class)
                .is_some_and(|c| c.kind == ClassKind::Trait)
            {
                return;
            }
            if let ExprKind::Prop { base, name, .. } = &e.kind {
                if let (ExprKind::Variable(v), MemberName::Ident(p)) = (&base.kind, name) {
                    if fa.interner.resolve(*v) == "this" {
                        let prop = fa.interner.resolve(*p);
                        if symbols::class_tree_fully_known(fa, class)
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
        },
    );
    out
}

// --- ReadOnlyPropertyAssignRule (level 3, $this outside ctor) --------------

/// phpstan `ReadOnlyPropertyAssignRule` (conservative subset): assigning to a
/// `readonly` property `$this->p` from a method other than the constructor of
/// the declaring class. Only fires when the property is known-readonly via
/// reflection.
fn run_readonly_property_assign(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk_scoped_methods(
        &fa.program.stmts,
        None,
        false,
        "",
        fa,
        &mut out,
        &mut |class, in_ctor, e, fa, out| {
            if in_ctor {
                return;
            }
            let target = match &e.kind {
                ExprKind::Assign { target, .. } | ExprKind::AssignOp { target, .. } => target,
                _ => return,
            };
            let ExprKind::Prop { base, name, .. } = &target.kind else {
                return;
            };
            let (ExprKind::Variable(v), MemberName::Ident(p)) = (&base.kind, name) else {
                return;
            };
            if fa.interner.resolve(*v) != "this" {
                return;
            }
            let prop = fa.interner.resolve(*p);
            let Some(found) = fa.reflection.find_property(class, prop) else {
                return;
            };
            if !found.member.is_readonly {
                return;
            }
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
        },
    );
    out
}

// --- MissingReadOnlyPropertyAssignRule (level 0, straight-line ctor) --------

#[derive(Clone, Copy, PartialEq, Eq)]
enum MissingReadonlyKind {
    Native,
    PhpDoc,
}

struct MissingReadonlyProp {
    name: String,
    span: Span,
}

struct MissingReadonlyCtorScan<'a> {
    class_name: &'a str,
    kind: MissingReadonlyKind,
    candidates: &'a [MissingReadonlyProp],
    initialized: Vec<String>,
    out: Vec<Diagnostic>,
    returned: bool,
}

impl<'a> MissingReadonlyCtorScan<'a> {
    fn new(
        class_name: &'a str,
        kind: MissingReadonlyKind,
        candidates: &'a [MissingReadonlyProp],
    ) -> Self {
        Self {
            class_name,
            kind,
            candidates,
            initialized: Vec::new(),
            out: Vec::new(),
            returned: false,
        }
    }

    fn candidate(&self, prop: &str) -> Option<&MissingReadonlyProp> {
        self.candidates.iter().find(|p| p.name == prop)
    }

    fn is_initialized(&self, prop: &str) -> bool {
        self.initialized.iter().any(|p| p == prop)
    }

    fn mark_initialized(&mut self, prop: &str) {
        if !self.is_initialized(prop) {
            self.initialized.push(prop.to_string());
        }
    }

    fn note_read(&mut self, prop: &str, span: Span) {
        if self.candidate(prop).is_some() && !self.is_initialized(prop) {
            self.out.push(
                Diagnostic::error(span, self.uninitialized_access_message(prop))
                    .with_code(self.uninitialized_code()),
            );
        }
    }

    fn note_write(&mut self, prop: &str, span: Span) {
        if self.candidate(prop).is_none() {
            return;
        }
        if self.is_initialized(prop) {
            self.out.push(
                Diagnostic::error(span, self.already_assigned_message(prop))
                    .with_code(self.already_assigned_code()),
            );
        } else {
            self.mark_initialized(prop);
        }
    }

    fn uninitialized_code(&self) -> &'static str {
        match self.kind {
            MissingReadonlyKind::Native => "property.uninitializedReadonly",
            MissingReadonlyKind::PhpDoc => "property.uninitializedReadonlyByPhpDoc",
        }
    }

    fn already_assigned_code(&self) -> &'static str {
        match self.kind {
            MissingReadonlyKind::Native => "assign.readOnlyProperty",
            MissingReadonlyKind::PhpDoc => "assign.readOnlyPropertyByPhpDoc",
        }
    }

    fn missing_message(&self, prop: &str) -> String {
        match self.kind {
            MissingReadonlyKind::Native => format!(
                "Class {} has an uninitialized readonly property ${prop}. Assign it in the constructor.",
                self.class_name
            ),
            MissingReadonlyKind::PhpDoc => format!(
                "Class {} has an uninitialized @readonly property ${prop}. Assign it in the constructor.",
                self.class_name
            ),
        }
    }

    fn uninitialized_access_message(&self, prop: &str) -> String {
        match self.kind {
            MissingReadonlyKind::Native => format!(
                "Access to an uninitialized readonly property {}::${prop}.",
                self.class_name
            ),
            MissingReadonlyKind::PhpDoc => format!(
                "Access to an uninitialized @readonly property {}::${prop}.",
                self.class_name
            ),
        }
    }

    fn already_assigned_message(&self, prop: &str) -> String {
        match self.kind {
            MissingReadonlyKind::Native => format!(
                "Readonly property {}::${prop} is already assigned.",
                self.class_name
            ),
            MissingReadonlyKind::PhpDoc => format!(
                "@readonly property {}::${prop} is already assigned.",
                self.class_name
            ),
        }
    }
}

fn run_missing_readonly_property_assign(fa: &FileAnalysis) -> Vec<Diagnostic> {
    run_missing_readonly_property_assign_kind(fa, MissingReadonlyKind::Native)
}

fn run_missing_readonly_phpdoc_property_assign(fa: &FileAnalysis) -> Vec<Diagnostic> {
    run_missing_readonly_property_assign_kind(fa, MissingReadonlyKind::PhpDoc)
}

fn run_missing_readonly_property_assign_kind(
    fa: &FileAnalysis,
    kind: MissingReadonlyKind,
) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            check_missing_readonly_stmt(fa, scope, st, kind, &mut out);
        }
    });
    out
}

fn check_missing_readonly_stmt(
    fa: &FileAnalysis,
    scope: &Scope,
    st: &Stmt,
    kind: MissingReadonlyKind,
    out: &mut Vec<Diagnostic>,
) {
    match &st.kind {
        StmtKind::Class(c) => check_missing_readonly_class(fa, scope, c, kind, out),
        StmtKind::Namespace { body: Some(b), .. } | StmtKind::Block(b) => b
            .iter()
            .for_each(|s| check_missing_readonly_stmt(fa, scope, s, kind, out)),
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            check_missing_readonly_stmt(fa, scope, then, kind, out);
            for e in elseifs {
                check_missing_readonly_stmt(fa, scope, &e.body, kind, out);
            }
            if let Some(e) = els {
                check_missing_readonly_stmt(fa, scope, e, kind, out);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => check_missing_readonly_stmt(fa, scope, body, kind, out),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter()
                .for_each(|s| check_missing_readonly_stmt(fa, scope, s, kind, out));
            for c in catches {
                c.body
                    .iter()
                    .for_each(|s| check_missing_readonly_stmt(fa, scope, s, kind, out));
            }
            if let Some(fin) = finally {
                fin.iter()
                    .for_each(|s| check_missing_readonly_stmt(fa, scope, s, kind, out));
            }
        }
        StmtKind::Declare { body: Some(b), .. } => {
            check_missing_readonly_stmt(fa, scope, b, kind, out)
        }
        StmtKind::Function(fd) => {
            fd.body
                .iter()
                .for_each(|s| check_missing_readonly_stmt(fa, scope, s, kind, out));
        }
        _ => {}
    }
}

fn check_missing_readonly_class(
    fa: &FileAnalysis,
    scope: &Scope,
    class: &ClassDecl,
    kind: MissingReadonlyKind,
    out: &mut Vec<Diagnostic>,
) {
    if class.kind != ClassKind::Class {
        return;
    }
    let Some(name) = class.name else { return };
    let class_fqn = scope.qualify(fa.interner.resolve(name));
    let class_display = class_fqn.trim_start_matches('\\').to_string();
    let candidates = missing_readonly_candidates(fa, &class_fqn, class, kind);
    if candidates.is_empty() {
        return;
    }

    let ctor = class.members.iter().find_map(|m| {
        let Member::Method(md) = m else { return None };
        fa.interner
            .resolve(md.name)
            .eq_ignore_ascii_case("__construct")
            .then_some(md)
    });

    let Some(ctor) = ctor else {
        for prop in &candidates {
            out.push(
                Diagnostic::error(
                    prop.span,
                    missing_readonly_message(kind, &class_display, &prop.name),
                )
                .with_code(missing_readonly_uninitialized_code(kind)),
            );
        }
        return;
    };
    let Some(body) = &ctor.body else { return };

    let mut scan = MissingReadonlyCtorScan::new(&class_display, kind, &candidates);
    if !scan_missing_readonly_ctor_body(fa, body, &mut scan) {
        return;
    }
    for prop in &candidates {
        if !scan.is_initialized(&prop.name) {
            out.push(
                Diagnostic::error(prop.span, scan.missing_message(&prop.name))
                    .with_code(scan.uninitialized_code()),
            );
        }
    }
    out.extend(scan.out);
}

fn missing_readonly_candidates(
    fa: &FileAnalysis,
    class_fqn: &str,
    class: &ClassDecl,
    kind: MissingReadonlyKind,
) -> Vec<MissingReadonlyProp> {
    let mut props = Vec::new();
    for m in &class.members {
        let Member::Property(pd) = m else { continue };
        if pd.modifiers.is_static || pd.modifiers.is_abstract || pd.ty.is_none() {
            continue;
        }
        let doc = pd.doc.as_deref();
        let is_phpdoc = doc.is_some_and(|d| has_readonly_doc(d, "readonly"));
        for elem in &pd.props {
            if elem.default.is_some() || elem.hooks.as_ref().is_some_and(|h| !h.is_empty()) {
                continue;
            }
            let prop = fa.interner.resolve(elem.name);
            let Some(info) = property_decl_info(fa, class_fqn, prop) else {
                continue;
            };
            let matches_kind = match kind {
                MissingReadonlyKind::Native => info.is_native_readonly,
                MissingReadonlyKind::PhpDoc => is_phpdoc && !info.is_native_readonly,
            };
            if matches_kind && symbols::same_fqn(&info.declaring_class, class_fqn) {
                props.push(MissingReadonlyProp {
                    name: prop.to_string(),
                    span: span_of(elem),
                });
            }
        }
    }
    props
}

fn missing_readonly_uninitialized_code(kind: MissingReadonlyKind) -> &'static str {
    match kind {
        MissingReadonlyKind::Native => "property.uninitializedReadonly",
        MissingReadonlyKind::PhpDoc => "property.uninitializedReadonlyByPhpDoc",
    }
}

fn missing_readonly_message(kind: MissingReadonlyKind, class: &str, prop: &str) -> String {
    match kind {
        MissingReadonlyKind::Native => format!(
            "Class {class} has an uninitialized readonly property ${prop}. Assign it in the constructor."
        ),
        MissingReadonlyKind::PhpDoc => format!(
            "Class {class} has an uninitialized @readonly property ${prop}. Assign it in the constructor."
        ),
    }
}

fn scan_missing_readonly_ctor_body(
    fa: &FileAnalysis,
    body: &[Stmt],
    scan: &mut MissingReadonlyCtorScan<'_>,
) -> bool {
    for st in body {
        if scan.returned {
            break;
        }
        if !scan_missing_readonly_ctor_stmt(fa, st, scan) {
            return false;
        }
    }
    true
}

fn scan_missing_readonly_ctor_stmt(
    fa: &FileAnalysis,
    st: &Stmt,
    scan: &mut MissingReadonlyCtorScan<'_>,
) -> bool {
    match &st.kind {
        StmtKind::Expr(e) => scan_missing_readonly_ctor_expr(fa, e, scan, false, true),
        StmtKind::Echo(es) => es
            .iter()
            .all(|e| scan_missing_readonly_ctor_expr(fa, e, scan, false, false)),
        StmtKind::Return(e) => {
            if let Some(e) = e {
                if !scan_missing_readonly_ctor_expr(fa, e, scan, false, false) {
                    return false;
                }
            }
            scan.returned = true;
            true
        }
        StmtKind::Block(b) => scan_missing_readonly_ctor_body(fa, b, scan),
        _ => false,
    }
}

fn scan_missing_readonly_ctor_expr(
    fa: &FileAnalysis,
    e: &Expr,
    scan: &mut MissingReadonlyCtorScan<'_>,
    as_write_target: bool,
    allow_writes: bool,
) -> bool {
    match &e.kind {
        ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Name(_)
        | ExprKind::Variable(_) => true,
        ExprKind::Paren(x)
        | ExprKind::Unary { expr: x, .. }
        | ExprKind::Cast { expr: x, .. }
        | ExprKind::ErrorSuppress(x)
        | ExprKind::Print(x)
        | ExprKind::Empty(x) => scan_missing_readonly_ctor_expr(fa, x, scan, false, false),
        ExprKind::Array { items, .. } => items.iter().all(|it| {
            it.key
                .as_ref()
                .is_none_or(|k| scan_missing_readonly_ctor_expr(fa, k, scan, false, false))
                && it
                    .value
                    .as_ref()
                    .is_none_or(|v| scan_missing_readonly_ctor_expr(fa, v, scan, false, false))
        }),
        ExprKind::Interpolated(parts) | ExprKind::ShellExec(parts) | ExprKind::Isset(parts) => {
            parts
                .iter()
                .all(|p| scan_missing_readonly_ctor_expr(fa, p, scan, false, false))
        }
        ExprKind::Index { base, index } => {
            scan_missing_readonly_ctor_expr(fa, base, scan, false, false)
                && index
                    .as_ref()
                    .is_none_or(|i| scan_missing_readonly_ctor_expr(fa, i, scan, false, false))
        }
        ExprKind::Prop { base, name, .. } => {
            let ExprKind::Variable(v) = &base.kind else {
                return scan_missing_readonly_ctor_expr(fa, base, scan, false, false);
            };
            if fa.interner.resolve(*v) != "this" {
                return true;
            }
            let MemberName::Ident(p) = name else {
                return false;
            };
            let prop = fa.interner.resolve(*p);
            if as_write_target {
                if !allow_writes {
                    return false;
                }
                scan.note_write(prop, e.span);
            } else {
                scan.note_read(prop, e.span);
            }
            true
        }
        ExprKind::Assign { target, rhs } => {
            if !allow_writes {
                return false;
            }
            if !scan_missing_readonly_ctor_expr(fa, rhs, scan, false, false) {
                return false;
            }
            if matches!(&target.kind, ExprKind::Prop { .. }) {
                scan_missing_readonly_ctor_expr(fa, target, scan, true, true)
            } else if property_fetch_from_write_target(target).is_some() {
                false
            } else {
                scan_missing_readonly_ctor_expr(fa, target, scan, false, false)
            }
        }
        ExprKind::AssignOp { target, rhs, .. } => {
            if !allow_writes {
                return false;
            }
            if property_fetch_from_write_target(target).is_some()
                && !matches!(&target.kind, ExprKind::Prop { .. })
            {
                return false;
            }
            if !scan_missing_readonly_ctor_expr(fa, target, scan, false, false)
                || !scan_missing_readonly_ctor_expr(fa, rhs, scan, false, false)
            {
                return false;
            }
            if let ExprKind::Prop { base, name, .. } = &target.kind {
                if matches!(&base.kind, ExprKind::Variable(v) if fa.interner.resolve(*v) == "this")
                {
                    let MemberName::Ident(p) = name else {
                        return false;
                    };
                    let prop = fa.interner.resolve(*p);
                    if scan.candidate(prop).is_some() && scan.is_initialized(prop) {
                        scan.note_write(prop, target.span);
                    }
                }
            }
            true
        }
        ExprKind::Binary { lhs, rhs, .. } | ExprKind::Coalesce { lhs, rhs } => {
            scan_missing_readonly_ctor_expr(fa, lhs, scan, false, false)
                && scan_missing_readonly_ctor_expr(fa, rhs, scan, false, false)
        }
        ExprKind::Ternary { cond, then, els } => {
            scan_missing_readonly_ctor_expr(fa, cond, scan, false, false)
                && then
                    .as_ref()
                    .is_none_or(|t| scan_missing_readonly_ctor_expr(fa, t, scan, false, false))
                && scan_missing_readonly_ctor_expr(fa, els, scan, false, false)
        }
        ExprKind::PreInc(x) | ExprKind::PreDec(x) | ExprKind::PostInc(x) | ExprKind::PostDec(x) => {
            if !allow_writes {
                return false;
            }
            if property_fetch_from_write_target(x).is_some()
                && !matches!(&x.kind, ExprKind::Prop { .. })
            {
                return false;
            }
            if !scan_missing_readonly_ctor_expr(fa, x, scan, false, false) {
                return false;
            }
            if let ExprKind::Prop { base, name, .. } = &x.kind {
                if matches!(&base.kind, ExprKind::Variable(v) if fa.interner.resolve(*v) == "this")
                {
                    let MemberName::Ident(p) = name else {
                        return false;
                    };
                    let prop = fa.interner.resolve(*p);
                    if scan.candidate(prop).is_some() && scan.is_initialized(prop) {
                        scan.note_write(prop, x.span);
                    }
                }
            }
            true
        }
        ExprKind::Exit(e) => {
            if let Some(e) = e {
                scan_missing_readonly_ctor_expr(fa, e, scan, false, false)
            } else {
                true
            }
        }
        _ => false,
    }
}

// --- ReadOnlyPropertyAssignRefRule (level 3, conservative) ----------------

/// phpstan `ReadOnlyPropertyAssignRefRule` (`property.readOnlyAssignByRef`):
/// assigning a native `readonly` property by reference is forbidden. FP-safe
/// subset: `$this->prop` where the property is declared on the current class and
/// known native-readonly. External receivers need PHPStan's `canWriteProperty`
/// visibility/asymmetric-set checks, so they are left to future work.
fn run_readonly_property_assign_ref(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk_scoped_methods(
        &fa.program.stmts,
        None,
        false,
        "",
        fa,
        &mut out,
        &mut |class, _in_ctor, e, fa, out| {
            let ExprKind::AssignRef { rhs, .. } = &e.kind else {
                return;
            };
            let ExprKind::Prop { base, name, .. } = &rhs.kind else {
                return;
            };
            let (ExprKind::Variable(v), MemberName::Ident(p)) = (&base.kind, name) else {
                return;
            };
            if fa.interner.resolve(*v) != "this" {
                return;
            }
            let prop = fa.interner.resolve(*p);
            let Some(found) = fa.reflection.find_property(class, prop) else {
                return;
            };
            if found.declaring_class.trim_start_matches('\\') != class.trim_start_matches('\\') {
                return;
            }
            if !found.member.is_readonly || found.member.magic {
                return;
            }
            out.push(
                Diagnostic::error(
                    e.span,
                    format!(
                        "Readonly property {}::${prop} is assigned by reference.",
                        found.declaring_class.trim_start_matches('\\')
                    ),
                )
                .with_code("property.readOnlyAssignByRef"),
            );
        },
    );
    out
}

// --- PropertyAssignRefRule (level 0, PHP 8.4+) ----------------------------

/// phpstan `PropertyAssignRefRule` (`property.assignByRef`): assigning a
/// property by reference is forbidden when the current scope cannot write that
/// property (private/protected or asymmetric private(set)/protected(set)).
/// FP-safe subset: an exact receiver class (`$this`, a typed/inferred object)
/// and a statically named instance property.
fn run_property_assign_ref(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    if !fa.php_version.at_least(80400) {
        return out;
    }
    walk_exprs_with_class(
        &fa.program.stmts,
        None,
        "",
        fa,
        &mut out,
        &mut |current_class, e, fa, out| {
            let ExprKind::AssignRef { rhs, .. } = &e.kind else {
                return;
            };
            let Some((base, prop)) = property_fetch_parts(fa, rhs) else {
                return;
            };
            let Some(receiver_class) = receiver_class_for_property_fetch(fa, current_class, base)
            else {
                return;
            };
            let Some(info) = property_decl_info(fa, &receiver_class, prop) else {
                return;
            };
            if can_write_property(fa, current_class, &info) {
                return;
            }
            out.push(
                Diagnostic::error(
                    rhs.span,
                    format!(
                        "Property {}::${prop} with {} visibility is assigned by reference.",
                        info.declaring_class.trim_start_matches('\\'),
                        write_visibility_label(&info),
                    ),
                )
                .with_code("property.assignByRef"),
            );
        },
    );
    out
}

// --- ReadOnlyByPhpDocPropertyAssignRefRule (level 3) ----------------------

/// phpstan `ReadOnlyByPhpDocPropertyAssignRefRule`
/// (`property.readOnlyByPhpDocAssignByRef`), for real properties whose declaring
/// property docblock is in this file. Cross-file PHPDoc readonly metadata is not
/// yet reflected, so those cases are skipped rather than guessed.
fn run_readonly_phpdoc_property_assign_ref(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk_exprs_with_class(
        &fa.program.stmts,
        None,
        "",
        fa,
        &mut out,
        &mut |current_class, e, fa, out| {
            let ExprKind::AssignRef { rhs, .. } = &e.kind else {
                return;
            };
            let Some((base, prop)) = property_fetch_parts(fa, rhs) else {
                return;
            };
            let Some(receiver_class) = receiver_class_for_property_fetch(fa, current_class, base)
            else {
                return;
            };
            let Some(info) = property_decl_info(fa, &receiver_class, prop) else {
                return;
            };
            if !info.doc_readonly || info.is_native_readonly {
                return;
            }
            if !can_write_property(fa, current_class, &info) {
                return;
            }
            out.push(
                Diagnostic::error(
                    rhs.span,
                    format!(
                        "@readonly property {}::${prop} is assigned by reference.",
                        info.declaring_class.trim_start_matches('\\')
                    ),
                )
                .with_code("property.readOnlyByPhpDocAssignByRef"),
            );
        },
    );
    out
}

// --- ReadOnlyByPhpDocPropertyAssignRule (level 3) -------------------------

/// phpstan `ReadOnlyByPhpDocPropertyAssignRule`: assignments to a real
/// `@readonly` property must happen on `$this` inside the declaring class's
/// constructor (or `__unserialize`). `@*-allow-private-mutation` permits later
/// in-class writes, matching phpstan's `isAllowedPrivateMutation()`.
fn run_readonly_phpdoc_property_assign(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk_exprs_with_method_context(
        &fa.program.stmts,
        None,
        false,
        "",
        fa,
        &mut out,
        &mut |current_class, in_ctor, e, fa, out| {
            let fetch = match &e.kind {
                ExprKind::Assign { target, .. } | ExprKind::AssignOp { target, .. } => {
                    property_fetch_from_write_target(target)
                }
                ExprKind::PreInc(target)
                | ExprKind::PreDec(target)
                | ExprKind::PostInc(target)
                | ExprKind::PostDec(target) => property_fetch_from_write_target(target),
                _ => None,
            };
            let Some(fetch) = fetch else { return };
            let Some((base, prop)) = property_fetch_parts(fa, fetch) else {
                return;
            };
            let Some(receiver_class) = receiver_class_for_property_fetch(fa, current_class, base)
            else {
                return;
            };
            let Some(info) = property_decl_info(fa, &receiver_class, prop) else {
                return;
            };
            if !info.doc_readonly || info.is_native_readonly {
                return;
            }
            if !can_write_property(fa, current_class, &info) {
                return;
            }

            let declaring = info.declaring_class.trim_start_matches('\\');
            let outside_declaring =
                current_class.is_none_or(|c| !symbols::same_fqn(c, &info.declaring_class));
            if outside_declaring {
                out.push(
                    Diagnostic::error(
                        fetch.span,
                        format!(
                            "@readonly property {declaring}::${prop} is assigned outside of its declaring class."
                        ),
                    )
                    .with_code("property.readOnlyByPhpDocAssignOutOfClass"),
                );
                return;
            }

            let assigned_on_this =
                matches!(&base.kind, ExprKind::Variable(v) if fa.interner.resolve(*v) == "this");
            if in_ctor {
                if !assigned_on_this {
                    out.push(
                        Diagnostic::error(
                            fetch.span,
                            format!(
                                "@readonly property {declaring}::${prop} is not assigned on $this."
                            ),
                        )
                        .with_code("property.readOnlyByPhpDocAssignNotOnThis"),
                    );
                }
                return;
            }

            if info.doc_allow_private_mutation {
                return;
            }
            out.push(
                Diagnostic::error(
                    fetch.span,
                    format!(
                        "@readonly property {declaring}::${prop} is assigned outside of the constructor."
                    ),
                )
                .with_code("property.readOnlyByPhpDocAssignNotInConstructor"),
            );
        },
    );
    out
}

// --- AccessPrivatePropertyThroughStaticRule (level 2) ---------------------

/// phpstan `AccessPrivatePropertyThroughStaticRule`
/// (`staticClassAccess.privateProperty`): `static::$p` is unsafe for a private
/// static property declared on a non-final class, because late static binding can
/// target a subclass where the private slot is not the same property.
fn run_access_private_property_through_static(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk_exprs_with_class(
        &fa.program.stmts,
        None,
        "",
        fa,
        &mut out,
        &mut |current_class, e, fa, out| {
            let Some(current_class) = current_class else {
                return;
            };
            let ExprKind::StaticProp { class, name } = &e.kind else {
                return;
            };
            let (ExprKind::Name(class_name), MemberName::Var(p)) = (&class.kind, name) else {
                return;
            };
            if !class_name.text.eq_ignore_ascii_case("static") {
                return;
            }
            if fa
                .reflection
                .class(current_class)
                .is_none_or(|c| c.is_final)
            {
                return;
            }
            let prop = fa.interner.resolve(*p);
            let Some(info) = property_decl_info(fa, current_class, prop) else {
                return;
            };
            if !info.is_static
                || info.visibility != Visibility::Private
                || !symbols::same_fqn(&info.declaring_class, current_class)
            {
                return;
            }
            out.push(
                Diagnostic::error(
                    e.span,
                    format!(
                        "Unsafe access to private property {}::${prop} through static::.",
                        info.declaring_class.trim_start_matches('\\')
                    ),
                )
                .with_code("staticClassAccess.privateProperty"),
            );
        },
    );
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
    name.as_ref()
        .map(|n| n.text.trim_start_matches('\\').to_string())
        .unwrap_or_default()
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
            StmtKind::Namespace {
                name,
                body: Some(b),
            } => walk_scoped(b, None, &ns_of(name), fa, out, on_expr),
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
                            let method = fa.interner.resolve(md.name);
                            let is_ctor = method.eq_ignore_ascii_case("__construct")
                                || method.eq_ignore_ascii_case("__unserialize")
                                || method.eq_ignore_ascii_case("__clone");
                            walk_scoped_methods(
                                body,
                                fqn.as_deref(),
                                is_ctor,
                                &cur_ns,
                                fa,
                                out,
                                on_expr,
                            );
                        }
                    }
                }
            }
            StmtKind::Namespace {
                name,
                body: Some(b),
            } => walk_scoped_methods(b, None, in_ctor, &ns_of(name), fa, out, on_expr),
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

/// Walk all expressions while tracking the enclosing named class, if any.
/// Nested functions/classes reset the class scope; closures/arrow functions
/// inherit it through `stmt_exprs`/`walk_expr_local`.
fn walk_exprs_with_class(
    stmts: &[Stmt],
    cur_class: Option<&str>,
    ns: &str,
    fa: &FileAnalysis,
    out: &mut Vec<Diagnostic>,
    on_expr: &mut impl FnMut(Option<&str>, &Expr, &FileAnalysis, &mut Vec<Diagnostic>),
) {
    let mut cur_ns = ns.to_string();
    for s in stmts {
        match &s.kind {
            StmtKind::Class(c) => {
                let fqn = c.name.map(|n| qualify_fqn(&cur_ns, fa.interner.resolve(n)));
                for m in &c.members {
                    if let Member::Method(md) = m {
                        if let Some(body) = &md.body {
                            walk_exprs_with_class(body, fqn.as_deref(), &cur_ns, fa, out, on_expr);
                        }
                    }
                }
            }
            StmtKind::Namespace {
                name,
                body: Some(b),
            } => walk_exprs_with_class(b, None, &ns_of(name), fa, out, on_expr),
            StmtKind::Namespace { name, body: None } => cur_ns = ns_of(name),
            StmtKind::Function(fd) => {
                walk_exprs_with_class(&fd.body, None, &cur_ns, fa, out, on_expr)
            }
            _ => stmt_exprs(s, &mut |e| on_expr(cur_class, e, fa, out)),
        }
    }
}

/// Like [`walk_exprs_with_class`], and also marks constructor-like methods.
fn walk_exprs_with_method_context(
    stmts: &[Stmt],
    cur_class: Option<&str>,
    in_ctor: bool,
    ns: &str,
    fa: &FileAnalysis,
    out: &mut Vec<Diagnostic>,
    on_expr: &mut impl FnMut(Option<&str>, bool, &Expr, &FileAnalysis, &mut Vec<Diagnostic>),
) {
    let mut cur_ns = ns.to_string();
    for s in stmts {
        match &s.kind {
            StmtKind::Class(c) => {
                let fqn = c.name.map(|n| qualify_fqn(&cur_ns, fa.interner.resolve(n)));
                for m in &c.members {
                    if let Member::Method(md) = m {
                        if let Some(body) = &md.body {
                            let method = fa.interner.resolve(md.name);
                            let is_ctor = method.eq_ignore_ascii_case("__construct")
                                || method.eq_ignore_ascii_case("__unserialize");
                            walk_exprs_with_method_context(
                                body,
                                fqn.as_deref(),
                                is_ctor,
                                &cur_ns,
                                fa,
                                out,
                                on_expr,
                            );
                        }
                    }
                }
            }
            StmtKind::Namespace {
                name,
                body: Some(b),
            } => walk_exprs_with_method_context(b, None, in_ctor, &ns_of(name), fa, out, on_expr),
            StmtKind::Namespace { name, body: None } => cur_ns = ns_of(name),
            StmtKind::Function(fd) => {
                walk_exprs_with_method_context(&fd.body, None, false, &cur_ns, fa, out, on_expr)
            }
            _ => stmt_exprs(s, &mut |e| on_expr(cur_class, in_ctor, e, fa, out)),
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
        StmtKind::If {
            cond,
            then,
            elseifs,
            els,
        } => {
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
        StmtKind::For {
            init,
            cond,
            update,
            body,
        } => {
            for e in init.iter().chain(cond).chain(update) {
                walk_expr_local(e, on_expr);
            }
            stmt_exprs(body, on_expr);
        }
        StmtKind::Foreach {
            subject,
            key,
            value,
            body,
            ..
        } => {
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
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
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
        | ExprKind::AssignOp {
            target: lhs, rhs, ..
        }
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

// --- type helpers (general property access) ---------------------------------

/// If `ty` denotes a single, concrete object class (directly or under one level
/// of nullable/parens), return its FQN (sans leading `\`). Returns `None` for
/// unions of classes, `mixed`/`object`/unknown, scalars, generics-bound vars,
/// `self`/`static`/`parent`, etc. — anything we cannot pin to one named class.
/// This is what keeps the access rules false-positive-free: we only judge a
/// receiver whose class is unambiguous.
fn sole_class(ty: &Type) -> Option<String> {
    match ty {
        Type::Named { fqn, .. } | Type::EnumCase { fqn, .. } => {
            Some(fqn.trim_start_matches('\\').to_string())
        }
        // `?C` / `C|null`: the access itself is a *different* (nullable) problem;
        // for member existence we still know the non-null part is exactly `C`.
        Type::Nullable(inner) => sole_class(inner),
        _ => None,
    }
}

/// Does `class_fqn` (or its hierarchy) declare a magic `__get`/`__set` that would
/// make any property access legal? If so we never flag undefined properties.
fn has_magic_accessor(fqn: &str, fa: &FileAnalysis, write: bool) -> bool {
    if is_dynamic_property_class(fqn) {
        return true;
    }
    let getset = if write { "__set" } else { "__get" };
    fa.reflection.find_method(fqn, getset).is_some()
}

/// A class that legally accepts *any* property, so undefined-property access must
/// never be reported. `stdClass` is the canonical case — objects from
/// `json_decode()`, `(object) [...]` casts, and DB row fetches are `stdClass` and
/// idiomatically carry dynamic properties (phpstan never flags these).
fn is_dynamic_property_class(fqn: &str) -> bool {
    fqn.trim_start_matches('\\')
        .eq_ignore_ascii_case("stdClass")
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
    let assign_targets = assignment_target_spans_facts(fa);
    for fetch in fa.facts.property_fetches() {
        let r = fetch.expr.span.range();
        if assign_targets.contains(&(r.start as u32, r.end as u32)) {
            continue;
        }
        check_property_access(
            fa,
            fetch.expr,
            fetch.base,
            fetch.name,
            fetch.nullsafe,
            false,
            &mut out,
        );
    }
    out
}

fn assignment_target_spans_facts(fa: &FileAnalysis) -> Vec<(u32, u32)> {
    let mut spans = Vec::new();
    for assign in fa.facts.assignments() {
        if !matches!(assign.kind, AssignmentKind::Plain | AssignmentKind::Ref) {
            continue;
        }
        if matches!(&assign.target.kind, ExprKind::Prop { .. }) {
            let r = assign.target.span.range();
            spans.push((r.start as u32, r.end as u32));
        }
    }
    spans
}

fn mark_property_subtree(expr: &Expr, spans: &mut Vec<(u32, u32)>) {
    walk::for_each_subexpr(expr, &mut |e| {
        if matches!(e.kind, ExprKind::Prop { .. }) {
            let r = e.span.range();
            spans.push((r.start as u32, r.end as u32));
        }
    });
}

fn undefined_allowed_property_spans_facts(fa: &FileAnalysis) -> Vec<(u32, u32)> {
    let mut spans = Vec::new();
    for isset in fa.facts.issets() {
        for v in isset.vars {
            mark_property_subtree(v, &mut spans);
        }
    }
    for empty in fa.facts.empties() {
        mark_property_subtree(empty.inner, &mut spans);
    }
    for coalesce in fa.facts.coalesces() {
        mark_property_subtree(coalesce.lhs, &mut spans);
    }
    for assign in fa.facts.assignments() {
        if matches!(assign.kind, AssignmentKind::Op(php_ast::BinOp::Coalesce)) {
            mark_property_subtree(assign.target, &mut spans);
        }
    }
    spans
}

/// Level-8 `checkNullables` strictness for property access. Below level 8
/// phpstan strips `null` from nullable receivers before checking the property;
/// at level 8+ it reports `property.nonObject` for `$maybeC->p`. Undefined-
/// probing contexts (`isset`, `empty`, `??`) stay silent like phpstan.
fn run_nullable_property_access(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let suppressed = undefined_allowed_property_spans_facts(fa);
    let mut out = Vec::new();
    for fetch in fa.facts.property_fetches() {
        if fetch.nullsafe {
            continue;
        }
        let r = fetch.expr.span.range();
        if suppressed.contains(&(r.start as u32, r.end as u32)) {
            continue;
        }
        let MemberName::Ident(p) = fetch.name else {
            continue;
        };
        let base_ty = fa.type_of(fetch.base);
        let Some(non_null) = super::non_null_part(&base_ty) else {
            continue;
        };
        if !super::known_objectish_type(fa, &non_null) {
            continue;
        }
        let prop = fa.interner.resolve(*p);
        out.push(
            Diagnostic::error(
                fetch.expr.span,
                format!(
                    "Cannot access property ${prop} on {}.",
                    super::nullable_type_display(&base_ty)
                ),
            )
            .with_code("property.nonObject"),
        );
    }
    out
}

/// Level-7 `checkUnionTypes` for property fetches: report when a concrete
/// object union has the property on some arms and definitely lacks it on others.
/// Interface arms are skipped to avoid false positives on properties declared by
/// runtime implementors rather than by the interface type itself.
fn run_union_property_access(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.report_maybes {
        return Vec::new();
    }
    let suppressed = undefined_allowed_property_spans_facts(fa);
    let assign_targets = assignment_target_spans_facts(fa);
    let mut out = Vec::new();
    for fetch in fa.facts.property_fetches() {
        if fetch.nullsafe {
            continue;
        }
        let r = fetch.expr.span.range();
        let span = (r.start as u32, r.end as u32);
        if suppressed.contains(&span) || assign_targets.contains(&span) {
            continue;
        }
        let MemberName::Ident(p) = fetch.name else {
            continue;
        };
        let base_ty = fa.type_of(fetch.base);
        let prop = fa.interner.resolve(*p);
        let Some((has_prop, lacks_prop)) = union_property_status(fa, &base_ty, prop, false) else {
            continue;
        };
        if !(has_prop && lacks_prop) {
            continue;
        }
        out.push(
            Diagnostic::error(
                fetch.expr.span,
                format!("Access to an undefined property {base_ty}::${prop}."),
            )
            .with_code("property.notFound"),
        );
    }
    out
}

/// The write-side (`AccessPropertiesInAssignRule`): same check, but on the target
/// of an assignment, judging *write* access (so a `private(set)`-ish member could
/// differ — but our model has no asymmetric-visibility split, so for writes we
/// only report `notFound`, never private/protected, to stay FP-safe).
fn run_access_properties_in_assign(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    // Walk every assignment whose target is a (non-`$this`) property fetch.
    for assign in fa.facts.assignments() {
        if !matches!(assign.kind, AssignmentKind::Plain | AssignmentKind::Ref) {
            continue;
        }
        let target = assign.target;
        if let ExprKind::Prop {
            base,
            name,
            nullsafe,
        } = &target.kind
        {
            check_property_access(fa, target, base, name, *nullsafe, true, &mut out);
        }
    }
    out
}

fn run_union_property_access_in_assign(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.report_maybes {
        return Vec::new();
    }
    let mut out = Vec::new();
    for assign in fa.facts.assignments() {
        if !matches!(assign.kind, AssignmentKind::Plain | AssignmentKind::Ref) {
            continue;
        }
        let target = assign.target;
        let ExprKind::Prop {
            base,
            name,
            nullsafe,
        } = &target.kind
        else {
            continue;
        };
        if *nullsafe {
            continue;
        }
        let MemberName::Ident(p) = name else {
            continue;
        };
        let base_ty = fa.type_of(base);
        let prop = fa.interner.resolve(*p);
        let Some((has_prop, lacks_prop)) = union_property_status(fa, &base_ty, prop, true) else {
            continue;
        };
        if !(has_prop && lacks_prop) {
            continue;
        }
        out.push(
            Diagnostic::error(
                target.span,
                format!("Access to an undefined property {base_ty}::${prop}."),
            )
            .with_code("property.notFound"),
        );
    }
    out
}

fn union_property_status(
    fa: &FileAnalysis,
    ty: &Type,
    prop: &str,
    write: bool,
) -> Option<(bool, bool)> {
    let Type::Union(parts) = ty else {
        return None;
    };
    if parts.len() < 2 || super::type_contains_null(ty) {
        return None;
    }
    let mut has_prop = false;
    let mut lacks_prop = false;
    for part in parts.iter() {
        let Type::Named { fqn, .. } = part else {
            return None;
        };
        let class = fqn.trim_start_matches('\\');
        if !symbols::class_tree_fully_known(fa, class) {
            return None;
        }
        if fa.reflection.class(class).map(|c| c.kind) == Some(ClassKind::Interface) {
            return None;
        }
        if fa.reflection.find_property(class, prop).is_some()
            || has_magic_accessor(class, fa, write)
        {
            has_prop = true;
        } else {
            lacks_prop = true;
        }
    }
    Some((has_prop, lacks_prop))
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

    let base_ty = fa.type_of(base);
    if fa.check_nullables && super::type_contains_null(&base_ty) {
        return;
    }
    let Some(class) = sole_class(&base_ty) else {
        return;
    };
    if is_dynamic_property_class(&class) {
        return;
    }
    if matches!(
        MemberAccessResolver::new(fa).instance_property(&base_ty, prop, write),
        ResolveStatus::Unknown
    ) {
        out.push(
            Diagnostic::error(
                fetch.span,
                format!(
                    "Access to an undefined property {}::${prop}.",
                    class.trim_start_matches('\\')
                ),
            )
            .with_code("property.notFound"),
        );
    }
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
                let ExprKind::StaticProp { .. } = &e.kind else {
                    return;
                };
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
    let ExprKind::StaticProp { class, name } = &e.kind else {
        return None;
    };
    // `C::$b` — the static-property name is the `$b` variable token.
    let MemberName::Var(p) = name else {
        return None;
    };
    let ExprKind::Name(n) = &class.kind else {
        return None;
    };
    // Skip self/static/parent — need enclosing-class context.
    let fqn = match scope.resolve_class(n) {
        Resolution::Fqn(f) => f.trim_start_matches('\\').to_string(),
        _ => return None,
    };
    if !symbols::class_tree_fully_known(fa, &fqn) {
        return None;
    }
    let prop = fa.interner.resolve(*p);
    match MemberAccessResolver::new(fa).static_property(&fqn, prop) {
        ResolveStatus::Unknown => Some(
            Diagnostic::error(
                e.span,
                format!(
                    "Access to an undefined static property {}::${prop}.",
                    fqn.trim_start_matches('\\')
                ),
            )
            .with_code("staticProperty.notFound"),
        ),
        ResolveStatus::Known(_) | ResolveStatus::Opaque | ResolveStatus::Skipped => None,
    }
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
                let ExprKind::StaticProp { .. } = &e.kind else {
                    return;
                };
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
    for fetch in fa.facts.property_fetches() {
        if !fetch.nullsafe {
            continue;
        }
        let recv = fa.type_of(fetch.base);
        // Only when we are SURE it's never null: a concrete named object type.
        if matches!(recv, Type::Named { .. }) {
            let desc = type_desc(&recv);
            out.push(
                Diagnostic::error(
                    fetch.expr.span,
                    format!(
                        "Using nullsafe property access on non-nullable type {desc}. Use -> instead."
                    ),
                )
                .with_code("nullsafe.neverNull"),
            );
        }
    }
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
    let write_targets = assignment_target_spans_facts(fa);

    for fetch in fa.facts.property_fetches() {
        let MemberName::Ident(p) = fetch.name else {
            continue;
        };
        let r = fetch.expr.span.range();
        if write_targets.contains(&(r.start as u32, r.end as u32)) {
            continue; // it's a write, not a read.
        }
        let Some(class) = receiver_class(fa, fetch.base) else {
            continue;
        };
        if !symbols::class_tree_fully_known(fa, &class) {
            continue;
        }
        let prop = fa.interner.resolve(*p);
        if let Some(found) = fa.reflection.find_property(&class, prop) {
            if found.member.magic && found.member.access == PropertyAccess::WriteOnly {
                out.push(
                    Diagnostic::error(
                        fetch.expr.span,
                        format!(
                            "Property {}::${prop} is not readable.",
                            found.declaring_class.trim_start_matches('\\')
                        ),
                    )
                    .with_code("property.writeOnly"),
                );
            }
        }
    }
    out
}

// --- WritingToReadOnlyPropertiesRule (level 0) -----------------------------

/// phpstan `WritingToReadOnlyPropertiesRule` (`assign.propertyReadOnly`): writing
/// to a magic property declared `@property-read` only. FP-safe: concrete known
/// class, magic property whose access is `ReadOnly`. (Distinct from native
/// `readonly` properties — those are `ReadOnlyPropertyAssignRule`.)
fn run_writing_to_read_only(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for assign in fa.facts.assignments() {
        if !matches!(assign.kind, AssignmentKind::Plain | AssignmentKind::Op(_)) {
            continue;
        }
        let target = assign.target;
        let ExprKind::Prop { base, name, .. } = &target.kind else {
            continue;
        };
        let MemberName::Ident(p) = name else {
            continue;
        };
        let Some(class) = receiver_class(fa, base) else {
            continue;
        };
        if !symbols::class_tree_fully_known(fa, &class) {
            continue;
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
    }
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
    for_each_property(fa, &mut |class, pd| {
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
        php_ast::TypeKind::Simple(n) => n
            .text
            .trim_start_matches('\\')
            .eq_ignore_ascii_case("callable"),
        php_ast::TypeKind::Nullable(inner) => type_mentions_callable(inner),
        php_ast::TypeKind::Union(parts) | php_ast::TypeKind::Intersection(parts) => {
            parts.iter().any(type_mentions_callable)
        }
    }
}

// --- UninitializedPropertyRule (property.uninitialized) --------------------

/// phpstan `UninitializedPropertyRule` (`property.uninitialized`), gated on
/// `checkUninitializedProperties` (off by default). A **deliberately
/// conservative, FP-safe** subset: a typed, non-readonly property with no
/// default that is never assigned via `$this->prop = …` in any of the class's
/// own method bodies is reported. To stay false-positive-free without full
/// cross-hierarchy constructor flow, the check skips a class that extends
/// another class or uses a trait (either could initialize the property), and
/// bails on any method that writes `$this` dynamically, uses variable-variables,
/// or passes the property somewhere it might be initialized by reference. This
/// under-reports (e.g. a leaf class only) but never false-positives.
fn run_uninitialized_properties(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    if !fa.check_uninitialized_properties {
        return out;
    }
    crate::decls::for_each_class_like(fa, |_scope, fqn, class| {
        check_uninitialized_class(fa, fqn, class, &mut out);
    });
    out
}

struct UninitCandidate {
    sym: php_intern::Symbol,
    name: String,
    span: Span,
}

fn check_uninitialized_class(
    fa: &FileAnalysis,
    class_fqn: &str,
    class: &ClassDecl,
    out: &mut Vec<Diagnostic>,
) {
    if class.kind != ClassKind::Class || class.modifiers.is_abstract {
        return;
    }
    // A parent or trait could initialize the property outside this class body.
    if !class.extends.is_empty()
        || class
            .members
            .iter()
            .any(|m| matches!(m, Member::TraitUse(_)))
    {
        return;
    }

    let mut candidates: Vec<UninitCandidate> = Vec::new();
    for m in &class.members {
        let Member::Property(pd) = m else { continue };
        if pd.modifiers.is_static
            || pd.modifiers.is_abstract
            || pd.modifiers.is_readonly
            || pd.ty.is_none()
        {
            continue;
        }
        // `@readonly`/`@psalm-readonly` props are the readonly rule's domain.
        if pd
            .doc
            .as_deref()
            .is_some_and(|d| has_readonly_doc(d, "readonly"))
        {
            continue;
        }
        for elem in &pd.props {
            if elem.default.is_some() || elem.hooks.as_ref().is_some_and(|h| !h.is_empty()) {
                continue;
            }
            candidates.push(UninitCandidate {
                sym: elem.name,
                name: fa.interner.resolve(elem.name).to_string(),
                span: span_of(elem),
            });
        }
    }
    if candidates.is_empty() {
        return;
    }
    let cand_syms: std::collections::HashSet<php_intern::Symbol> =
        candidates.iter().map(|c| c.sym).collect();

    let mut assigned: std::collections::HashSet<php_intern::Symbol> =
        std::collections::HashSet::new();
    let mut bail = false;
    for m in &class.members {
        let Member::Method(md) = m else { continue };
        let Some(body) = &md.body else { continue };
        for st in body {
            walk::for_each_expr_in_scope(st, &mut |e| {
                scan_uninit_expr(fa, e, &cand_syms, &mut assigned, &mut bail);
            });
        }
    }
    if bail {
        return;
    }

    let class_display = class_fqn.trim_start_matches('\\');
    for cand in &candidates {
        if !assigned.contains(&cand.sym) {
            out.push(
                Diagnostic::error(
                    cand.span,
                    format!(
                        "Class {class_display} has an uninitialized property ${}. Give it default value or assign it in the constructor.",
                        cand.name
                    ),
                )
                .with_code("property.uninitialized"),
            );
        }
    }
}

/// Whether `e` is the `$this` variable.
fn is_this_var(e: &Expr, fa: &FileAnalysis) -> bool {
    matches!(&e.kind, ExprKind::Variable(s) if fa.interner.resolve(*s) == "this")
}

/// A `$this->NAME` property access with an identifier name (not dynamic).
fn this_prop_name(e: &Expr, fa: &FileAnalysis) -> Option<php_intern::Symbol> {
    match &e.kind {
        ExprKind::Prop {
            base,
            nullsafe: false,
            name: MemberName::Ident(s),
        } if is_this_var(base, fa) => Some(*s),
        _ => None,
    }
}

/// Record `$this->prop` writes into `assigned`; set `bail` on any hazard that
/// could hide an initialization (dynamic `$this` member, variable-variable, or
/// a candidate property passed as a possibly-by-reference call argument).
fn scan_uninit_expr(
    fa: &FileAnalysis,
    e: &Expr,
    cand_syms: &std::collections::HashSet<php_intern::Symbol>,
    assigned: &mut std::collections::HashSet<php_intern::Symbol>,
    bail: &mut bool,
) {
    match &e.kind {
        ExprKind::Assign { target, .. } | ExprKind::AssignRef { target, .. } => {
            note_uninit_target(fa, target, cand_syms, assigned, bail)
        }
        ExprKind::AssignOp { target, .. } => {
            note_uninit_target(fa, target, cand_syms, assigned, bail)
        }
        ExprKind::VariableVariable(_) => *bail = true,
        // Dynamic `$this->{$x}` / `$this->$v` could name any property.
        ExprKind::Prop {
            base,
            name: MemberName::Var(_) | MemberName::Expr(_),
            ..
        } if is_this_var(base, fa) => *bail = true,
        // A candidate `$this->prop` passed as a call argument might be an
        // out-parameter (by-reference) that initializes it — stay safe.
        ExprKind::Call { args, .. }
        | ExprKind::MethodCall { args, .. }
        | ExprKind::StaticCall { args, .. }
        | ExprKind::New { args, .. } => {
            for a in args {
                if this_prop_name(&a.value, fa).is_some_and(|s| cand_syms.contains(&s)) {
                    *bail = true;
                }
            }
        }
        _ => {}
    }
}

/// Mark every candidate `$this->NAME` written by assignment `target` (handles
/// list-destructure and `$this->prop[…]` append targets); bail on dynamic `$this`.
fn note_uninit_target(
    fa: &FileAnalysis,
    target: &Expr,
    cand_syms: &std::collections::HashSet<php_intern::Symbol>,
    assigned: &mut std::collections::HashSet<php_intern::Symbol>,
    bail: &mut bool,
) {
    crate::walk::for_each_subexpr(target, &mut |sub| match &sub.kind {
        ExprKind::Prop {
            base,
            name: MemberName::Ident(s),
            ..
        } if is_this_var(base, fa) && cand_syms.contains(s) => {
            assigned.insert(*s);
        }
        ExprKind::Prop {
            base,
            name: MemberName::Var(_) | MemberName::Expr(_),
            ..
        } if is_this_var(base, fa) => *bail = true,
        _ => {}
    });
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
    decls::for_each_class_like(fa, |scope, fqn, class| {
        for m in &class.members {
            let Member::Property(pd) = m else { continue };
            if pd.ty.is_some() {
                continue; // has a native type.
            }
            if doc_has_var(pd.doc.as_deref()) {
                continue; // an `@var` PHPDoc type counts as "specified".
            }
            let cname = class_name(class, fa);
            for elem in &pd.props {
                let prop = fa.interner.resolve(elem.name);
                let mut d = Diagnostic::error(
                    span_of(elem),
                    format!("Property {cname}::${prop} has no type specified."),
                )
                .with_code("missingType.property");
                // `--fix`: a `@var` from the default value + the own-class
                // `$this->prop = …` assignment evidence (private props only),
                // else restate an overridden ancestor property's declared type.
                if fa.collect_fixes && pd.props.len() == 1 && elem.hooks.is_none() {
                    if let Some(fix) =
                        crate::fix::infer_property_type(fa, scope, fqn, class, pd, elem)
                            .or_else(|| {
                                crate::fix::inherited_property_type(fa, scope, fqn, class, pd, elem)
                            })
                            .and_then(|ty| {
                                crate::fix::typed_tag_fix(
                                    fa,
                                    scope,
                                    &ty,
                                    crate::fix::first_attr_span(&pd.attrs).unwrap_or(span_of(elem)),
                                    pd.doc.as_deref(),
                                    php_diagnostics::DocTagKind::Var,
                                    None,
                                )
                            })
                    {
                        d = d.with_fix(fix);
                    }
                }
                out.push(d);
            }
        }
    });
    out
}

/// Conservative scan of a raw docblock for an `@var` tag. Any occurrence — even
/// partial — counts as "type specified", to avoid false positives.
fn doc_has_var(doc: Option<&str>) -> bool {
    php_phpdoc::query::has_var_conservative(doc)
}

// --- registry --------------------------------------------------------------

// ---------------------------------------------------------------------------
// TypesAssignedToPropertiesRule — assign.propertyType
// ---------------------------------------------------------------------------

/// `$obj->prop = $value` where `$value`'s type is not assignable to the
/// property's declared type. Uses `fa.type_of` + `find_property` + `is_assignable`
/// (lenient: mixed/unknown never flag), gated on `class_fully_known`.
fn run_types_assigned_to_properties(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Assign { target, rhs } = &e.kind else {
            return;
        };
        let ExprKind::Prop {
            base,
            name: MemberName::Ident(psym),
            ..
        } = &target.kind
        else {
            return;
        };
        let recv = fa.type_of(base);
        let Some(fqn) = sole_class(&recv) else { return };
        if !fa.class_fully_known(&fqn) {
            return;
        }
        let pname = fa.interner.resolve(*psym);
        let Some(found) = fa
            .reflection
            .find_property_on_type(&recv, pname)
            .or_else(|| fa.reflection.find_property(&fqn, pname))
        else {
            return;
        };
        let decl = found.member.ty.clone();
        let native_decl = found.member.native_ty.clone();
        let val = fa.type_of(rhs);
        let native_val = fa.native_type_of(rhs);
        if compat::value_mismatch(fa, &val, Some(&native_val), &decl, &native_decl) {
            out.push(
                Diagnostic::error(
                    rhs.span,
                    format!("Property {fqn}::${pname} ({decl}) does not accept {val}."),
                )
                .with_code("assign.propertyType"),
            );
        }
    });
    out
}

// ---------------------------------------------------------------------------
// DefaultValueTypesAssignedToPropertiesRule — property.defaultValue
// ---------------------------------------------------------------------------

/// A property default value must be accepted by the property's writable type.
/// Mirrors phpstan's `DefaultValueTypesAssignedToPropertiesRule`: if a property
/// has no native type, `= null` is allowed even when PHPDoc says otherwise.
fn run_default_value_types_assigned_to_properties(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            check_property_defaults_stmt(fa, scope, st, &mut out);
        }
    });
    out
}

fn check_property_defaults_stmt(
    fa: &FileAnalysis,
    scope: &Scope,
    st: &Stmt,
    out: &mut Vec<Diagnostic>,
) {
    match &st.kind {
        StmtKind::Class(c) => {
            let fqn = c
                .name
                .map(|n| scope.qualify(fa.interner.resolve(n)))
                .unwrap_or_else(|| "class@anonymous".to_string());
            let class = fa.reflect_class(scope, &fqn, c);
            let ctx = TypeCtx::new(fa.reflection, scope, fa.interner);
            let mut native_ctx = TypeCtx::new(fa.reflection, scope, fa.interner);
            native_ctx.native = true;
            for m in &c.members {
                let Member::Property(pd) = m else { continue };
                for elem in &pd.props {
                    let Some(default) = &elem.default else {
                        continue;
                    };
                    let pname = fa.interner.resolve(elem.name);
                    let Some(prop) = class.properties.iter().find(|p| p.name == pname) else {
                        continue;
                    };
                    let value = ctx.infer(default);
                    if pd.ty.is_none() && matches!(value, Type::Null) {
                        continue;
                    }
                    if is_empty_array_expr(default) && is_array_or_iterable_type(&prop.ty) {
                        continue;
                    }
                    let native_value = native_ctx.infer(default);
                    if !compat::value_mismatch(
                        fa,
                        &value,
                        Some(&native_value),
                        &prop.ty,
                        &prop.native_ty,
                    ) {
                        continue;
                    }
                    let kind = if prop.is_static {
                        "Static property"
                    } else {
                        "Property"
                    };
                    out.push(
                        Diagnostic::error(
                            default.span,
                            format!(
                                "{kind} {}::${pname} ({}) does not accept default value of type {value}.",
                                fqn.trim_start_matches('\\'),
                                prop.ty
                            ),
                        )
                        .with_code("property.defaultValue"),
                    );
                }
            }
        }
        StmtKind::Namespace { body: Some(b), .. } | StmtKind::Block(b) => {
            b.iter()
                .for_each(|s| check_property_defaults_stmt(fa, scope, s, out));
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            check_property_defaults_stmt(fa, scope, then, out);
            for e in elseifs {
                check_property_defaults_stmt(fa, scope, &e.body, out);
            }
            if let Some(e) = els {
                check_property_defaults_stmt(fa, scope, e, out);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => check_property_defaults_stmt(fa, scope, body, out),
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            body.iter()
                .for_each(|s| check_property_defaults_stmt(fa, scope, s, out));
            for c in catches {
                c.body
                    .iter()
                    .for_each(|s| check_property_defaults_stmt(fa, scope, s, out));
            }
            if let Some(fin) = finally {
                fin.iter()
                    .for_each(|s| check_property_defaults_stmt(fa, scope, s, out));
            }
        }
        StmtKind::Switch { cases, .. } => {
            for case in cases {
                case.body
                    .iter()
                    .for_each(|s| check_property_defaults_stmt(fa, scope, s, out));
            }
        }
        StmtKind::Declare { body: Some(b), .. } => check_property_defaults_stmt(fa, scope, b, out),
        StmtKind::Function(fd) => {
            fd.body
                .iter()
                .for_each(|s| check_property_defaults_stmt(fa, scope, s, out));
        }
        _ => {}
    }
}

fn is_empty_array_expr(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Array { items, .. } if items.is_empty())
}

fn is_array_or_iterable_type(t: &Type) -> bool {
    match t {
        Type::Array(_) | Type::Iterable(_) | Type::List(_) | Type::Shape { .. } => true,
        Type::Nullable(inner) => is_array_or_iterable_type(inner),
        _ => false,
    }
}

pub(crate) static RULES: &[RuleEntry] = &[
    // Gated on `checkUninitializedProperties` (off by default); registered at
    // level 0 so the config flag — not level — controls it.
    RuleEntry {
        name: "property.uninitialized",
        level: 0,
        run: run_uninitialized_properties,
    },
    RuleEntry {
        name: "property.readOnly",
        level: 0,
        run: run_readonly_property,
    },
    RuleEntry {
        name: "property.readOnlyByPhpDocDefaultValue",
        level: 0,
        run: run_readonly_phpdoc_property,
    },
    RuleEntry {
        name: "property.inClass",
        level: 0,
        run: run_property_in_class,
    },
    RuleEntry {
        name: "property.inInterface",
        level: 0,
        run: run_properties_in_interface,
    },
    RuleEntry {
        name: "property.hookAttributes",
        level: 0,
        run: run_property_hook_attributes,
    },
    RuleEntry {
        name: "propertySetHook.parameter",
        level: 0,
        run: run_set_property_hook_parameter,
    },
    RuleEntry {
        name: "propertyGetHook.noRead",
        level: 3,
        run: run_get_non_virtual_property_hook_read,
    },
    RuleEntry {
        name: "propertySetHook.noAssign",
        level: 3,
        run: run_set_non_virtual_property_hook_assign,
    },
    RuleEntry {
        name: "property.overriding",
        level: 0,
        run: run_overriding_property,
    },
    RuleEntry {
        name: "property.accessUndefined",
        level: 0,
        run: run_access_properties,
    },
    RuleEntry {
        name: "property.readOnlyAssign",
        level: 3,
        run: run_readonly_property_assign,
    },
    RuleEntry {
        name: "property.missingReadOnlyAssign",
        level: 0,
        run: run_missing_readonly_property_assign,
    },
    RuleEntry {
        name: "property.readOnlyAssignByRef",
        level: 3,
        run: run_readonly_property_assign_ref,
    },
    RuleEntry {
        name: "property.assignByRef",
        level: 0,
        run: run_property_assign_ref,
    },
    RuleEntry {
        name: "property.readOnlyByPhpDocAssign",
        level: 3,
        run: run_readonly_phpdoc_property_assign,
    },
    RuleEntry {
        name: "property.missingReadOnlyByPhpDocAssign",
        level: 0,
        run: run_missing_readonly_phpdoc_property_assign,
    },
    RuleEntry {
        name: "property.readOnlyByPhpDocAssignByRef",
        level: 3,
        run: run_readonly_phpdoc_property_assign_ref,
    },
    RuleEntry {
        name: "property.access",
        level: 0,
        run: run_access_properties_general,
    },
    RuleEntry {
        name: "property.nullableAccess",
        level: 8,
        run: run_nullable_property_access,
    },
    RuleEntry {
        name: "property.unionAccess",
        level: 7,
        run: run_union_property_access,
    },
    RuleEntry {
        name: "property.accessInAssign",
        level: 0,
        run: run_access_properties_in_assign,
    },
    RuleEntry {
        name: "property.unionAccessInAssign",
        level: 7,
        run: run_union_property_access_in_assign,
    },
    RuleEntry {
        name: "staticProperty.access",
        level: 0,
        run: run_access_static_properties,
    },
    RuleEntry {
        name: "staticProperty.accessInAssign",
        level: 0,
        run: run_access_static_properties_in_assign,
    },
    RuleEntry {
        name: "staticClassAccess.privateProperty",
        level: 2,
        run: run_access_private_property_through_static,
    },
    RuleEntry {
        name: "property.nullsafeNeverNull",
        level: 4,
        run: run_nullsafe_property_fetch,
    },
    RuleEntry {
        name: "property.readingWriteOnly",
        level: 0,
        run: run_reading_write_only,
    },
    RuleEntry {
        name: "property.writingToReadOnly",
        level: 0,
        run: run_writing_to_read_only,
    },
    RuleEntry {
        name: "property.callableType",
        level: 0,
        run: run_invalid_callable_property_type,
    },
    RuleEntry {
        name: "property.missingType",
        level: 6,
        run: run_missing_property_typehint,
    },
    RuleEntry {
        name: "assign.propertyType",
        level: 3,
        run: run_types_assigned_to_properties,
    },
    RuleEntry {
        name: "property.defaultValue",
        level: 3,
        run: run_default_value_types_assigned_to_properties,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{codes, codes_with, fixes, run, run_fixes};

    // --- UninitializedPropertyRule (property.uninitialized) -------------

    #[test]
    fn uninitialized_typed_property_without_constructor_is_flagged() {
        let src = r#"<?php
            class C {
                public int $x;
            }"#;
        assert_eq!(
            codes(src, run_uninitialized_properties),
            ["property.uninitialized"]
        );
    }

    #[test]
    fn uninitialized_property_message_matches_phpstan() {
        let src = r#"<?php
            namespace App;
            class Widget {
                public int $size;
            }"#;
        let diags = run(src, run_uninitialized_properties);
        assert_eq!(
            diags[0].message,
            "Class App\\Widget has an uninitialized property $size. Give it default value or assign it in the constructor."
        );
    }

    #[test]
    fn property_assigned_in_constructor_is_clean() {
        let src = r#"<?php
            class C {
                public int $x;
                public function __construct() { $this->x = 1; }
            }"#;
        assert!(codes(src, run_uninitialized_properties).is_empty());
    }

    #[test]
    fn property_not_assigned_in_constructor_is_flagged() {
        let src = r#"<?php
            class C {
                public int $x;
                public int $y;
                public function __construct() { $this->x = 1; }
            }"#;
        assert_eq!(
            codes(src, run_uninitialized_properties),
            ["property.uninitialized"]
        );
    }

    #[test]
    fn property_with_default_or_readonly_or_nullable_default_is_clean() {
        let src = r#"<?php
            class C {
                public int $withDefault = 0;
                public readonly int $ro;
                public ?int $nullableDefault = null;
                public function __construct(public int $promoted) {}
            }"#;
        assert!(codes(src, run_uninitialized_properties).is_empty());
    }

    #[test]
    fn class_with_parent_or_trait_is_skipped_conservatively() {
        let parent = r#"<?php
            class Base {}
            class C extends Base {
                public int $x;
            }"#;
        assert!(codes(parent, run_uninitialized_properties).is_empty());

        let traituse = r#"<?php
            trait T {}
            class C {
                use T;
                public int $x;
            }"#;
        assert!(codes(traituse, run_uninitialized_properties).is_empty());
    }

    #[test]
    fn property_assigned_in_any_method_is_clean() {
        // Conservative: assignment in a non-constructor method also counts as
        // initialized (under-reports vs phpstan, never false-positives).
        let src = r#"<?php
            class C {
                public int $x;
                public function init(): void { $this->x = 1; }
            }"#;
        assert!(codes(src, run_uninitialized_properties).is_empty());
    }

    #[test]
    fn dynamic_this_write_bails_the_class() {
        let src = r#"<?php
            class C {
                public int $x;
                public function __construct(string $k) { $this->$k = 1; }
            }"#;
        assert!(codes(src, run_uninitialized_properties).is_empty());
    }

    #[test]
    fn property_passed_by_possible_ref_bails() {
        let src = r#"<?php
            class C {
                public int $x;
                public function __construct() { settype($this->x, 'integer'); }
            }"#;
        assert!(codes(src, run_uninitialized_properties).is_empty());
    }

    #[test]
    fn uninitialized_rule_off_by_default_flag() {
        let src = r#"<?php
            class C { public int $x; }"#;
        // With the gate disabled the rule stays silent.
        assert!(codes_with(src, run_uninitialized_properties, |fa| {
            fa.check_uninitialized_properties = false;
        })
        .is_empty());
    }

    // --- ReadOnlyByPhpDocPropertyRule -----------------------------------

    #[test]
    fn readonly_phpdoc_property_with_default_flagged() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public int $x = 5;
            }"#;
        assert_eq!(
            codes(src, run_readonly_phpdoc_property),
            ["property.readOnlyByPhpDocDefaultValue"]
        );
    }

    #[test]
    fn readonly_phpdoc_property_without_default_ok() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public int $x;
            }"#;
        assert!(codes(src, run_readonly_phpdoc_property).is_empty());
    }

    #[test]
    fn native_readonly_with_default_not_this_rule() {
        // Native `readonly` + default is property.readOnlyDefaultValue, not this rule.
        let src = r#"<?php
            class C {
                public readonly int $x;
            }"#;
        assert!(codes(src, run_readonly_phpdoc_property).is_empty());
    }

    #[test]
    fn plain_property_with_default_ok() {
        let src = r#"<?php class C { public int $x = 5; }"#;
        assert!(codes(src, run_readonly_phpdoc_property).is_empty());
    }

    #[test]
    fn allow_private_mutation_opt_out() {
        let src = r#"<?php
            class C {
                /**
                 * @readonly
                 * @psalm-allow-private-mutation
                 */
                public int $x = 5;
            }"#;
        assert!(codes(src, run_readonly_phpdoc_property).is_empty());
    }

    #[test]
    fn readonly_allow_private_mutation_combined_tag_opt_out() {
        let src = r#"<?php
            class C {
                /** @phpstan-readonly-allow-private-mutation */
                public int $x = 5;
            }"#;
        assert!(codes(src, run_readonly_phpdoc_property).is_empty());
    }

    // --- TypesAssignedToPropertiesRule ----------------------------------

    #[test]
    fn wrong_typed_property_assignment_flagged() {
        let src = "<?php class C { public int $n; function f() { $this->n = 'x'; } }";
        assert_eq!(
            codes(src, run_types_assigned_to_properties),
            ["assign.propertyType"]
        );
    }

    #[test]
    fn correct_typed_property_assignment_clean() {
        let src = "<?php class C { public int $n; function f() { $this->n = 5; } }";
        assert!(codes(src, run_types_assigned_to_properties).is_empty());
    }

    #[test]
    fn untyped_property_assignment_clean() {
        let src = "<?php class C { public $n; function f() { $this->n = 'x'; } }";
        assert!(codes(src, run_types_assigned_to_properties).is_empty());
    }

    #[test]
    fn mixed_value_to_typed_property_clean() {
        let src = "<?php class C { public int $n; function f($x) { $this->n = $x; } }";
        assert!(codes_with(src, run_types_assigned_to_properties, |fa| {
            fa.check_implicit_mixed = false;
        })
        .is_empty());
    }

    #[test]
    fn maybe_property_assignment_waits_for_report_maybes() {
        let src = r#"<?php
            class C { public int $n; }
            /** @param int|string $x */
            function f(C $c, $x) { $c->n = $x; }
        "#;
        assert!(codes_with(src, run_types_assigned_to_properties, |fa| {
            fa.report_maybes = false;
        })
        .is_empty());
        assert_eq!(
            codes(src, run_types_assigned_to_properties),
            ["assign.propertyType"]
        );
    }

    #[test]
    fn nullable_property_assignment_waits_for_check_nullables() {
        let src = r#"<?php
            class C { public int $n; }
            /** @param int|null $x */
            function f(C $c, $x) { $c->n = $x; }
        "#;
        assert!(codes_with(src, run_types_assigned_to_properties, |fa| {
            fa.check_nullables = false;
        })
        .is_empty());
        assert_eq!(
            codes(src, run_types_assigned_to_properties),
            ["assign.propertyType"]
        );
    }

    #[test]
    fn explicit_mixed_property_assignment_waits_for_level_9() {
        let src = "<?php class C { public int $n; function f(mixed $x) { $this->n = $x; } }";
        assert!(codes_with(src, run_types_assigned_to_properties, |fa| {
            fa.check_explicit_mixed = false;
            fa.check_implicit_mixed = false;
        })
        .is_empty());
        assert_eq!(
            codes_with(src, run_types_assigned_to_properties, |fa| {
                fa.check_implicit_mixed = false;
            }),
            ["assign.propertyType"]
        );
    }

    #[test]
    fn implicit_mixed_property_assignment_waits_for_max() {
        let src = "<?php class C { public int $n; function f($x) { $this->n = $x; } }";
        assert!(codes_with(src, run_types_assigned_to_properties, |fa| {
            fa.check_implicit_mixed = false;
        })
        .is_empty());
        assert_eq!(
            codes(src, run_types_assigned_to_properties),
            ["assign.propertyType"]
        );
    }

    #[test]
    fn phpdoc_uncertain_suppresses_phpdoc_only_property_assignment() {
        let src = r#"<?php
            class C { public int $n; }
            /** @param string $x */
            function f(C $c, $x) { $c->n = $x; }
        "#;
        assert_eq!(
            codes(src, run_types_assigned_to_properties),
            ["assign.propertyType"]
        );
        assert!(codes_with(src, run_types_assigned_to_properties, |fa| {
            fa.treat_phpdoc_types_as_certain = false;
            fa.check_implicit_mixed = false;
        })
        .is_empty());
    }

    #[test]
    fn generic_receiver_property_assignment_uses_instantiated_type() {
        let src = r#"<?php
            class User {}
            /** @template T */
            class Box { /** @var T */ public $value; }
            /** @param Box<User> $box */
            function f($box) { $box->value = 'no'; }
        "#;
        assert_eq!(
            codes(src, run_types_assigned_to_properties),
            ["assign.propertyType"]
        );
    }

    #[test]
    fn assignment_on_external_object_flagged() {
        let src = "<?php class C { public int $n; } function f() { $c = new C(); $c->n = 'x'; }";
        assert_eq!(
            codes(src, run_types_assigned_to_properties),
            ["assign.propertyType"]
        );
    }

    // --- DefaultValueTypesAssignedToPropertiesRule ----------------------

    #[test]
    fn wrong_typed_property_default_flagged() {
        let src = "<?php class C { public int $n = 'x'; }";
        assert_eq!(
            codes(src, run_default_value_types_assigned_to_properties),
            ["property.defaultValue"]
        );
    }

    #[test]
    fn correct_typed_property_default_clean() {
        let src = "<?php class C { public int $n = 1; }";
        assert!(codes(src, run_default_value_types_assigned_to_properties).is_empty());
    }

    #[test]
    fn wrong_static_property_default_flagged() {
        let src = "<?php class C { public static string $s = 1; }";
        assert_eq!(
            codes(src, run_default_value_types_assigned_to_properties),
            ["property.defaultValue"]
        );
    }

    #[test]
    fn phpdoc_property_default_is_checked() {
        let src = "<?php class C { /** @var int */ public $n = 'x'; }";
        assert_eq!(
            codes(src, run_default_value_types_assigned_to_properties),
            ["property.defaultValue"]
        );
    }

    #[test]
    fn phpdoc_uncertain_suppresses_phpdoc_only_property_default() {
        let src = "<?php class C { /** @var int */ public $n = 'x'; }";
        assert!(
            codes_with(src, run_default_value_types_assigned_to_properties, |fa| {
                fa.treat_phpdoc_types_as_certain = false;
                fa.check_implicit_mixed = false;
            })
            .is_empty()
        );
    }

    #[test]
    fn untyped_phpdoc_property_default_null_is_clean() {
        let src = "<?php class C { /** @var int */ public $n = null; }";
        assert!(codes(src, run_default_value_types_assigned_to_properties).is_empty());
    }

    // --- ReadOnlyPropertyRule -------------------------------------------

    #[test]
    fn readonly_without_type_is_flagged() {
        let src = "<?php class C { public readonly $x; }";
        assert_eq!(
            codes(src, run_readonly_property),
            ["property.readOnlyNoNativeType"]
        );
    }

    #[test]
    fn readonly_with_type_is_clean() {
        let src = "<?php class C { public readonly int $x; }";
        assert!(codes(src, run_readonly_property).is_empty());
    }

    #[test]
    fn readonly_static_is_flagged() {
        let src = "<?php class C { public static readonly int $x; }";
        assert_eq!(
            codes(src, run_readonly_property),
            ["property.readOnlyStatic"]
        );
    }

    #[test]
    fn readonly_with_default_is_flagged() {
        let src = "<?php class C { public readonly int $x = 1; }";
        assert_eq!(
            codes(src, run_readonly_property),
            ["property.readOnlyDefaultValue"]
        );
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
        assert_eq!(
            codes(src, run_property_in_class),
            ["property.abstractNonHooked"]
        );
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
        assert_eq!(
            codes(src, run_properties_in_interface),
            ["property.nonHookedInInterface"]
        );
    }

    #[test]
    fn hooked_public_property_in_interface_is_clean() {
        let src = "<?php interface I { public int $x { get; } }";
        assert!(codes(src, run_properties_in_interface).is_empty());
    }

    #[test]
    fn non_public_hooked_property_in_interface_is_flagged() {
        let src = "<?php interface I { protected int $x { get; } }";
        assert_eq!(
            codes(src, run_properties_in_interface),
            ["property.nonPublicInInterface"]
        );
    }

    #[test]
    fn hook_with_body_in_interface_is_flagged() {
        let src = "<?php interface I { public int $x { get => 1; } }";
        assert_eq!(
            codes(src, run_properties_in_interface),
            ["property.hookBodyInInterface"]
        );
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
        assert_eq!(
            codes(src, run_property_hook_attributes),
            ["attribute.target"]
        );
    }

    #[test]
    fn other_attr_on_hook_is_clean() {
        let src = "<?php class C { public int $x { #[Other] get => 1; } }";
        assert!(codes(src, run_property_hook_attributes).is_empty());
    }

    // --- SetPropertyHookParameterRule -----------------------------------

    #[test]
    fn set_hook_param_without_native_type_for_typed_property_is_flagged() {
        let src = "<?php class C { public int $x { set($v) {} } }";
        assert_eq!(
            codes(src, run_set_property_hook_parameter),
            ["propertySetHook.nativeParameterType"]
        );
    }

    #[test]
    fn set_hook_param_native_type_for_untyped_property_is_flagged() {
        let src = "<?php class C { public $x { set(int $v) {} } }";
        assert_eq!(
            codes(src, run_set_property_hook_parameter),
            ["propertySetHook.nativeParameterType"]
        );
    }

    #[test]
    fn set_hook_param_native_type_must_be_contravariant() {
        let src = "<?php class C { public int|float $x { set(int $v) {} } }";
        assert_eq!(
            codes(src, run_set_property_hook_parameter),
            ["propertySetHook.nativeParameterType"]
        );
    }

    #[test]
    fn set_hook_param_native_supertype_is_clean() {
        let src = "<?php class C { public int $x { set(int|float $v) {} } }";
        assert!(codes(src, run_set_property_hook_parameter).is_empty());
    }

    #[test]
    fn implicit_set_hook_param_is_clean() {
        let src = "<?php class C { public int $x { set { $this->x = $value; } } }";
        assert!(codes(src, run_set_property_hook_parameter).is_empty());
    }

    #[test]
    fn set_hook_param_type_checks_phpdoc_certain_property_type() {
        let src = r#"<?php
            class C {
                /** @var string */
                public mixed $x { set(int $v) {} }
            }"#;
        assert_eq!(
            codes(src, run_set_property_hook_parameter),
            ["propertySetHook.parameterType"]
        );
    }

    #[test]
    fn set_hook_param_type_skips_phpdoc_that_is_not_native_refinement() {
        let src = r#"<?php
            class C {
                /** @var string */
                public int $x { set(int $v) {} }
            }"#;
        assert!(codes(src, run_set_property_hook_parameter).is_empty());
    }

    #[test]
    fn set_hook_param_bare_array_reports_missing_iterable_value() {
        let src = "<?php class C { public mixed $x { set(array $v) {} } }";
        assert_eq!(
            codes(src, run_set_property_hook_parameter),
            ["missingType.iterableValue"]
        );
    }

    #[test]
    fn set_hook_param_bare_callable_reports_missing_signature() {
        let src = "<?php class C { public mixed $x { set(callable $cb) {} } }";
        assert_eq!(
            codes(src, run_set_property_hook_parameter),
            ["missingType.callable"]
        );
    }

    #[test]
    fn set_hook_param_generic_class_without_args_is_flagged() {
        let src = r#"<?php
            /** @template T */
            class Box {}
            class C {
                public mixed $x { set(Box $box) {} }
            }"#;
        assert_eq!(
            codes(src, run_set_property_hook_parameter),
            ["missingType.generics"]
        );
    }

    // --- GetNonVirtualPropertyHookReadRule ------------------------------

    #[test]
    fn get_hook_for_backed_property_without_read_is_flagged() {
        let src = "<?php class C { public int $k { get => 1; set => $value + 1; } }";
        assert_eq!(
            codes(src, run_get_non_virtual_property_hook_read),
            ["propertyGetHook.noRead"]
        );
    }

    #[test]
    fn get_hook_that_reads_backing_value_is_clean() {
        let src = "<?php class C { public int $k { get => $this->k + 1; set => $value + 1; } }";
        assert!(codes(src, run_get_non_virtual_property_hook_read).is_empty());
    }

    #[test]
    fn virtual_get_hook_without_read_is_clean() {
        let src = "<?php class C { public int $j; public int $k { get => 1; set { $this->j = $value; } } }";
        assert!(codes(src, run_get_non_virtual_property_hook_read).is_empty());
    }

    // --- SetNonVirtualPropertyHookAssignRule ----------------------------

    #[test]
    fn set_hook_for_backed_property_without_assign_is_flagged() {
        let src = "<?php class C { public int $j; public int $k { get { return $this->k + 1; } set { $this->j = $value; } } }";
        assert_eq!(
            codes(src, run_set_non_virtual_property_hook_assign),
            ["propertySetHook.noAssign"]
        );
    }

    #[test]
    fn set_hook_that_assigns_backing_value_is_clean() {
        let src = "<?php class C { public int $k { get { return $this->k + 1; } set { $this->k = $value; } } }";
        assert!(codes(src, run_set_non_virtual_property_hook_assign).is_empty());
    }

    #[test]
    fn short_set_hook_is_clean() {
        let src = "<?php class C { public int $k { get { return $this->k + 1; } set => $value; } }";
        assert!(codes(src, run_set_non_virtual_property_hook_assign).is_empty());
    }

    // --- OverridingPropertyRule -----------------------------------------

    #[test]
    fn override_static_with_nonstatic_is_flagged() {
        let src =
            "<?php class B { public static int $x = 0; } class C extends B { public int $x = 0; }";
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
        let src =
            "<?php class B { public int $x = 0; } class C extends B { protected int $x = 0; }";
        let got = codes(src, run_overriding_property);
        assert!(got.contains(&"property.visibility"), "{got:?}");
    }

    #[test]
    fn override_missing_attribute_is_flagged() {
        // `#[\Override]` on properties is a PHP 8.5+ feature, so the rule only
        // fires when the target version supports it.
        let src = "<?php class B { public int $x = 0; } class C extends B { public int $x = 0; }";
        let got = crate::testutil::codes_version(
            src,
            run_overriding_property,
            crate::PhpVersion::parse("8.5").unwrap(),
        );
        assert!(got.contains(&"property.missingOverride"), "{got:?}");
    }

    #[test]
    fn override_missing_attribute_below_85_is_clean() {
        // Default target (8.4) must NOT report it.
        let src = "<?php class B { public int $x = 0; } class C extends B { public int $x = 0; }";
        let got = codes(src, run_overriding_property);
        assert!(!got.contains(&"property.missingOverride"), "{got:?}");
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

    #[test]
    fn override_missing_native_property_type_is_flagged() {
        let src = "<?php class B { public int $x = 0; } class C extends B { public $x; }";
        assert!(codes(src, run_overriding_property).contains(&"property.missingNativeType"));
    }

    #[test]
    fn override_extra_native_property_type_is_flagged() {
        let src = "<?php class B { public $x; } class C extends B { public int $x = 0; }";
        assert!(codes(src, run_overriding_property).contains(&"property.extraNativeType"));
    }

    #[test]
    fn override_incompatible_native_property_type_is_flagged() {
        let src =
            "<?php class B { public int $x = 0; } class C extends B { public string $x = ''; }";
        assert!(codes(src, run_overriding_property).contains(&"property.nativeType"));
    }

    #[test]
    fn maybe_property_native_override_waits_for_report_maybes() {
        let src =
            "<?php class B { public int|string $x = 0; } class C extends B { public int $x = 0; }";
        assert!(codes_with(src, run_overriding_property, |fa| {
            fa.report_maybes = false;
        })
        .is_empty());
        assert!(codes(src, run_overriding_property).contains(&"property.nativeType"));
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

    #[test]
    fn undefined_property_inside_array_callback_is_flagged() {
        let src = r#"<?php
            class User {}
            /** @param list<User> $users */
            function f(array $users): void {
                array_map(fn($u) => $u->missing, $users);
            }
        "#;
        assert_eq!(
            codes(src, run_access_properties_general),
            ["property.notFound"]
        );
    }

    #[test]
    fn undefined_property_inside_arrayobject_foreach_is_flagged() {
        let src = r#"<?php
            class User {}
            /** @param \ArrayObject<int, User> $users */
            function f(\ArrayObject $users): void {
                foreach ($users as $u) {
                    $u->missing;
                }
            }
        "#;
        assert_eq!(
            codes(src, run_access_properties_general),
            ["property.notFound"]
        );
    }

    #[test]
    fn undefined_property_inside_iteratoraggregate_foreach_is_flagged() {
        let src = r#"<?php
            class User {}
            /** @implements \IteratorAggregate<string, User> */
            class Users implements \IteratorAggregate {}
            function f(Users $users): void {
                foreach ($users as $u) {
                    $u->missing;
                }
            }
        "#;
        assert_eq!(
            codes(src, run_access_properties_general),
            ["property.notFound"]
        );
    }

    #[test]
    fn undefined_property_inside_aliased_array_callback_is_flagged() {
        let src = r#"<?php
            class User {}
            /** @param list<User> $users */
            function f(array $users): void {
                $cb = fn($u) => $u->missing;
                array_map($cb, $users);
            }
        "#;
        assert_eq!(
            codes(src, run_access_properties_general),
            ["property.notFound"]
        );
    }

    #[test]
    fn undefined_property_inside_collection_map_callback_is_flagged() {
        let src = r#"<?php
            class User {}
            /** @template T */
            class Collection {
                public function map(callable $callback) {}
            }
            /** @param Collection<User> $users */
            function f(Collection $users): void {
                $users->map(fn($u) => $u->missing);
            }
        "#;
        assert_eq!(
            codes(src, run_access_properties_general),
            ["property.notFound"]
        );
    }

    #[test]
    fn undefined_property_on_userland_generic_result_is_flagged() {
        let src = r#"<?php
            class User {}
            /**
             * @template T
             * @param T $x
             * @return T
             */
            function id($x) {}
            function f(User $u): void {
                id($u)->missing;
            }
        "#;
        assert_eq!(
            codes(src, run_access_properties_general),
            ["property.notFound"]
        );
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

    #[test]
    fn readonly_assign_in_unserialize_is_clean() {
        let src =
            "<?php class C { public readonly int $x; function __unserialize(array $d) { $this->x = 1; } }";
        assert!(codes(src, run_readonly_property_assign).is_empty());
    }

    #[test]
    fn readonly_assign_in_clone_is_clean() {
        let src = "<?php class C { public readonly int $x; function __clone() { $this->x = 1; } }";
        assert!(codes(src, run_readonly_property_assign).is_empty());
    }

    // --- MissingReadOnlyPropertyAssignRule --------------------------------

    #[test]
    fn missing_readonly_without_constructor_is_flagged() {
        let src = "<?php class C { public readonly int $x; }";
        assert_eq!(
            codes(src, run_missing_readonly_property_assign),
            ["property.uninitializedReadonly"]
        );
    }

    #[test]
    fn missing_readonly_not_assigned_in_ctor_is_flagged() {
        let src = "<?php class C { public readonly int $x; function __construct() {} }";
        assert_eq!(
            codes(src, run_missing_readonly_property_assign),
            ["property.uninitializedReadonly"]
        );
    }

    #[test]
    fn missing_readonly_assigned_in_ctor_is_clean() {
        let src =
            "<?php class C { public readonly int $x; function __construct() { $this->x = 1; } }";
        assert!(codes(src, run_missing_readonly_property_assign).is_empty());
    }

    #[test]
    fn missing_readonly_read_before_assign_in_ctor_is_flagged() {
        let src = "<?php class C { public readonly int $x; function __construct() { echo $this->x; $this->x = 1; } }";
        assert_eq!(
            codes(src, run_missing_readonly_property_assign),
            ["property.uninitializedReadonly"]
        );
    }

    #[test]
    fn missing_readonly_double_assign_in_ctor_is_flagged() {
        let src = "<?php class C { public readonly int $x; function __construct() { $this->x = 1; $this->x = 2; } }";
        assert_eq!(
            codes(src, run_missing_readonly_property_assign),
            ["assign.readOnlyProperty"]
        );
    }

    #[test]
    fn missing_readonly_helper_call_in_ctor_is_skipped() {
        let src = "<?php class C { public readonly int $x; function __construct() { $this->init(); } function init() { $this->x = 1; } }";
        assert!(codes(src, run_missing_readonly_property_assign).is_empty());
    }

    #[test]
    fn missing_readonly_branchy_ctor_is_skipped() {
        let src = "<?php class C { public readonly int $x; function __construct(bool $ok) { if ($ok) { $this->x = 1; } } }";
        assert!(codes(src, run_missing_readonly_property_assign).is_empty());
    }

    #[test]
    fn missing_readonly_nested_conditional_assignment_is_skipped() {
        let src = "<?php class C { public readonly int $x; function __construct(bool $ok) { $ok && ($this->x = 1); } }";
        assert!(codes(src, run_missing_readonly_property_assign).is_empty());
    }

    #[test]
    fn missing_readonly_offset_write_is_skipped() {
        let src = "<?php class C { public readonly array $x; function __construct() { $this->x[0] = 1; } }";
        assert!(codes(src, run_missing_readonly_property_assign).is_empty());
    }

    // --- ReadOnlyPropertyAssignRefRule ----------------------------------

    #[test]
    fn readonly_assign_ref_on_this_is_flagged() {
        let src = "<?php class C { public readonly int $x; function f() { $r = &$this->x; } }";
        assert_eq!(
            codes(src, run_readonly_property_assign_ref),
            ["property.readOnlyAssignByRef"]
        );
    }

    #[test]
    fn readonly_assign_ref_is_not_reported_as_plain_assign() {
        let src = "<?php class C { public readonly int $x; function f() { $r = &$this->x; } }";
        assert!(codes(src, run_readonly_property_assign).is_empty());
    }

    #[test]
    fn non_readonly_assign_ref_is_clean() {
        let src = "<?php class C { public int $x; function f() { $r = &$this->x; } }";
        assert!(codes(src, run_readonly_property_assign_ref).is_empty());
    }

    // --- PropertyAssignRefRule ------------------------------------------

    #[test]
    fn assign_ref_to_private_property_is_flagged() {
        let src = "<?php class C { private int $x; } function f(C $c) { $r = &$c->x; }";
        assert_eq!(
            codes(src, run_property_assign_ref),
            ["property.assignByRef"]
        );
    }

    #[test]
    fn assign_ref_to_private_property_on_this_is_clean() {
        let src = "<?php class C { private int $x; function f() { $r = &$this->x; } }";
        assert!(codes(src, run_property_assign_ref).is_empty());
    }

    #[test]
    fn assign_ref_to_protected_set_property_is_flagged() {
        let src =
            "<?php class C { public protected(set) int $x; } function f(C $c) { $r = &$c->x; }";
        assert_eq!(
            codes(src, run_property_assign_ref),
            ["property.assignByRef"]
        );
    }

    // --- ReadOnlyByPhpDocPropertyAssignRule -----------------------------

    #[test]
    fn readonly_phpdoc_assign_outside_ctor_is_flagged() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public int $x;
                function f() { $this->x = 1; }
            }"#;
        assert_eq!(
            codes(src, run_readonly_phpdoc_property_assign),
            ["property.readOnlyByPhpDocAssignNotInConstructor"]
        );
    }

    #[test]
    fn readonly_phpdoc_assign_in_ctor_on_this_is_clean() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public int $x;
                function __construct() { $this->x = 1; }
            }"#;
        assert!(codes(src, run_readonly_phpdoc_property_assign).is_empty());
    }

    #[test]
    fn readonly_phpdoc_assign_in_ctor_not_on_this_is_flagged() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public int $x;
                function __construct(C $c) { $c->x = 1; }
            }"#;
        assert_eq!(
            codes(src, run_readonly_phpdoc_property_assign),
            ["property.readOnlyByPhpDocAssignNotOnThis"]
        );
    }

    #[test]
    fn readonly_phpdoc_assign_outside_declaring_class_is_flagged() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public int $x;
            }
            function f(C $c) { $c->x = 1; }"#;
        assert_eq!(
            codes(src, run_readonly_phpdoc_property_assign),
            ["property.readOnlyByPhpDocAssignOutOfClass"]
        );
    }

    #[test]
    fn readonly_phpdoc_allow_private_mutation_allows_in_class_assign() {
        let src = r#"<?php
            class C {
                /** @phpstan-readonly-allow-private-mutation */
                public int $x;
                function f() { $this->x = 1; }
            }"#;
        assert!(codes(src, run_readonly_phpdoc_property_assign).is_empty());
    }

    // --- MissingReadOnlyByPhpDocPropertyAssignRule -----------------------

    #[test]
    fn missing_readonly_phpdoc_without_constructor_is_flagged() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public int $x;
            }"#;
        assert_eq!(
            codes(src, run_missing_readonly_phpdoc_property_assign),
            ["property.uninitializedReadonlyByPhpDoc"]
        );
    }

    #[test]
    fn missing_readonly_phpdoc_not_assigned_in_ctor_is_flagged() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public int $x;
                function __construct() {}
            }"#;
        assert_eq!(
            codes(src, run_missing_readonly_phpdoc_property_assign),
            ["property.uninitializedReadonlyByPhpDoc"]
        );
    }

    #[test]
    fn missing_readonly_phpdoc_assigned_in_ctor_is_clean() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public int $x;
                function __construct() { $this->x = 1; }
            }"#;
        assert!(codes(src, run_missing_readonly_phpdoc_property_assign).is_empty());
    }

    #[test]
    fn missing_readonly_phpdoc_read_before_assign_in_ctor_is_flagged() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public int $x;
                function __construct() { echo $this->x; $this->x = 1; }
            }"#;
        assert_eq!(
            codes(src, run_missing_readonly_phpdoc_property_assign),
            ["property.uninitializedReadonlyByPhpDoc"]
        );
    }

    #[test]
    fn missing_readonly_phpdoc_double_assign_in_ctor_is_flagged() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public int $x;
                function __construct() { $this->x = 1; $this->x = 2; }
            }"#;
        assert_eq!(
            codes(src, run_missing_readonly_phpdoc_property_assign),
            ["assign.readOnlyPropertyByPhpDoc"]
        );
    }

    #[test]
    fn missing_readonly_phpdoc_native_readonly_is_skipped() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public readonly int $x;
                function __construct() {}
            }"#;
        assert!(codes(src, run_missing_readonly_phpdoc_property_assign).is_empty());
    }

    #[test]
    fn missing_readonly_phpdoc_helper_call_in_ctor_is_skipped() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public int $x;
                function __construct() { $this->init(); }
                function init() { $this->x = 1; }
            }"#;
        assert!(codes(src, run_missing_readonly_phpdoc_property_assign).is_empty());
    }

    // --- ReadOnlyByPhpDocPropertyAssignRefRule --------------------------

    #[test]
    fn readonly_phpdoc_assign_ref_is_flagged() {
        let src = r#"<?php
            class C {
                /** @readonly */
                public int $x;
                function f() { $r = &$this->x; }
            }"#;
        assert_eq!(
            codes(src, run_readonly_phpdoc_property_assign_ref),
            ["property.readOnlyByPhpDocAssignByRef"]
        );
    }

    #[test]
    fn native_readonly_assign_ref_not_phpdoc_rule() {
        let src = "<?php class C { public readonly int $x; function f() { $r = &$this->x; } }";
        assert!(codes(src, run_readonly_phpdoc_property_assign_ref).is_empty());
    }

    // --- AccessPrivatePropertyThroughStaticRule -------------------------

    #[test]
    fn private_static_property_through_static_is_flagged() {
        let src = "<?php class C { private static int $x; function f() { return static::$x; } }";
        assert_eq!(
            codes(src, run_access_private_property_through_static),
            ["staticClassAccess.privateProperty"]
        );
    }

    #[test]
    fn private_static_property_through_static_in_final_class_is_clean() {
        let src =
            "<?php final class C { private static int $x; function f() { return static::$x; } }";
        assert!(codes(src, run_access_private_property_through_static).is_empty());
    }

    #[test]
    fn public_static_property_through_static_is_clean() {
        let src = "<?php class C { public static int $x; function f() { return static::$x; } }";
        assert!(codes(src, run_access_private_property_through_static).is_empty());
    }

    // --- AccessPropertiesRule (general receiver) ------------------------

    #[test]
    fn access_undefined_property_on_new_is_flagged() {
        let src = "<?php class C { public int $a; } function f() { return (new C())->b; }";
        assert_eq!(
            codes(src, run_access_properties_general),
            ["property.notFound"]
        );
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
    fn access_arbitrary_property_on_stdclass_is_clean() {
        // stdClass legally carries dynamic properties (json_decode, (object) casts,
        // DB rows) — never report undefined-property access on it.
        let src = "<?php function f(): \\stdClass { return new \\stdClass(); } f()->anything;";
        assert!(codes(src, run_access_properties_general).is_empty());
    }

    #[test]
    fn nullable_property_access_is_flagged_at_strict_level() {
        let src = "<?php class C { public int $a; } function f(?C $c): int { return $c->a; }";
        assert_eq!(
            codes(src, run_nullable_property_access),
            ["property.nonObject"]
        );
    }

    #[test]
    fn nullsafe_property_access_on_nullable_is_clean() {
        let src = "<?php class C { public int $a; } function f(?C $c): mixed { return $c?->a; }";
        assert!(codes(src, run_nullable_property_access).is_empty());
    }

    #[test]
    fn nullable_property_access_in_isset_is_clean() {
        let src =
            "<?php class C { public int $a; } function f(?C $c): bool { return isset($c->a); }";
        assert!(codes(src, run_nullable_property_access).is_empty());
    }

    #[test]
    fn narrowed_nullable_property_access_is_clean() {
        let src = "<?php class C { public int $a; } function f(?C $c): int { if ($c === null) { return 0; } return $c->a; }";
        assert!(codes(src, run_nullable_property_access).is_empty());
    }

    #[test]
    fn nullable_property_access_suppresses_not_found_branch() {
        let src = "<?php class C {} function f(?C $c): mixed { return $c->missing; }";
        assert!(codes(src, run_access_properties_general).is_empty());
    }

    #[test]
    fn union_property_access_missing_on_one_arm_is_flagged() {
        let src = "<?php class A { public int $p; } class B {} \
            /** @param A|B $x */ function f($x): int { return $x->p; }";
        assert_eq!(codes(src, run_union_property_access), ["property.notFound"]);
    }

    #[test]
    fn union_property_access_present_on_all_arms_is_clean() {
        let src = "<?php class A { public int $p; } class B { public int $p; } \
            /** @param A|B $x */ function f($x): int { return $x->p; }";
        assert!(codes(src, run_union_property_access).is_empty());
    }

    #[test]
    fn union_property_assignment_missing_on_one_arm_is_flagged() {
        let src = "<?php class A { public int $p; } class B {} \
            /** @param A|B $x */ function f($x): void { $x->p = 1; }";
        assert_eq!(
            codes(src, run_union_property_access_in_assign),
            ["property.notFound"]
        );
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
        assert_eq!(
            codes(src, run_access_properties_in_assign),
            ["property.notFound"]
        );
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
        assert_eq!(
            codes(src, run_access_static_properties),
            ["staticProperty.notFound"]
        );
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
        assert_eq!(
            codes(src, run_nullsafe_property_fetch),
            ["nullsafe.neverNull"]
        );
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
        let src =
            "<?php /** @property-write int $w */ class C {} function f() { return (new C())->w; }";
        assert_eq!(codes(src, run_reading_write_only), ["property.writeOnly"]);
    }

    #[test]
    fn writing_write_only_magic_property_is_clean() {
        let src =
            "<?php /** @property-write int $w */ class C {} function f() { (new C())->w = 1; }";
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
        let src =
            "<?php /** @property-read int $r */ class C {} function f() { (new C())->r = 1; }";
        assert_eq!(
            codes(src, run_writing_to_read_only),
            ["assign.propertyReadOnly"]
        );
    }

    #[test]
    fn reading_read_only_magic_property_is_clean() {
        let src =
            "<?php /** @property-read int $r */ class C {} function f() { return (new C())->r; }";
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
        assert_eq!(
            codes(src, run_access_static_properties_in_assign),
            ["staticProperty.notFound"]
        );
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
        assert_eq!(
            codes(src, run_access_static_properties),
            ["staticProperty.notFound"]
        );
    }

    // --- InvalidCallablePropertyTypeRule -------------------------------

    #[test]
    fn callable_property_type_is_flagged() {
        let src = "<?php class C { public callable $cb; }";
        assert_eq!(
            codes(src, run_invalid_callable_property_type),
            ["property.callableType"]
        );
    }

    #[test]
    fn nullable_callable_property_type_is_flagged() {
        let src = "<?php class C { public ?callable $cb; }";
        assert_eq!(
            codes(src, run_invalid_callable_property_type),
            ["property.callableType"]
        );
    }

    #[test]
    fn callable_in_union_property_type_is_flagged() {
        let src = "<?php class C { public int|callable $cb; }";
        assert_eq!(
            codes(src, run_invalid_callable_property_type),
            ["property.callableType"]
        );
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
        assert_eq!(
            codes(src, run_missing_property_typehint),
            ["missingType.property"]
        );
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
        assert_eq!(
            codes(src, run_missing_property_typehint),
            ["missingType.property"]
        );
    }

    #[test]
    fn untyped_multi_property_flags_each() {
        let src = "<?php class C { public $a, $b; }";
        assert_eq!(
            codes(src, run_missing_property_typehint),
            ["missingType.property", "missingType.property"]
        );
    }

    // --- `--fix` repairs (missingType.property) ---------------------------

    fn property_fix_tags(src: &str) -> Vec<String> {
        fixes(src, run_missing_property_typehint)
            .into_iter()
            .map(|(tag, _, _)| tag)
            .collect()
    }

    #[test]
    fn fix_var_from_default_value() {
        let src = "<?php\nclass C {\n    private $rows = [];\n    public function add(string $r): void { $this->rows[] = $r; }\n}\n";
        // An index-write (`$this->rows[] =`) bails: the element type evolves in a
        // way the collector doesn't model. No fix, finding still reports.
        assert!(property_fix_tags(src).is_empty());
    }

    #[test]
    fn fix_var_from_assignments_and_default() {
        let src = "<?php\nclass C {\n    private $rows = [];\n    public function set(): void { $this->rows = ['a', 'b']; }\n}\n";
        assert_eq!(property_fix_tags(src), ["@var list<string>"]);
    }

    #[test]
    fn fix_var_unions_default_and_assignment() {
        let src = "<?php\nclass C {\n    private $v = null;\n    public function set(): void { $this->v = 1; }\n}\n";
        assert_eq!(property_fix_tags(src), ["@var null|int"]);
    }

    #[test]
    fn fix_var_coalesce_assign_contributes_evidence() {
        let src = "<?php\nclass C {\n    private $n;\n    public function init(): void { $this->n ??= 5; }\n}\n";
        // No default and `??=` only: evidence is the RHS.
        assert_eq!(property_fix_tags(src), ["@var int"]);
    }

    #[test]
    fn no_fix_for_public_or_static_property() {
        // Public props can be written from other files; static writes use
        // `self::$p` which the collector doesn't model.
        for src in [
            "<?php class C { public $x = 1; }",
            "<?php class C { private static $x = 1; }",
        ] {
            for d in run_fixes(src, run_missing_property_typehint) {
                assert!(d.fix.is_none(), "{src}");
            }
        }
    }

    #[test]
    fn no_fix_on_compound_assign_or_byref_alias() {
        for src in [
            "<?php class C { private $n = 0; public function f(): void { $this->n += 1; } }",
            "<?php class C { private $n = 0; public function f(): void { $r =& $this->n; } }",
            "<?php class C { private $m = []; public function f(): void { preg_match('/x/', 'y', $this->m); } }",
            "<?php class C { private $d = 1; public function f($k): void { $this->{$k} = 'x'; } }",
        ] {
            for d in run_fixes(src, run_missing_property_typehint) {
                assert!(d.fix.is_none(), "{src}");
            }
        }
    }

    #[test]
    fn fix_survives_safe_builtin_reads() {
        // `count()` takes its argument by value — not an invisible write.
        let src = "<?php\nclass C {\n    private $rows = [];\n    public function set(): void { $this->rows = ['a']; }\n    public function n(): int { return count($this->rows); }\n}\n";
        assert_eq!(property_fix_tags(src), ["@var list<string>"]);
    }

    #[test]
    fn no_fix_when_evidence_is_only_a_bare_array() {
        // `[]` alone would render `@var array` — a type the missing-typehint
        // family itself reports. Skip rather than trade one finding for another.
        let src = "<?php class C { private $rows = []; }";
        for d in run_fixes(src, run_missing_property_typehint) {
            assert!(d.fix.is_none());
        }
    }

    #[test]
    fn fix_protected_property_on_leaf_class() {
        let src = "<?php\nclass C {\n    protected $n = 0;\n    public function bump(): void { $this->n = 5; }\n}\n";
        assert_eq!(property_fix_tags(src), ["@var int"]);
    }

    #[test]
    fn fix_var_inherited_from_overridden_parent_property() {
        // The Eloquent pattern: the parent both declares the type and writes
        // the slot, so own-evidence bails on the ancestor write; the fix
        // restates the parent's declared type.
        let src = "<?php\nclass B {\n    /** @var array<int, string> */\n    protected $fillable = [];\n    public function fill(array $f): void { $this->fillable = $f; }\n}\nclass C extends B {\n    protected $fillable = ['name'];\n}\n";
        assert_eq!(property_fix_tags(src), ["@var array<int, string>"]);
    }

    #[test]
    fn no_inherited_fix_when_child_default_conflicts() {
        // A child default incompatible with the ancestor type would trade the
        // finding for an assignment one.
        let src = "<?php\nclass B {\n    /** @var array<int, string> */\n    protected $fillable = [];\n    public function fill(array $f): void { $this->fillable = $f; }\n}\nclass C extends B {\n    protected $fillable = 'nope';\n}\n";
        for d in run_fixes(src, run_missing_property_typehint) {
            assert!(d.fix.is_none(), "conflicting default must not be fixed");
        }
    }

    #[test]
    fn no_inherited_fix_from_private_ancestor_property() {
        // A private ancestor property is a separate slot, not an override.
        // (Child is public so the own-evidence path can't fix it either.)
        let src = "<?php class B { /** @var int */ private $n = 0; } class C extends B { public $n = 0; }";
        for d in run_fixes(src, run_missing_property_typehint) {
            assert!(d.fix.is_none(), "private ancestor is not an override");
        }
    }

    #[test]
    fn no_inherited_fix_when_subclass_writes_the_property() {
        // A subclass write through the shared slot would be checked against
        // the new `@var`; the conservative guard bails.
        let src = "<?php\nclass B {\n    /** @var int */\n    protected $n = 0;\n    public function set(int $v): void { $this->n = $v; }\n}\nclass C extends B {\n    protected $n = 5;\n}\nclass D extends C {\n    public function zap(): void { $this->n = 9; }\n}\n";
        for d in run_fixes(src, run_missing_property_typehint) {
            assert!(
                d.fix.is_none(),
                "subclass write must bail the inherited fix"
            );
        }
    }

    #[test]
    fn no_inherited_fix_for_bare_array_ancestor_type() {
        // Restating the parent's bare `array` would re-report as
        // `missingType.iterableValue` — the check_type gate rejects it.
        let src = "<?php\nclass B {\n    /** @var array */\n    protected $casts = [];\n    public function merge(array $c): void { $this->casts = $c; }\n}\nclass C extends B {\n    protected $casts = [];\n}\n";
        for d in run_fixes(src, run_missing_property_typehint) {
            assert!(
                d.fix.is_none(),
                "bare-array ancestor type must not be restated"
            );
        }
    }

    #[test]
    fn no_fix_for_protected_property_on_extended_class() {
        let src = "<?php class B { protected $n = 0; } class C extends B {}";
        for d in run_fixes(src, run_missing_property_typehint) {
            assert!(
                d.fix.is_none(),
                "subclass exists: protected prop must not be fixed"
            );
        }
    }

    #[test]
    fn no_fix_when_parent_or_trait_writes_the_property() {
        for src in [
            // The parent's method writes the child's protected prop via $this.
            "<?php class B { public function reset(): void { $this->n = 'x'; } }              class C extends B { protected $n = 0; }",
            // A used trait writes a private prop (traits flatten into the class).
            "<?php trait T { public function reset(): void { $this->n = 'x'; } }              class C { use T; private $n = 0; }",
        ] {
            for d in run_fixes(src, run_missing_property_typehint) {
                assert!(d.fix.is_none(), "{src}");
            }
        }
    }

    #[test]
    fn no_fix_for_multi_element_declaration() {
        let src = "<?php class C { private $a = 1, $b = 2; }";
        for d in run_fixes(src, run_missing_property_typehint) {
            assert!(d.fix.is_none());
        }
    }

    #[test]
    fn fix_var_object_type_short_name() {
        let src = "<?php\nnamespace App;\nclass User {}\nclass C {\n    private $u;\n    public function set(): void { $this->u = new User(); }\n}\n";
        assert_eq!(property_fix_tags(src), ["@var User"]);
    }
}
