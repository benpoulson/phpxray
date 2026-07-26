//! phpstan category **Generics** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Generics/` — 15 rule(s) at level(s) 2.
//! The rule set's coverage truth is `cargo run -p xtask -- rule-manifest`; for phpstan's behaviour read `phpstan-src/src/Rules/` directly. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).

use crate::{symbols, walk, FileAnalysis, RuleEntry};
use php_ast::{
    ClassDecl, ClassKind, Expr, ExprKind, Member, Name, NameFq, Stmt, StmtKind, Visibility,
};
use php_diagnostics::Diagnostic;
use php_phpdoc::{parse as parse_doc, parse_block, parse_type};
use php_resolve::{for_each_region, Resolution, Scope};
use php_span::Span;
use php_types::Type;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TemplateVariance {
    Invariant,
    Covariant,
    Contravariant,
}

impl TemplateVariance {
    fn describe(self) -> &'static str {
        match self {
            TemplateVariance::Invariant => "invariant",
            TemplateVariance::Covariant => "covariant",
            TemplateVariance::Contravariant => "contravariant",
        }
    }

    fn is_invariant(self) -> bool {
        self == TemplateVariance::Invariant
    }
}

#[derive(Clone, Debug)]
struct TemplateInfo {
    name: String,
    bound: Option<String>,
    has_default: bool,
    variance: TemplateVariance,
}

#[derive(Clone, Debug)]
struct MethodTagTemplates {
    method: String,
    templates: Vec<TemplateInfo>,
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "generics.classTemplateType",
        level: 2,
        run: run_class_template_types,
    },
    RuleEntry {
        name: "generics.interfaceTemplateType",
        level: 2,
        run: run_interface_template_types,
    },
    RuleEntry {
        name: "generics.traitTemplateType",
        level: 2,
        run: run_trait_template_types,
    },
    RuleEntry {
        name: "enum.generic",
        level: 2,
        run: run_enum_template_types,
    },
    RuleEntry {
        name: "generics.functionTemplateType",
        level: 2,
        run: run_function_template_types,
    },
    RuleEntry {
        name: "generics.functionSignatureVariance",
        level: 2,
        run: run_function_signature_variance,
    },
    RuleEntry {
        name: "method.shadowTemplate",
        level: 2,
        run: run_method_template_types,
    },
    RuleEntry {
        name: "generics.methodSignatureVariance",
        level: 2,
        run: run_method_signature_variance,
    },
    RuleEntry {
        name: "generics.propertyVariance",
        level: 2,
        run: run_property_variance,
    },
    RuleEntry {
        name: "methodTag.shadowTemplate",
        level: 2,
        run: run_method_tag_template_types,
    },
    RuleEntry {
        name: "methodTagTrait.shadowTemplate",
        level: 2,
        run: run_method_tag_template_trait_types,
    },
    RuleEntry {
        name: "generics.classAncestors",
        level: 2,
        run: run_class_ancestors,
    },
    RuleEntry {
        name: "generics.interfaceAncestors",
        level: 2,
        run: run_interface_ancestors,
    },
    RuleEntry {
        name: "generics.enumAncestors",
        level: 2,
        run: run_enum_ancestors,
    },
    RuleEntry {
        name: "generics.usedTraits",
        level: 2,
        run: run_used_traits,
    },
    RuleEntry {
        name: "generics.notSubtype",
        level: 2,
        run: run_generic_bounds,
    },
];

/// `GenericObjectTypeCheck` (the `generics.notSubtype` branch) — when a generic
/// ancestor supplies type arguments (`@extends Base<X>`, `@implements I<X>`,
/// `@use Trait<X>`), each argument must be a subtype of the target class's
/// declared `@template T of Bound`. FP-safe: an argument is only flagged when it
/// is *confidently* not assignable to the bound (both sides concrete + known);
/// unbounded templates, template pass-through, and unresolved/vendor targets stay
/// silent.
fn run_generic_bounds(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class_like(fa, |_scope, class, fqn, span| {
        let Some(class_fqn) = fqn else { return };
        let Some(refl) = fa.reflection.class(&class_fqn) else {
            return;
        };
        let implements_tag = if class.kind == ClassKind::Enum || class.kind == ClassKind::Class {
            "@implements"
        } else {
            "@extends"
        };
        check_generic_bounds(fa, &refl.parents, "@extends", span, &mut out);
        check_generic_bounds(fa, &refl.interfaces, implements_tag, span, &mut out);
        check_generic_bounds(fa, &refl.traits, "@use", span, &mut out);
    });
    out
}

fn check_generic_bounds(
    fa: &FileAnalysis,
    reflected: &[Type],
    tag: &str,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    for ancestor in reflected {
        let Type::Named { fqn, args } = ancestor else {
            continue;
        };
        if args.is_empty() {
            continue;
        }
        let Some(ancestor_refl) = fa.reflection.class(fqn) else {
            continue;
        };
        for (i, arg) in args.iter().enumerate() {
            let Some(Some(bound)) = ancestor_refl.template_bounds.get(i) else {
                continue;
            };
            if matches!(bound, Type::Mixed) {
                continue;
            }
            if crate::is_assignable(fa.reflection, arg, bound) {
                continue;
            }
            let Some(template_name) = ancestor_refl.templates.get(i) else {
                continue;
            };
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "Type {arg} in generic type {ancestor} in PHPDoc tag {tag} is not subtype of template type {template_name} of {bound} of {} {fqn}.",
                        class_like_description(ancestor_refl.kind),
                    ),
                )
                .with_code("generics.notSubtype"),
            );
        }
    }
}

fn class_like_description(kind: ClassKind) -> &'static str {
    match kind {
        ClassKind::Class => "class",
        ClassKind::Interface => "interface",
        ClassKind::Trait => "trait",
        ClassKind::Enum => "enum",
    }
}

fn run_class_template_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class_like(fa, |scope, class, fqn, span| {
        if class.kind != ClassKind::Class {
            return;
        }
        let Some(raw) = class.doc.as_deref() else {
            return;
        };
        let display = fqn
            .map(|n| format!("class {n}"))
            .unwrap_or_else(|| "anonymous class".to_string());
        check_template_tags(
            fa,
            scope,
            span,
            raw_templates(raw),
            |name| {
                format!("PHPDoc tag @template for {display} cannot have existing class {name} as its name.")
            },
            |name, prior| {
                format!(
                    "PHPDoc tag @template {name} for {display} does not have a default type but follows an optional @template {prior}."
                )
            },
            &mut out,
        );
    });
    out
}

fn run_interface_template_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class_like(fa, |scope, class, fqn, span| {
        if class.kind != ClassKind::Interface {
            return;
        }
        let (Some(raw), Some(display)) = (class.doc.as_deref(), fqn) else {
            return;
        };
        check_template_tags(
            fa,
            scope,
            span,
            raw_templates(raw),
            |name| {
                format!("PHPDoc tag @template for interface {display} cannot have existing class {name} as its name.")
            },
            |name, prior| {
                format!(
                    "PHPDoc tag @template {name} for interface {display} does not have a default type but follows an optional @template {prior}."
                )
            },
            &mut out,
        );
    });
    out
}

fn run_trait_template_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class_like(fa, |scope, class, fqn, span| {
        if class.kind != ClassKind::Trait {
            return;
        }
        let (Some(raw), Some(display)) = (class.doc.as_deref(), fqn) else {
            return;
        };
        check_template_tags(
            fa,
            scope,
            span,
            raw_templates(raw),
            |name| {
                format!("PHPDoc tag @template for trait {display} cannot have existing class {name} as its name.")
            },
            |name, prior| {
                format!(
                    "PHPDoc tag @template {name} for trait {display} does not have a default type but follows an optional @template {prior}."
                )
            },
            &mut out,
        );
    });
    out
}

fn run_enum_template_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class_like(fa, |_scope, class, fqn, span| {
        if class.kind != ClassKind::Enum {
            return;
        }
        let (Some(raw), Some(display)) = (class.doc.as_deref(), fqn) else {
            return;
        };
        let count = raw_templates(raw).len();
        if count == 0 {
            return;
        }
        out.push(
            Diagnostic::error(
                span,
                format!(
                    "Enum {display} has PHPDoc @template tag{} but enums cannot be generic.",
                    if count == 1 { "" } else { "s" }
                ),
            )
            .with_code("enum.generic"),
        );
    });
    out
}

fn run_function_template_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        visit_stmts(region, &mut |st| {
            let StmtKind::Function(function) = &st.kind else {
                return;
            };
            let Some(raw) = function.doc.as_deref() else {
                return;
            };
            let display = scope.qualify(fa.interner.resolve(function.name));
            check_template_tags(
                fa,
                scope,
                st.span,
                raw_templates(raw),
                |name| {
                    format!(
                        "PHPDoc tag @template for function {display}() cannot have existing class {name} as its name."
                    )
                },
                |name, prior| {
                    format!(
                        "PHPDoc tag @template {name} for function {display}() does not have a default type but follows an optional @template {prior}."
                    )
                },
                &mut out,
            );
        });
    });
    out
}

/// `FunctionSignatureVarianceRule` — the deterministic declaration branch:
/// function-local templates may not be declared covariant/contravariant.
/// Parameter/return position checks need full referenced-template variance
/// tracking and stay deferred.
fn run_function_signature_variance(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        visit_stmts(region, &mut |st| {
            let StmtKind::Function(function) = &st.kind else {
                return;
            };
            let Some(raw) = function.doc.as_deref() else {
                return;
            };
            let display = scope.qualify(fa.interner.resolve(function.name));
            check_non_invariant_signature_templates(
                st.span,
                raw_templates(raw),
                &format!("in function {display}()"),
                "function.variance",
                &mut out,
            );
        });
    });
    out
}

fn run_method_template_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class_like(fa, |scope, class, fqn, _class_span| {
        let Some(class_display) = fqn else { return };
        let class_templates = class.doc.as_deref().map(raw_templates).unwrap_or_default();
        let class_template_names: Vec<&str> =
            class_templates.iter().map(|t| t.name.as_str()).collect();
        for member in &class.members {
            let Member::Method(method) = member else {
                continue;
            };
            let Some(raw) = method.doc.as_deref() else {
                continue;
            };
            let method_name = fa.interner.resolve(method.name);
            let method_templates = raw_templates(raw);
            check_template_tags(
                fa,
                scope,
                method.name_span,
                method_templates.clone(),
                |name| {
                    format!(
                        "PHPDoc tag @template for method {class_display}::{method_name}() cannot have existing class {name} as its name."
                    )
                },
                |name, prior| {
                    format!(
                        "PHPDoc tag @template {name} for method {class_display}::{method_name}() does not have a default type but follows an optional @template {prior}."
                    )
                },
                &mut out,
            );
            for mt in &method_templates {
                if !class_template_names.iter().any(|name| *name == mt.name) {
                    continue;
                }
                let shadowed = class_templates
                    .iter()
                    .find(|ct| ct.name == mt.name)
                    .map(|ct| template_display(scope, &class_templates, ct))
                    .unwrap_or_else(|| mt.name.clone());
                out.push(
                    Diagnostic::error(
                        method.name_span,
                        format!(
                            "PHPDoc tag @template {} for method {class_display}::{method_name}() shadows @template {shadowed} for class {class_display}.",
                            mt.name
                        ),
                    )
                    .with_code("method.shadowTemplate"),
                );
            }
        }
    });
    out
}

/// `MethodSignatureVarianceRule` — the deterministic declaration branch:
/// method-local templates may not be declared covariant/contravariant.
fn run_method_signature_variance(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class_like(fa, |_scope, class, fqn, _class_span| {
        let Some(class_display) = fqn else { return };
        for member in &class.members {
            let Member::Method(method) = member else {
                continue;
            };
            let Some(raw) = method.doc.as_deref() else {
                continue;
            };
            let method_name = fa.interner.resolve(method.name);
            check_non_invariant_signature_templates(
                method.name_span,
                raw_templates(raw),
                &format!("in method {class_display}::{method_name}()"),
                "method.variance",
                &mut out,
            );
        }
    });
    out
}

/// `PropertyVarianceRule` — FP-safe read/write property branch. Public or
/// protected plain properties are invariant positions; if a covariant or
/// contravariant class template appears in their declared type, report it.
/// Readonly, asymmetric-set, hook, promoted, and private properties are left
/// silent until the richer property-access model can mirror PHPStan exactly.
fn run_property_variance(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class_like(fa, |scope, class, fqn, class_span| {
        let Some(class_display) = fqn else { return };
        let class_templates = class.doc.as_deref().map(raw_templates).unwrap_or_default();
        let variant_templates: Vec<&TemplateInfo> = class_templates
            .iter()
            .filter(|t| !t.variance.is_invariant())
            .collect();
        if variant_templates.is_empty() {
            return;
        }
        if class.modifiers.is_readonly {
            return;
        }
        let template_names = class_templates
            .iter()
            .map(|t| t.name.clone())
            .collect::<Vec<_>>();
        for member in &class.members {
            let Member::Property(property) = member else {
                continue;
            };
            if property.modifiers.visibility == Some(Visibility::Private)
                || property.modifiers.is_readonly
                || property.modifiers.set_visibility.is_some()
            {
                continue;
            }
            let Some(ty) = property_declared_type(scope, &template_names, property) else {
                continue;
            };
            let mut used = Vec::new();
            collect_template_vars(&ty, &template_names, &mut used);
            if used.is_empty() {
                continue;
            }
            for prop in &property.props {
                if prop.hooks.is_some() {
                    continue;
                }
                let prop_name = fa.interner.resolve(prop.name);
                for template in &variant_templates {
                    if !used.iter().any(|name| name == &template.name) {
                        continue;
                    }
                    out.push(
                        Diagnostic::error(
                            class_span,
                            format!(
                                "Template type {} is declared as {}, but occurs in invariant position in property {class_display}::${prop_name}.",
                                template.name,
                                template.variance.describe(),
                            ),
                        )
                        .with_code("generics.variance"),
                    );
                }
            }
        }
    });
    out
}

fn run_method_tag_template_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    run_method_tag_templates(fa, false)
}

fn run_method_tag_template_trait_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    run_method_tag_templates(fa, true)
}

/// `ClassAncestorsRule` — the FP-safe `missingType.generics` branch for direct
/// same-file generic ancestors whose required template types are not supplied.
/// Generic arity/subtype/variance and wrong-parent branches require richer
/// PHPDoc metadata and remain deferred.
fn run_class_ancestors(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class_like(fa, |scope, class, fqn, span| {
        if class.kind != ClassKind::Class {
            return;
        }
        let Some(class_fqn) = fqn else { return };
        let Some(refl) = fa.reflection.class(&class_fqn) else {
            return;
        };
        check_missing_generic_ancestor(
            GenericAncestorCheck {
                fa,
                scope,
                class_fqn: &class_fqn,
                subject_kind: "Class",
                relation: "extends generic class",
                native_names: &class.extends,
                reflected: &refl.parents,
                span,
            },
            &mut out,
        );
        check_missing_generic_ancestor(
            GenericAncestorCheck {
                fa,
                scope,
                class_fqn: &class_fqn,
                subject_kind: "Class",
                relation: "implements generic interface",
                native_names: &class.implements,
                reflected: &refl.interfaces,
                span,
            },
            &mut out,
        );
    });
    out
}

/// `InterfaceAncestorsRule` — direct same-file generic interface extension
/// without supplied template arguments.
fn run_interface_ancestors(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class_like(fa, |scope, class, fqn, span| {
        if class.kind != ClassKind::Interface {
            return;
        }
        let Some(class_fqn) = fqn else { return };
        let Some(refl) = fa.reflection.class(&class_fqn) else {
            return;
        };
        check_missing_generic_ancestor(
            GenericAncestorCheck {
                fa,
                scope,
                class_fqn: &class_fqn,
                subject_kind: "Interface",
                relation: "extends generic interface",
                native_names: &class.extends,
                reflected: &refl.parents,
                span,
            },
            &mut out,
        );
    });
    out
}

/// `EnumAncestorsRule` — direct same-file generic interface implementation
/// without supplied template arguments.
fn run_enum_ancestors(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class_like(fa, |scope, class, fqn, span| {
        if class.kind != ClassKind::Enum {
            return;
        }
        let Some(class_fqn) = fqn else { return };
        let Some(refl) = fa.reflection.class(&class_fqn) else {
            return;
        };
        check_missing_generic_ancestor(
            GenericAncestorCheck {
                fa,
                scope,
                class_fqn: &class_fqn,
                subject_kind: "Enum",
                relation: "implements generic interface",
                native_names: &class.implements,
                reflected: &refl.interfaces,
                span,
            },
            &mut out,
        );
    });
    out
}

/// `UsedTraitsRule` — direct same-file generic trait use without supplied
/// template arguments. Local trait-use `@use` docblocks are not stored on the
/// AST, so this branch deliberately skips a trait use when such a docblock is
/// present in the source; that keeps valid `/** @use Trait<int> */ use Trait;`
/// cases silent until trait-use PHPDoc is first-class.
fn run_used_traits(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class_like(fa, |scope, class, fqn, class_span| {
        let Some(class_fqn) = fqn else { return };
        let Some(refl) = fa.reflection.class(&class_fqn) else {
            return;
        };
        for member in &class.members {
            let Member::TraitUse(trait_use) = member else {
                continue;
            };
            if trait_use_has_local_use_doc(fa.source, trait_use) {
                continue;
            }
            for name in &trait_use.traits {
                let Some(trait_fqn) = scope.resolve_class(name).fqn().map(str::to_string) else {
                    continue;
                };
                if reflected_has_args(&refl.traits, &trait_fqn) {
                    continue;
                }
                let Some(templates) =
                    same_file_required_templates_of_kind(fa, &trait_fqn, Some(ClassKind::Trait))
                else {
                    continue;
                };
                out.push(
                    Diagnostic::error(
                        class_span,
                        format!(
                            "{} {class_fqn} uses generic trait {trait_fqn} but does not specify its types: {}",
                            class_kind_sentence_label(class.kind),
                            templates.join(", "),
                        ),
                    )
                    .with_code("missingType.generics"),
                );
            }
        }
    });
    out
}

struct GenericAncestorCheck<'a> {
    fa: &'a FileAnalysis<'a>,
    scope: &'a Scope,
    class_fqn: &'a str,
    subject_kind: &'a str,
    relation: &'a str,
    native_names: &'a [Name],
    reflected: &'a [Type],
    span: Span,
}

fn check_missing_generic_ancestor(check: GenericAncestorCheck<'_>, out: &mut Vec<Diagnostic>) {
    for name in check.native_names {
        let Some(ancestor_fqn) = check.scope.resolve_class(name).fqn().map(str::to_string) else {
            continue;
        };
        if reflected_has_args(check.reflected, &ancestor_fqn) {
            continue;
        }
        let Some(templates) = same_file_required_templates(check.fa, &ancestor_fqn) else {
            continue;
        };
        out.push(
            Diagnostic::error(
                check.span,
                format!(
                    "{} {} {} {ancestor_fqn} but does not specify its types: {}",
                    check.subject_kind,
                    check.class_fqn,
                    check.relation,
                    templates.join(", ")
                ),
            )
            .with_code("missingType.generics"),
        );
    }
}

fn reflected_has_args(reflected: &[Type], ancestor_fqn: &str) -> bool {
    reflected.iter().any(|ty| match ty {
        Type::Named { fqn, args } => symbols::same_fqn(fqn, ancestor_fqn) && !args.is_empty(),
        _ => false,
    })
}

/// Template names for a same-file class-like only when all templates are
/// required. Optional/defaulted template parameters are skipped because
/// `ClassReflection` currently stores names but not defaults.
fn same_file_required_templates(fa: &FileAnalysis, ancestor_fqn: &str) -> Option<Vec<String>> {
    same_file_required_templates_of_kind(fa, ancestor_fqn, None)
}

fn same_file_required_templates_of_kind(
    fa: &FileAnalysis,
    ancestor_fqn: &str,
    kind: Option<ClassKind>,
) -> Option<Vec<String>> {
    let mut found = None;
    for_each_class_like(fa, |_scope, class, fqn, _span| {
        if found.is_some()
            || !fqn
                .as_deref()
                .is_some_and(|f| symbols::same_fqn(f, ancestor_fqn))
        {
            return;
        }
        if kind.is_some_and(|k| class.kind != k) {
            return;
        }
        let Some(raw) = class.doc.as_deref() else {
            return;
        };
        let templates = raw_templates(raw);
        if templates.is_empty() || templates.iter().any(|t| t.has_default) {
            return;
        }
        found = Some(templates.into_iter().map(|t| t.name).collect());
    });
    found
}

fn check_non_invariant_signature_templates(
    span: Span,
    templates: Vec<TemplateInfo>,
    context: &str,
    code: &'static str,
    out: &mut Vec<Diagnostic>,
) {
    for template in templates {
        if template.variance.is_invariant() {
            continue;
        }
        out.push(
            Diagnostic::error(
                span,
                format!(
                    "Variance annotation is only allowed for type parameters of classes and interfaces, but occurs in template type {} in {context}.",
                    template.name
                ),
            )
            .with_code(code),
        );
    }
}

fn property_declared_type(
    scope: &Scope,
    templates: &[String],
    property: &php_ast::PropertyDecl,
) -> Option<Type> {
    if let Some(raw) = property.doc.as_deref() {
        let doc = parse_doc(raw);
        if let Some(doc_ty) = doc.vars.first().and_then(|var| var.ty.as_ref()) {
            return Some(php_reflect::resolve_doc_type(scope, templates, doc_ty));
        }
    }
    property
        .ty
        .as_ref()
        .map(|ty| php_reflect::resolve_ast_type(scope, ty))
}

fn collect_template_vars(ty: &Type, templates: &[String], out: &mut Vec<String>) {
    match ty {
        Type::TemplateVar(name) if templates.iter().any(|t| t.as_str() == &**name) => {
            if !out.iter().any(|seen| seen.as_str() == &**name) {
                out.push(name.to_string());
            }
        }
        Type::Nullable(inner) | Type::List(inner) | Type::ClassString(Some(inner)) => {
            collect_template_vars(inner, templates, out)
        }
        Type::Union(parts) | Type::Intersection(parts) => {
            for part in parts.iter() {
                collect_template_vars(part, templates, out);
            }
        }
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            collect_template_vars(&kv.0, templates, out);
            collect_template_vars(&kv.1, templates, out);
        }
        Type::Named { args, .. } => {
            for arg in args {
                collect_template_vars(arg, templates, out);
            }
        }
        Type::Callable(Some(sig)) => {
            for param in &sig.params {
                collect_template_vars(param, templates, out);
            }
            collect_template_vars(&sig.ret, templates, out);
        }
        Type::Shape { fields, .. } => {
            for field in fields {
                collect_template_vars(&field.ty, templates, out);
            }
        }
        Type::Conditional {
            target, then, els, ..
        } => {
            collect_template_vars(target, templates, out);
            collect_template_vars(then, templates, out);
            collect_template_vars(els, templates, out);
        }
        _ => {}
    }
}

fn class_kind_sentence_label(kind: ClassKind) -> &'static str {
    match kind {
        ClassKind::Class => "Class",
        ClassKind::Interface => "Interface",
        ClassKind::Trait => "Trait",
        ClassKind::Enum => "Enum",
    }
}

fn trait_use_has_local_use_doc(source: &str, trait_use: &php_ast::TraitUseDecl) -> bool {
    let Some(first_trait) = trait_use.traits.first() else {
        return false;
    };
    local_doc_before_trait_use(source, first_trait.span.start as usize).is_some_and(doc_has_use_tag)
}

fn local_doc_before_trait_use(source: &str, trait_name_start: usize) -> Option<&str> {
    if trait_name_start > source.len() {
        return None;
    }
    let bytes = source.as_bytes();
    let before_trait = skip_ws_back(bytes, trait_name_start);
    let use_start = before_trait.checked_sub(3)?;
    if source.get(use_start..before_trait)? != "use" {
        return None;
    }
    if use_start > 0 && is_ident_byte(bytes[use_start - 1]) {
        return None;
    }
    let before_use = skip_ws_back(bytes, use_start);
    let doc_end = before_use;
    let body_end = doc_end.checked_sub(2)?;
    if source.get(body_end..doc_end)? != "*/" {
        return None;
    }
    let doc_start = source.get(..body_end)?.rfind("/**")?;
    source.get(doc_start..doc_end)
}

fn doc_has_use_tag(raw: &str) -> bool {
    parse_block(raw).tags.iter().any(|tag| {
        let (base, _prefix) = crate::doctags::prefix_label(&tag.name);
        base == "use" || base == "template-use"
    })
}

fn skip_ws_back(bytes: &[u8], mut pos: usize) -> usize {
    while pos > 0 && bytes[pos - 1].is_ascii_whitespace() {
        pos -= 1;
    }
    pos
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn run_method_tag_templates(fa: &FileAnalysis, traits_only: bool) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_class_like(fa, |scope, class, fqn, span| {
        if (class.kind == ClassKind::Trait) != traits_only {
            return;
        }
        let (Some(raw), Some(class_display)) = (class.doc.as_deref(), fqn) else {
            return;
        };
        let class_templates = raw_templates(raw);
        let class_template_names: Vec<&str> =
            class_templates.iter().map(|t| t.name.as_str()).collect();
        for method_tag in method_tag_templates(raw) {
            let method_name = method_tag.method;
            check_template_tags(
                fa,
                scope,
                span,
                method_tag.templates.clone(),
                |name| {
                    format!(
                        "PHPDoc tag @method template for method {class_display}::{method_name}() cannot have existing class {name} as its name."
                    )
                },
                |name, prior| {
                    format!(
                        "PHPDoc tag @template {name} for method {class_display}::{method_name}() does not have a default type but follows an optional @template {prior}."
                    )
                },
                &mut out,
            );
            for mt in &method_tag.templates {
                if !class_template_names.iter().any(|name| *name == mt.name) {
                    continue;
                }
                let shadowed = class_templates
                    .iter()
                    .find(|ct| ct.name == mt.name)
                    .map(|ct| template_display(scope, &class_templates, ct))
                    .unwrap_or_else(|| mt.name.clone());
                out.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "PHPDoc tag @method template {} for method {class_display}::{method_name}() shadows @template {shadowed} for class {class_display}.",
                            mt.name
                        ),
                    )
                    .with_code("methodTag.shadowTemplate"),
                );
            }
        }
    });
    out
}

fn check_template_tags(
    fa: &FileAnalysis,
    scope: &Scope,
    span: Span,
    templates: Vec<TemplateInfo>,
    existing_class_msg: impl Fn(&str) -> String,
    required_after_optional_msg: impl Fn(&str, &str) -> String,
    out: &mut Vec<Diagnostic>,
) {
    let mut last_optional: Option<String> = None;
    for template in templates {
        if let Some(class_name) = existing_class_name(fa, scope, &template.name) {
            out.push(
                Diagnostic::error(span, existing_class_msg(&class_name))
                    .with_code("generics.existingClass"),
            );
        }

        if template.has_default {
            last_optional = Some(template.name.clone());
        } else if let Some(prior) = &last_optional {
            out.push(
                Diagnostic::error(span, required_after_optional_msg(&template.name, prior))
                    .with_code("generics.requiredTypeAfterOptional"),
            );
        }
    }
}

fn existing_class_name(fa: &FileAnalysis, scope: &Scope, name: &str) -> Option<String> {
    let name_node = Name {
        span: Span::new(0, 0),
        fq: NameFq::NotFq,
        text: name.to_string(),
    };
    if let Resolution::Fqn(fqn) = scope.resolve_class(&name_node) {
        if let Some(entry) = fa.project.class(&fqn) {
            return Some(entry.fqn.clone());
        }
    }
    fa.project.class(name).map(|entry| entry.fqn.clone())
}

fn template_display(scope: &Scope, templates: &[TemplateInfo], template: &TemplateInfo) -> String {
    let Some(bound) = &template.bound else {
        return template.name.clone();
    };
    let template_names: Vec<String> = templates.iter().map(|t| t.name.clone()).collect();
    match parse_type(bound) {
        Some(ty) => format!(
            "{} of {}",
            template.name,
            php_reflect::resolve_doc_type(scope, &template_names, &ty)
        ),
        None => format!("{} of {bound}", template.name),
    }
}

fn raw_templates(raw: &str) -> Vec<TemplateInfo> {
    parse_block(raw)
        .tags
        .iter()
        .filter_map(|tag| {
            let (base, _prefix) = crate::doctags::prefix_label(&tag.name);
            if !is_template_tag(base) {
                return None;
            }
            parse_template_value(base, &tag.value)
        })
        .collect()
}

fn method_tag_templates(raw: &str) -> Vec<MethodTagTemplates> {
    parse_block(raw)
        .tags
        .iter()
        .filter_map(|tag| {
            let (base, _prefix) = crate::doctags::prefix_label(&tag.name);
            if base != "method" {
                return None;
            }
            parse_method_tag_templates(&tag.value)
        })
        .collect()
}

fn is_template_tag(base: &str) -> bool {
    matches!(
        base,
        "template" | "template-covariant" | "template-contravariant"
    )
}

fn parse_template_value(base: &str, value: &str) -> Option<TemplateInfo> {
    let value = value.trim();
    let end = value
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .unwrap_or(value.len());
    let name = value[..end].to_string();
    if name.is_empty() {
        return None;
    }
    let rest = value[end..].trim_start();
    let (before_default, has_default) = match top_level_eq(rest) {
        Some(i) => (rest[..i].trim_end(), true),
        None => (rest, false),
    };
    let bound = before_default
        .strip_prefix("of ")
        .or_else(|| before_default.strip_prefix("as "))
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(str::to_string);
    Some(TemplateInfo {
        name,
        bound,
        has_default,
        variance: template_variance(base),
    })
}

fn template_variance(base: &str) -> TemplateVariance {
    match base {
        "template-covariant" => TemplateVariance::Covariant,
        "template-contravariant" => TemplateVariance::Contravariant,
        _ => TemplateVariance::Invariant,
    }
}

fn parse_method_tag_templates(value: &str) -> Option<MethodTagTemplates> {
    let open = top_level_byte(value, b'(')?;
    let mut head = value[..open].trim_end();
    if !head.ends_with('>') {
        return None;
    }
    let gt = head.len() - 1;
    let lt = matching_angle_start(head, gt)?;
    let generic_part = &head[lt + 1..gt];
    head = head[..lt].trim_end();
    let method_start = head
        .rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .map(|i| i + 1)
        .unwrap_or(0);
    let method = head[method_start..].to_string();
    if method.is_empty() {
        return None;
    }
    let templates: Vec<TemplateInfo> = split_top_level(generic_part, b',')
        .into_iter()
        .filter_map(|part| parse_template_value("template", part))
        .collect();
    if templates.is_empty() {
        return None;
    }
    Some(MethodTagTemplates { method, templates })
}

fn top_level_eq(s: &str) -> Option<usize> {
    top_level_byte(s, b'=')
}

fn top_level_byte(s: &str, needle: u8) -> Option<usize> {
    let mut round = 0i32;
    let mut square = 0i32;
    let mut curly = 0i32;
    let mut angle = 0i32;
    for (i, c) in s.bytes().enumerate() {
        match c {
            _ if c == needle && round == 0 && square == 0 && curly == 0 && angle == 0 => {
                return Some(i)
            }
            b'(' => round += 1,
            b')' if round > 0 => round -= 1,
            b'[' => square += 1,
            b']' if square > 0 => square -= 1,
            b'{' => curly += 1,
            b'}' if curly > 0 => curly -= 1,
            b'<' => angle += 1,
            b'>' if angle > 0 => angle -= 1,
            _ => {}
        }
    }
    None
}

fn split_top_level(s: &str, sep: u8) -> Vec<&str> {
    let mut round = 0i32;
    let mut square = 0i32;
    let mut curly = 0i32;
    let mut angle = 0i32;
    let mut start = 0usize;
    let mut out = Vec::new();
    for (i, c) in s.bytes().enumerate() {
        match c {
            b'(' => round += 1,
            b')' if round > 0 => round -= 1,
            b'[' => square += 1,
            b']' if square > 0 => square -= 1,
            b'{' => curly += 1,
            b'}' if curly > 0 => curly -= 1,
            b'<' => angle += 1,
            b'>' if angle > 0 => angle -= 1,
            _ if c == sep && round == 0 && square == 0 && curly == 0 && angle == 0 => {
                out.push(s[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(s[start..].trim());
    out.into_iter().filter(|part| !part.is_empty()).collect()
}

fn matching_angle_start(s: &str, close: usize) -> Option<usize> {
    let bytes = s.as_bytes();
    if bytes.get(close) != Some(&b'>') {
        return None;
    }
    let mut depth = 0i32;
    for i in (0..=close).rev() {
        match bytes[i] {
            b'>' => depth += 1,
            b'<' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

fn for_each_class_like(
    fa: &FileAnalysis,
    mut f: impl FnMut(&Scope, &ClassDecl, Option<String>, Span),
) {
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        visit_stmts(region, &mut |st| {
            if let StmtKind::Class(class) = &st.kind {
                let fqn = class
                    .name
                    .map(|name| scope.qualify(fa.interner.resolve(name)));
                f(scope, class, fqn, st.span);
            }
            walk::for_each_expr_in_scope(st, &mut |expr| {
                visit_anonymous_classes(scope, expr, &mut f)
            });
        });
    });
}

fn visit_anonymous_classes(
    scope: &Scope,
    expr: &Expr,
    f: &mut impl FnMut(&Scope, &ClassDecl, Option<String>, Span),
) {
    if let ExprKind::NewAnon { class, .. } = &expr.kind {
        f(scope, class, None, expr.span);
        for member in &class.members {
            if let Member::Method(method) = member {
                if let Some(body) = &method.body {
                    for st in body.iter() {
                        walk::for_each_expr_in_scope(st, &mut |inner| {
                            visit_anonymous_classes(scope, inner, f)
                        });
                    }
                }
            }
        }
    }
}

fn visit_stmts(stmts: &[Stmt], f: &mut impl FnMut(&Stmt)) {
    for st in stmts {
        f(st);
        match &st.kind {
            StmtKind::Block(body) => visit_stmts(body, f),
            StmtKind::If {
                then, elseifs, els, ..
            } => {
                visit_stmts(std::slice::from_ref(then), f);
                for elseif in elseifs {
                    visit_stmts(std::slice::from_ref(&elseif.body), f);
                }
                if let Some(els) = els {
                    visit_stmts(std::slice::from_ref(els), f);
                }
            }
            StmtKind::While { body, .. }
            | StmtKind::DoWhile { body, .. }
            | StmtKind::For { body, .. }
            | StmtKind::Foreach { body, .. } => visit_stmts(std::slice::from_ref(body), f),
            StmtKind::Switch { cases, .. } => {
                for case in cases {
                    visit_stmts(&case.body, f);
                }
            }
            StmtKind::Try {
                body,
                catches,
                finally,
            } => {
                visit_stmts(body, f);
                for catch in catches {
                    visit_stmts(&catch.body, f);
                }
                if let Some(finally) = finally {
                    visit_stmts(finally, f);
                }
            }
            StmtKind::Declare {
                body: Some(body), ..
            } => visit_stmts(std::slice::from_ref(body), f),
            StmtKind::Namespace {
                body: Some(body), ..
            } => visit_stmts(body, f),
            StmtKind::Function(function) => visit_stmts(&function.body, f),
            StmtKind::Class(class) => {
                for member in &class.members {
                    if let Member::Method(method) = member {
                        if let Some(body) = &method.body {
                            visit_stmts(body, f);
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{codes, run};

    #[test]
    fn enum_template_tags_are_rejected() {
        assert_eq!(
            codes(
                "<?php
                /** @template T */
                enum Foo {}
                ",
                run_enum_template_types,
            ),
            ["enum.generic"]
        );
    }

    #[test]
    fn template_name_that_is_existing_class_is_rejected() {
        assert_eq!(
            codes(
                "<?php namespace App;
                use stdClass;
                /** @template stdClass */
                class Box {}
                ",
                run_class_template_types,
            ),
            ["generics.existingClass"]
        );
    }

    #[test]
    fn optional_template_before_required_template_is_rejected() {
        assert_eq!(
            codes(
                "<?php
                /**
                 * @template T
                 * @template U = string
                 * @template V
                 */
                function f($x) {}
                ",
                run_function_template_types,
            ),
            ["generics.requiredTypeAfterOptional"]
        );
    }

    #[test]
    fn method_template_shadowing_class_template_is_rejected() {
        let diagnostics = run(
            "<?php namespace App;
            /**
             * @template T of \\Exception
             * @template U
             */
            class Box {
                /** @template T */
                public function get() {}
            }
            ",
            run_method_template_types,
        );
        assert_eq!(
            diagnostics
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["method.shadowTemplate"]
        );
        assert_eq!(
            diagnostics[0].message,
            "PHPDoc tag @template T for method App\\Box::get() shadows @template T of Exception for class App\\Box."
        );
    }

    #[test]
    fn method_tag_template_shadowing_class_template_is_rejected() {
        assert_eq!(
            codes(
                "<?php namespace App;
                /**
                 * @template T
                 * @method void get<T>(T $value)
                 */
                class Box {}
                ",
                run_method_tag_template_types,
            ),
            ["methodTag.shadowTemplate"]
        );
    }

    #[test]
    fn method_tag_template_parser_extracts_generic_method_tags() {
        let tags =
            method_tag_templates("/**\n * @template T\n * @method void get<T>(T $value)\n */");
        assert_eq!(tags.len(), 1);
        assert_eq!(tags[0].method, "get");
        assert_eq!(
            tags[0]
                .templates
                .iter()
                .map(|t| t.name.as_str())
                .collect::<Vec<_>>(),
            ["T"]
        );
    }

    #[test]
    fn method_tag_template_trait_rule_only_runs_on_traits() {
        assert_eq!(
            codes(
                "<?php namespace App;
                /**
                 * @template T
                 * @method void get<T>(T $value)
                 */
                trait Box {}
                ",
                run_method_tag_template_trait_types,
            ),
            ["methodTag.shadowTemplate"]
        );
        assert!(codes(
            "<?php namespace App;
            /**
             * @template T
             * @method void get<T>(T $value)
             */
            class Box {}
            ",
            run_method_tag_template_trait_types,
        )
        .is_empty());
    }

    #[test]
    fn clean_templates_are_quiet() {
        let src = "<?php namespace App;
            /** @template T */
            class Box {
                /** @template U */
                public function get($x) {}
            }
            /** @template V */
            function f($x) {}
        ";
        assert!(codes(src, run_class_template_types).is_empty());
        assert!(codes(src, run_method_template_types).is_empty());
        assert!(codes(src, run_function_template_types).is_empty());
    }

    #[test]
    fn class_extending_generic_parent_without_args_is_flagged() {
        let src = "<?php namespace App;
            /** @template T */
            class Base {}
            class Child extends Base {}
        ";
        assert_eq!(codes(src, run_class_ancestors), ["missingType.generics"]);
    }

    #[test]
    fn class_extending_generic_parent_with_extends_args_is_clean() {
        let src = "<?php namespace App;
            /** @template T */
            class Base {}
            /** @extends Base<int> */
            class Child extends Base {}
        ";
        assert!(codes(src, run_class_ancestors).is_empty());
    }

    #[test]
    fn class_implementing_generic_interface_without_args_is_flagged() {
        let src = "<?php namespace App;
            /** @template T */
            interface I {}
            class Child implements I {}
        ";
        assert_eq!(codes(src, run_class_ancestors), ["missingType.generics"]);
    }

    #[test]
    fn interface_extending_generic_interface_without_args_is_flagged() {
        let src = "<?php namespace App;
            /** @template T */
            interface I {}
            interface Child extends I {}
        ";
        assert_eq!(
            codes(src, run_interface_ancestors),
            ["missingType.generics"]
        );
    }

    #[test]
    fn enum_implementing_generic_interface_without_args_is_flagged() {
        let src = "<?php namespace App;
            /** @template T */
            interface I {}
            enum E implements I {}
        ";
        assert_eq!(codes(src, run_enum_ancestors), ["missingType.generics"]);
    }

    #[test]
    fn generic_parent_with_default_template_is_skipped() {
        let src = "<?php namespace App;
            /** @template T = int */
            class Base {}
            class Child extends Base {}
        ";
        assert!(codes(src, run_class_ancestors).is_empty());
    }

    #[test]
    fn function_local_variance_annotation_is_rejected() {
        let diagnostics = run(
            "<?php namespace App;
            /** @template-covariant T */
            function f($x) {}
            ",
            run_function_signature_variance,
        );
        assert_eq!(
            diagnostics
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["function.variance"]
        );
        assert_eq!(
            diagnostics[0].message,
            "Variance annotation is only allowed for type parameters of classes and interfaces, but occurs in template type T in in function App\\f()."
        );
    }

    #[test]
    fn method_local_variance_annotation_is_rejected() {
        let diagnostics = run(
            "<?php namespace App;
            class C {
                /** @template-contravariant U */
                public function m($x) {}
            }
            ",
            run_method_signature_variance,
        );
        assert_eq!(
            diagnostics
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["method.variance"]
        );
        assert_eq!(
            diagnostics[0].message,
            "Variance annotation is only allowed for type parameters of classes and interfaces, but occurs in template type U in in method App\\C::m()."
        );
    }

    #[test]
    fn variant_class_template_in_plain_public_property_is_rejected() {
        let diagnostics = run(
            "<?php namespace App;
            /** @template-covariant T */
            class Box {
                /** @var T */
                public $value;
            }
            ",
            run_property_variance,
        );
        assert_eq!(
            diagnostics
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["generics.variance"]
        );
        assert_eq!(
            diagnostics[0].message,
            "Template type T is declared as covariant, but occurs in invariant position in property App\\Box::$value."
        );
    }

    #[test]
    fn private_or_restricted_properties_are_quiet_for_property_variance_subset() {
        let src = "<?php namespace App;
            /** @template-covariant T */
            readonly class Box {
                /** @var T */
                public $readonlyClassProp;
            }
            /** @template-covariant U */
            class Other {
                /** @var U */
                private $privateProp;
            }
        ";
        assert!(codes(src, run_property_variance).is_empty());
    }

    #[test]
    fn trait_use_of_generic_trait_without_args_is_flagged() {
        let diagnostics = run(
            "<?php namespace App;
            /** @template T */
            trait BagTrait {}
            class Box {
                use BagTrait;
            }
            ",
            run_used_traits,
        );
        assert_eq!(
            diagnostics
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["missingType.generics"]
        );
        assert_eq!(
            diagnostics[0].message,
            "Class App\\Box uses generic trait App\\BagTrait but does not specify its types: T"
        );
    }

    #[test]
    fn generic_arg_violating_bound_is_flagged() {
        let diagnostics = run(
            "<?php namespace App;
            class Animal {}
            /** @template T of Animal */
            class Base {}
            /** @extends Base<\\stdClass> */
            class Child extends Base {}
            ",
            run_generic_bounds,
        );
        assert_eq!(
            diagnostics
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["generics.notSubtype"]
        );
        assert_eq!(
            diagnostics[0].message,
            "Type stdClass in generic type App\\Base<stdClass> in PHPDoc tag @extends is not subtype of template type T of App\\Animal of class App\\Base."
        );
    }

    #[test]
    fn generic_arg_satisfying_bound_is_clean() {
        let src = "<?php namespace App;
            class Animal {}
            class Dog extends Animal {}
            /** @template T of Animal */
            class Base {}
            /** @extends Base<Dog> */
            class Child extends Base {}
        ";
        assert!(codes(src, run_generic_bounds).is_empty());
    }

    #[test]
    fn unbounded_generic_arg_is_clean() {
        let src = "<?php namespace App;
            /** @template T */
            class Base {}
            /** @extends Base<\\stdClass> */
            class Child extends Base {}
        ";
        assert!(codes(src, run_generic_bounds).is_empty());
    }

    #[test]
    fn trait_use_with_local_use_docblock_is_skipped() {
        let src = "<?php namespace App;
            /** @template T */
            trait BagTrait {}
            class Box {
                /** @use BagTrait<int> */
                use BagTrait;
            }
        ";
        assert!(codes(src, run_used_traits).is_empty());
    }
}
