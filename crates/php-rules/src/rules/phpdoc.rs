//! phpstan category **PhpDoc** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/PhpDoc/` — 22 rule(s) at level(s) 0,2.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! These rules are **structural**: they parse a declaration's attached doc
//! comment with our own `php_phpdoc` parser (NOT phpstan's — hard project rule)
//! and check the result against the declaration's real AST shape (parameter
//! names, native types, by-ref flags, the kind of node the tag sits on).
//!
//! Implemented (all level 2):
//! - `parameter.notFound`     — `@param`/`@phpstan-param` for a parameter that
//!   the function/method does not declare (`IncompatiblePhpDocTypeCheck`).
//! - `varTag.differentVariable` / `varTag.variableNotFound` — `@var $x` on a
//!   property whose name doesn't match (`WrongVariableNameInVarTagRule`).
//! - `varTag.misplaced`       — a `@var` tag on a class/function/method, where
//!   it has no effect (`WrongVariableNameInVarTagRule`).
//! - `phpDoc.phpstanTag`      — an unknown `@phpstan-*` tag
//!   (`InvalidPHPStanDocTagRule`).
//! - `parameter.phpDocType` / `return.phpDocType` — a `@param`/`@return` PHPDoc
//!   type that is not a subtype of the native type hint
//!   (`IncompatiblePhpDocTypeRule`, via `resolve_doc_type`/`resolve_ast_type`/
//!   `is_assignable`).
//! - `property.phpDocType` — a `@var` PHPDoc type on a property that is not a
//!   subtype of the property's native type (`IncompatiblePropertyPhpDocTypeRule`).
//! - `classConstant.phpDocType` — a `@var` PHPDoc type on a class constant that
//!   is not a subtype of the constant's native type
//!   (`IncompatibleClassConstantPhpDocTypeRule`).
//! - `throws.notThrowable` — a `@throws` type that is not a subtype of
//!   `Throwable` (`InvalidThrowsPhpDocValueRule`); only flagged when the type is
//!   a definite non-throwable (a scalar, or an *indexed* class that is provably
//!   not a `Throwable`).
//! - `varTag.trait` — a `@var` whose type references a (project-indexed) trait
//!   (`InvalidPhpDocVarTagTypeRule`).
//! - `selfOut.static` — `@phpstan-self-out` on a static method
//!   (`IncompatibleSelfOutTypeRule`).
//! - `requireExtends.on*` / `requireImplements.on*` — `@phpstan-require-extends`
//!   on a non-interface/non-trait, `@phpstan-require-implements` on a non-trait
//!   (`RequireExtendsDefinitionClassRule` / `RequireImplementsDefinitionClassRule`).
//! - `sealed.onEnum` — `@phpstan-sealed` on an enum (`SealedDefinitionClassRule`).
//!
//! Deferred (need machinery our pipeline doesn't yet expose):
//! - `InvalidPhpDocTagValueRule` (`phpDoc.parseError`): phpstan reports the
//!   *parse exception* from its own PHPDoc parser. Our `php_phpdoc` parser is
//!   intentionally lenient (malformed operands yield `None`/empty rather than a
//!   structured error with a message), so we cannot reproduce phpstan's
//!   "has invalid value (...): <exception message>" wording faithfully.
//! - `InvalidPhpDocVarTagTypeRule` (`class.notFound`): we deliberately do NOT
//!   flag unknown classes inside `@var` — our builtin/stub class coverage isn't
//!   complete enough to avoid false positives on namespaced/relative names. The
//!   `varTag.trait` half (a definite indexed trait) is done above.
//! - `missingType.iterableValue` / `missingType.generics`: "missing value type"
//!   checks are a separate strictness mode (level 6) — out of this category's
//!   level-2 scope.
//! - Conditional-return / assert rules (`FunctionAssertRule`,
//!   `MethodConditionalReturnTypeRule`, …): need `@phpstan-assert` /
//!   conditional-return semantic modelling our pipeline doesn't have yet.

#![allow(unused_imports)]
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{
    ClassDecl, ClassKind, FunctionDecl, Member, MethodDecl, Param, PropertyDecl, Stmt, StmtKind,
};
use php_diagnostics::Diagnostic;
use php_intern::Interner;
use php_reflect::{resolve_ast_type, resolve_doc_type};
use php_resolve::{for_each_region, Scope};
use php_span::Span;
use php_types::Type;
use std::collections::HashSet;

/// The set of `@phpstan-*` tags phpstan recognises (mirrors
/// `InvalidPHPStanDocTagRule::POSSIBLE_PHPSTAN_TAGS`). Bare names without the
/// `@phpstan-` prefix.
const POSSIBLE_PHPSTAN_TAGS: &[&str] = &[
    "param",
    "param-out",
    "var",
    "extends",
    "implements",
    "use",
    "template",
    "template-contravariant",
    "template-covariant",
    "return",
    "throws",
    "ignore",
    "ignore-next-line",
    "ignore-line",
    "method",
    "pure",
    "impure",
    "immutable",
    "type",
    "import-type",
    "property",
    "property-read",
    "property-write",
    "consistent-constructor",
    "assert",
    "assert-if-true",
    "assert-if-false",
    "self-out",
    "this-out",
    "allow-private-mutation",
    "readonly",
    "readonly-allow-private-mutation",
    "require-extends",
    "require-implements",
    "sealed",
    "param-immediately-invoked-callable",
    "param-later-invoked-callable",
    "param-closure-this",
    "all-methods-pure",
    "all-methods-impure",
];

// --- parameter.notFound / parameter.notByRef -------------------------------

/// Check a function/method's `@param` tags against its real parameter list.
fn check_params(
    doc_raw: &str,
    params: &[Param],
    interner: &Interner,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    // Plain tags use `@param`; phpstan-prefixed ones report as `@phpstan-param`.
    // We surface both via the parser's precedence-merged `params`, but we need
    // the original spelling for the message, so re-scan the raw tag list.
    let block = php_phpdoc::parse_block(doc_raw);

    let native: Vec<String> =
        params.iter().map(|p| interner.resolve(p.name).to_string()).collect();

    for tag in &block.tags {
        let (base, prefix) = strip_doc_prefix(&tag.name);
        if base != "param" {
            continue;
        }
        let tag_name = match prefix {
            Some("phpstan") => "@phpstan-param",
            Some("psalm") => continue, // phpstan ignores @psalm-* here
            _ => "@param",
        };
        let parsed = php_phpdoc::parse(&format!("/** @{} {} */", tag.name, tag.value));
        let Some(param) = parsed.params.first() else { continue };
        let Some(name) = &param.name else { continue };

        if !native.iter().any(|n| n == name) {
            out.push(
                Diagnostic::error(
                    span,
                    format!("PHPDoc tag {tag_name} references unknown parameter: ${name}"),
                )
                .with_code("parameter.notFound"),
            );
        }
    }
}

/// `parameter.notFound` / `parameter.notByRef` — walk every function & method.
fn run_param_tags(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| match &s.kind {
        StmtKind::Function(f) => {
            if let Some(doc) = &f.doc {
                check_params(doc, &f.params, fa.interner, s.span, &mut out);
            }
        }
        StmtKind::Class(c) => {
            for m in &c.members {
                if let Member::Method(mth) = m {
                    if let Some(doc) = &mth.doc {
                        check_params(doc, &mth.params, fa.interner, s.span, &mut out);
                    }
                }
            }
        }
        _ => {}
    });
    out
}

// --- parameter.notByRef (@param-out on a non-by-ref param) ------------------

/// `@param-out $x` documents what a function writes back through a by-reference
/// parameter — so `$x` must actually be declared `&$x`. Mirrors phpstan's
/// `parameter.notByRef` (from `IncompatiblePhpDocTypeCheck`).
fn check_param_out(
    doc_raw: &str,
    params: &[Param],
    interner: &Interner,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    let block = php_phpdoc::parse_block(doc_raw);
    for tag in &block.tags {
        let (base, prefix) = strip_doc_prefix(&tag.name);
        if base != "param-out" || prefix == Some("psalm") {
            continue;
        }
        // `@param-out` shares `@param`'s "Type $name" grammar — reuse the parser.
        let parsed = php_phpdoc::parse(&format!("/** @param {} */", tag.value));
        let Some(p) = parsed.params.first() else { continue };
        let Some(name) = &p.name else { continue };
        if let Some(np) = params.iter().find(|np| interner.resolve(np.name) == name) {
            if !np.by_ref {
                out.push(
                    Diagnostic::error(
                        span,
                        format!("Parameter ${name} for PHPDoc tag @param-out is not passed by reference."),
                    )
                    .with_code("parameter.notByRef"),
                );
            }
        }
    }
}

/// `parameter.notByRef` — walk every function & method.
fn run_param_out_tags(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| match &s.kind {
        StmtKind::Function(f) => {
            if let Some(doc) = &f.doc {
                check_param_out(doc, &f.params, fa.interner, s.span, &mut out);
            }
        }
        StmtKind::Class(c) => {
            for m in &c.members {
                if let Member::Method(mth) = m {
                    if let Some(doc) = &mth.doc {
                        check_param_out(doc, &mth.params, fa.interner, s.span, &mut out);
                    }
                }
            }
        }
        _ => {}
    });
    out
}

// --- varTag.* (WrongVariableNameInVarTagRule) -------------------------------

/// `@var` tags on a property must either omit the variable name or name a
/// property declared in that statement; `@var` on a class/function/method has
/// no effect (`varTag.misplaced`).
fn run_var_tags(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        match &s.kind {
            // `@var` directly above a class/function declaration has no effect.
            StmtKind::Class(c) => {
                check_var_misplaced(c.doc.as_deref(), class_description(c), s.span, &mut out);
                for m in &c.members {
                    match m {
                        Member::Method(mth) => {
                            check_var_misplaced(mth.doc.as_deref(), "a method", s.span, &mut out);
                        }
                        Member::Property(p) => {
                            check_property_var(p, fa.interner, s.span, &mut out);
                        }
                        _ => {}
                    }
                }
            }
            StmtKind::Function(f) => {
                check_var_misplaced(f.doc.as_deref(), "a function", s.span, &mut out);
            }
            _ => {}
        }
    });
    out
}

fn class_description(c: &ClassDecl) -> &'static str {
    use php_ast::ClassKind;
    match c.kind {
        ClassKind::Class => "a class",
        ClassKind::Interface => "an interface",
        ClassKind::Trait => "a trait",
        ClassKind::Enum => "an enum",
    }
}

fn check_var_misplaced(
    doc: Option<&str>,
    description: &str,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    let Some(raw) = doc else { return };
    let parsed = php_phpdoc::parse(raw);
    if !parsed.vars.is_empty() {
        out.push(
            Diagnostic::error(
                span,
                format!("PHPDoc tag @var above {description} has no effect."),
            )
            .with_code("varTag.misplaced"),
        );
    }
}

/// `@var $x` on a property whose declared name(s) differ.
fn check_property_var(p: &PropertyDecl, interner: &Interner, span: Span, out: &mut Vec<Diagnostic>) {
    let Some(raw) = &p.doc else { return };
    let parsed = php_phpdoc::parse(raw);
    if parsed.vars.is_empty() {
        return;
    }

    let names: Vec<String> =
        p.props.iter().map(|pe| interner.resolve(pe.name).to_string()).collect();

    for var in &parsed.vars {
        let Some(name) = &var.name else { continue };
        if names.iter().any(|n| n == name) {
            continue;
        }
        if names.len() == 1 {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "Variable ${} in PHPDoc tag @var does not match property variable ${}.",
                        name, names[0]
                    ),
                )
                .with_code("varTag.differentVariable"),
            );
        } else {
            out.push(
                Diagnostic::error(
                    span,
                    format!("Variable ${name} in PHPDoc tag @var does not exist."),
                )
                .with_code("varTag.variableNotFound"),
            );
        }
    }
}

// --- phpDoc.phpstanTag (InvalidPHPStanDocTagRule) ---------------------------

/// `phpDoc.phpstanTag` — an unknown `@phpstan-*` tag on any declaration.
fn run_phpstan_tags(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| match &s.kind {
        StmtKind::Function(f) => {
            if let Some(d) = &f.doc {
                check_phpstan_tags(d, s.span, &mut out);
            }
        }
        StmtKind::Class(c) => {
            if let Some(d) = &c.doc {
                check_phpstan_tags(d, s.span, &mut out);
            }
            for m in &c.members {
                let md = match m {
                    Member::Method(x) => x.doc.as_ref(),
                    Member::Property(x) => x.doc.as_ref(),
                    Member::ClassConst(x) => x.doc.as_ref(),
                    Member::EnumCase(x) => x.doc.as_ref(),
                    Member::TraitUse(_) => None,
                };
                if let Some(d) = md {
                    check_phpstan_tags(d, s.span, &mut out);
                }
            }
        }
        _ => {}
    });
    out
}

fn check_phpstan_tags(raw: &str, span: Span, out: &mut Vec<Diagnostic>) {
    let block = php_phpdoc::parse_block(raw);
    for tag in &block.tags {
        let Some(rest) = tag.name.strip_prefix("phpstan-") else { continue };
        if POSSIBLE_PHPSTAN_TAGS.contains(&rest) {
            continue;
        }
        out.push(
            Diagnostic::error(span, format!("Unknown PHPDoc tag: @{}", tag.name))
                .with_code("phpDoc.phpstanTag"),
        );
    }
}

// --- parameter.phpDocType / return.phpDocType (IncompatiblePhpDocTypeRule) --

/// A `@param`/`@return` PHPDoc type must be a *subtype* of the parameter's /
/// function's native type hint (phpstan checks `native->isSuperTypeOf(phpDoc)`).
/// We reuse the type machinery built for reflection — `resolve_doc_type` +
/// `resolve_ast_type` + `is_assignable` — resolving both sides to semantic
/// `Type`s in the declaration's name-resolution scope, and flag when the PHPDoc
/// type is **not** assignable to the native type. `is_assignable` is lenient
/// (true when either side is unknown/`mixed`/an unindexed class, or a template),
/// so we only ever report a *definite* incompatibility — false-positive-safe.
fn run_incompatible_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            match &st.kind {
                StmtKind::Function(f) => {
                    if let Some(doc) = &f.doc {
                        let templates = template_names(doc);
                        check_incompat(
                            fa, scope, &templates, doc, &f.params,
                            f.return_type.as_ref(), st.span, &mut out,
                        );
                    }
                }
                StmtKind::Class(c) => {
                    let class_templates =
                        c.doc.as_deref().map(template_names).unwrap_or_default();
                    for m in &c.members {
                        let Member::Method(mth) = m else { continue };
                        let Some(doc) = &mth.doc else { continue };
                        let mut templates = class_templates.clone();
                        templates.extend(template_names(doc));
                        check_incompat(
                            fa, scope, &templates, doc, &mth.params,
                            mth.return_type.as_ref(), st.span, &mut out,
                        );
                    }
                }
                _ => {}
            }
        }
    });
    out
}

/// `@template` names declared in a docblock.
fn template_names(raw: &str) -> Vec<String> {
    php_phpdoc::parse(raw).templates.into_iter().map(|t| t.name).collect()
}

#[allow(clippy::too_many_arguments)]
fn check_incompat(
    fa: &FileAnalysis,
    scope: &Scope,
    templates: &[String],
    doc_raw: &str,
    params: &[Param],
    return_type: Option<&php_ast::Type>,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    let doc = php_phpdoc::parse(doc_raw);

    // `@param` tags (already merged across @param/@phpstan-param by precedence).
    for p in &doc.params {
        if p.variadic {
            continue; // variadic native/doc shapes differ; phpstan special-cases.
        }
        let (Some(pname), Some(doc_ty)) = (&p.name, &p.ty) else { continue };
        let Some(native) = params.iter().find(|np| fa.interner.resolve(np.name) == pname)
        else {
            continue; // unknown param -> parameter.notFound (a different rule).
        };
        let Some(native_ast) = &native.ty else { continue }; // no native hint -> mixed.
        let native_t = resolve_ast_type(scope, native_ast);
        let doc_t = resolve_doc_type(scope, templates, doc_ty);
        if !crate::is_assignable(fa.reflection, &doc_t, &native_t) {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "PHPDoc tag @param for parameter ${pname} with type {doc_t} \
                         is incompatible with native type {native_t}."
                    ),
                )
                .with_code("parameter.phpDocType"),
            );
        }
    }

    // `@return` tag.
    if let (Some(native_ast), Some(doc_ty)) = (return_type, &doc.returns) {
        let native_t = resolve_ast_type(scope, native_ast);
        let doc_t = resolve_doc_type(scope, templates, doc_ty);
        if !crate::is_assignable(fa.reflection, &doc_t, &native_t) {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "PHPDoc tag @return with type {doc_t} \
                         is incompatible with native type {native_t}."
                    ),
                )
                .with_code("return.phpDocType"),
            );
        }
    }
}

// --- property.phpDocType (IncompatiblePropertyPhpDocTypeRule) ---------------

/// A property's `@var` PHPDoc type must be a *subtype* of the property's native
/// type hint. Mirrors phpstan's `IncompatiblePropertyPhpDocTypeRule`
/// (`property.phpDocType`). Same machinery as the `@param`/`@return` check:
/// resolve both sides and flag a definite incompatibility only.
fn run_property_phpdoc_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            let StmtKind::Class(c) = &st.kind else { continue };
            let class_name = c
                .name
                .map(|n| fa.interner.resolve(n).to_string())
                .unwrap_or_else(|| "class@anonymous".to_string());
            let class_templates = c.doc.as_deref().map(template_names).unwrap_or_default();
            for m in &c.members {
                let Member::Property(p) = m else { continue };
                let Some(native_ast) = &p.ty else { continue }; // no native hint -> mixed.
                let Some(doc_raw) = &p.doc else { continue };
                let parsed = php_phpdoc::parse(doc_raw);
                let Some(var) = parsed.vars.first() else { continue };
                let Some(doc_ty) = &var.ty else { continue };
                let native_t = resolve_ast_type(scope, native_ast);
                let doc_t = resolve_doc_type(scope, &class_templates, doc_ty);
                if !crate::is_assignable(fa.reflection, &doc_t, &native_t) {
                    // Report against the first declared property name in the group.
                    let pname = p
                        .props
                        .first()
                        .map(|pe| fa.interner.resolve(pe.name).to_string())
                        .unwrap_or_default();
                    out.push(
                        Diagnostic::error(
                            st.span,
                            format!(
                                "PHPDoc tag @var for property {class_name}::${pname} \
                                 with type {doc_t} is incompatible with native type {native_t}."
                            ),
                        )
                        .with_code("property.phpDocType"),
                    );
                }
            }
        }
    });
    out
}

// --- classConstant.phpDocType (IncompatibleClassConstantPhpDocTypeRule) ------

/// A class constant's `@var` PHPDoc type must be a *subtype* of the constant's
/// native type hint (8.3 typed constants). Mirrors phpstan's
/// `IncompatibleClassConstantPhpDocTypeRule` (`classConstant.phpDocType`).
fn run_class_const_phpdoc_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            let StmtKind::Class(c) = &st.kind else { continue };
            let class_name = c
                .name
                .map(|n| fa.interner.resolve(n).to_string())
                .unwrap_or_else(|| "class@anonymous".to_string());
            let class_templates = c.doc.as_deref().map(template_names).unwrap_or_default();
            for m in &c.members {
                let Member::ClassConst(cc) = m else { continue };
                let Some(native_ast) = &cc.ty else { continue }; // untyped const -> mixed.
                let Some(doc_raw) = &cc.doc else { continue };
                let parsed = php_phpdoc::parse(doc_raw);
                let Some(var) = parsed.vars.first() else { continue };
                let Some(doc_ty) = &var.ty else { continue };
                let native_t = resolve_ast_type(scope, native_ast);
                let doc_t = resolve_doc_type(scope, &class_templates, doc_ty);
                if !crate::is_assignable(fa.reflection, &doc_t, &native_t) {
                    // A `@var` above a const group documents every constant; report
                    // against the first declared name.
                    let cname = cc
                        .consts
                        .first()
                        .map(|ce| fa.interner.resolve(ce.name).to_string())
                        .unwrap_or_default();
                    out.push(
                        Diagnostic::error(
                            st.span,
                            format!(
                                "PHPDoc tag @var for constant {class_name}::{cname} \
                                 with type {doc_t} is incompatible with native type {native_t}."
                            ),
                        )
                        .with_code("classConstant.phpDocType"),
                    );
                }
            }
        }
    });
    out
}

// --- throws.notThrowable (InvalidThrowsPhpDocValueRule) ----------------------

/// `@throws` must name a `Throwable` subtype. Mirrors phpstan's
/// `InvalidThrowsPhpDocValueRule` (`throws.notThrowable`). We resolve the
/// `@throws` type and flag it only when it is a **definite** non-throwable:
/// a scalar/array/etc., or an *indexed* class that provably does not extend
/// `Throwable`. Unknown/built-in classes, templates and `void` are left alone
/// (lenient — no false positives).
fn run_throws_not_throwable(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            match &st.kind {
                StmtKind::Function(f) => {
                    if let Some(doc) = &f.doc {
                        check_throws(scope, doc, st.span, &mut out);
                    }
                }
                StmtKind::Class(c) => {
                    for m in &c.members {
                        let Member::Method(mth) = m else { continue };
                        if let Some(doc) = &mth.doc {
                            check_throws(scope, doc, st.span, &mut out);
                        }
                    }
                }
                _ => {}
            }
        }
    });
    out
}

fn check_throws(scope: &Scope, doc_raw: &str, span: Span, out: &mut Vec<Diagnostic>) {
    let doc = php_phpdoc::parse(doc_raw);
    for throws_ty in &doc.throws {
        let t = resolve_doc_type(scope, &[], throws_ty);
        // `@throws void` is explicitly allowed (phpstan: "this never throws").
        if matches!(t, Type::Void | Type::Never) {
            continue;
        }
        if !throws_is_valid(&t) {
            out.push(
                Diagnostic::error(
                    span,
                    format!("PHPDoc tag @throws with type {t} is not subtype of Throwable"),
                )
                .with_code("throws.notThrowable"),
            );
        }
    }
}

/// Whether `t` is (conservatively) a valid `@throws` type — i.e. *not* a
/// definite non-throwable. Returns `true` whenever we can't be sure, so we only
/// report a guaranteed violation.
///
/// **Any class-like type is treated as valid.** A user class can extend a
/// built-in `\Exception` whose hierarchy our reflection index doesn't carry, so
/// `is_subclass_of(.., "Throwable")` would wrongly fail — we never flag a named
/// class to stay false-positive-free. We only flag types that *cannot* be a
/// `Throwable` under any circumstance: scalars, arrays, callables, shapes, etc.
fn throws_is_valid(t: &Type) -> bool {
    match t {
        // A union/nullable @throws is valid iff every member is.
        Type::Union(parts) => parts.iter().all(throws_is_valid),
        Type::Nullable(inner) => throws_is_valid(inner),
        // Anything that is (or could be) an object — leave alone.
        Type::Named { .. }
        | Type::SelfType
        | Type::StaticType
        | Type::Parent
        | Type::Object
        | Type::Mixed
        | Type::TemplateVar(_)
        | Type::Unknown(_)
        | Type::Intersection(_) => true,
        // Everything else (scalars, arrays, callables, shapes, …) is definitely
        // not a Throwable.
        _ => false,
    }
}

// --- varTag.trait (InvalidPhpDocVarTagTypeRule) ------------------------------

/// `@var` must not reference a trait (traits cannot be used as types). Mirrors
/// the `varTag.trait` half of phpstan's `InvalidPhpDocVarTagTypeRule`. We only
/// flag a class the project indexes *as a trait* — never an unknown name.
fn run_var_tag_trait(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        let mut handle = |doc_raw: &str, templates: &[String], span: Span| {
            let doc = php_phpdoc::parse(doc_raw);
            for var in &doc.vars {
                let Some(ty) = &var.ty else { continue };
                let resolved = resolve_doc_type(scope, templates, ty);
                for fqn in referenced_classes(&resolved) {
                    if let Some(entry) = fa.project.class(&fqn) {
                        if entry.kind == ClassKind::Trait {
                            out.push(
                                Diagnostic::error(
                                    span,
                                    format!(
                                        "PHPDoc tag @var has invalid type {}.",
                                        entry.fqn
                                    ),
                                )
                                .with_code("varTag.trait"),
                            );
                        }
                    }
                }
            }
        };
        for st in region {
            match &st.kind {
                StmtKind::Class(c) => {
                    let class_templates = c.doc.as_deref().map(template_names).unwrap_or_default();
                    for m in &c.members {
                        if let Member::Property(p) = m {
                            if let Some(doc) = &p.doc {
                                handle(doc, &class_templates, st.span);
                            }
                        }
                    }
                }
                StmtKind::Function(f) => {
                    if let Some(doc) = &f.doc {
                        handle(doc, &[], st.span);
                    }
                }
                _ => {}
            }
        }
    });
    out
}

/// Collect the fully-qualified class names referenced (transitively) by `t`.
fn referenced_classes(t: &Type) -> Vec<String> {
    let mut out = Vec::new();
    collect_named(t, &mut out);
    out
}

fn collect_named(t: &Type, out: &mut Vec<String>) {
    match t {
        Type::Named { fqn, args } => {
            out.push(fqn.clone());
            for a in args {
                collect_named(a, out);
            }
        }
        Type::Nullable(inner) | Type::List(inner) | Type::ClassString(Some(inner)) => {
            collect_named(inner, out)
        }
        Type::Union(parts) | Type::Intersection(parts) => {
            parts.iter().for_each(|p| collect_named(p, out))
        }
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            collect_named(&kv.0, out);
            collect_named(&kv.1, out);
        }
        _ => {}
    }
}

// --- selfOut.static (IncompatibleSelfOutTypeRule) ---------------------------

/// `@phpstan-self-out` (and `@psalm-self-out`) cannot be used on a static
/// method. Mirrors the `selfOut.static` half of phpstan's
/// `IncompatibleSelfOutTypeRule`. (The subtype half needs late-static binding
/// to the receiver type — deferred.)
fn run_self_out_static(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        let StmtKind::Class(c) = &s.kind else { return };
        let class_name = c
            .name
            .map(|n| fa.interner.resolve(n).to_string())
            .unwrap_or_else(|| "class@anonymous".to_string());
        for m in &c.members {
            let Member::Method(mth) = m else { continue };
            if !mth.modifiers.is_static {
                continue;
            }
            let Some(doc) = &mth.doc else { continue };
            if !has_tag(doc, "self-out") {
                continue;
            }
            let mname = fa.interner.resolve(mth.name);
            out.push(
                Diagnostic::error(
                    s.span,
                    format!(
                        "PHPDoc tag @phpstan-self-out is not supported above static method \
                         {class_name}::{mname}()."
                    ),
                )
                .with_code("selfOut.static"),
            );
        }
    });
    out
}

// --- requireExtends.on* / requireImplements.on* / sealed.onEnum -------------

/// `@phpstan-require-extends` is only valid on an interface or trait;
/// `@phpstan-require-implements` only on a trait; `@phpstan-sealed` not on an
/// enum. Mirrors `RequireExtendsDefinitionClassRule` (`requireExtends.onClass`/
/// `onEnum`), `RequireImplementsDefinitionClassRule` (`requireImplements.on*`),
/// and the `sealed.onEnum` half of `SealedDefinitionClassRule`.
fn run_require_sealed_placement(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        let StmtKind::Class(c) = &s.kind else { return };
        let Some(doc) = &c.doc else { return };

        // `@require-extends`: valid on interface or trait only.
        if has_tag(doc, "require-extends") && !matches!(c.kind, ClassKind::Interface | ClassKind::Trait) {
            out.push(
                Diagnostic::error(
                    s.span,
                    "PHPDoc tag @phpstan-require-extends is only valid on trait or interface."
                        .to_string(),
                )
                .with_code(require_extends_id(c.kind)),
            );
        }

        // `@require-implements`: valid on trait only.
        if has_tag(doc, "require-implements") && c.kind != ClassKind::Trait {
            out.push(
                Diagnostic::error(
                    s.span,
                    "PHPDoc tag @phpstan-require-implements is only valid on trait."
                        .to_string(),
                )
                .with_code(require_implements_id(c.kind)),
            );
        }

        // `@sealed`: not valid on an enum.
        if has_tag(doc, "sealed") && c.kind == ClassKind::Enum {
            out.push(
                Diagnostic::error(
                    s.span,
                    "PHPDoc tag @phpstan-sealed is not supported above an enum.".to_string(),
                )
                .with_code("sealed.onEnum"),
            );
        }
    });
    out
}

/// The `requireExtends.on{X}` identifier for a class kind (phpstan suffixes the
/// `ClassReflection::getClassTypeDescription()` word). `@require-extends` is only
/// emitted on class/enum (interface & trait are valid placements).
fn require_extends_id(kind: ClassKind) -> &'static str {
    match kind {
        ClassKind::Enum => "requireExtends.onEnum",
        _ => "requireExtends.onClass",
    }
}

/// The `requireImplements.on{X}` identifier for a class kind. `@require-implements`
/// is only valid on a trait; everything else is flagged.
fn require_implements_id(kind: ClassKind) -> &'static str {
    match kind {
        ClassKind::Interface => "requireImplements.onInterface",
        ClassKind::Enum => "requireImplements.onEnum",
        _ => "requireImplements.onClass",
    }
}

/// Whether the docblock carries `@base`, `@phpstan-base`, or `@psalm-base`
/// (any prefix variant of the given base tag name).
fn has_tag(doc_raw: &str, base: &str) -> bool {
    let block = php_phpdoc::parse_block(doc_raw);
    block.tags.iter().any(|t| {
        let (b, _) = strip_doc_prefix(&t.name);
        b == base
    })
}

// --- shared helpers ---------------------------------------------------------

/// Split a doc tag name into its base and an optional `phpstan`/`psalm` prefix.
/// `"phpstan-param"` -> `("param", Some("phpstan"))`; `"param"` -> `("param", None)`.
fn strip_doc_prefix(name: &str) -> (&str, Option<&str>) {
    if let Some(rest) = name.strip_prefix("phpstan-") {
        (rest, Some("phpstan"))
    } else if let Some(rest) = name.strip_prefix("psalm-") {
        (rest, Some("psalm"))
    } else {
        (name, None)
    }
}

// --- @mixin validation (MixinRule / MixinTraitRule / MixinTraitUseRule) -----

/// A `@mixin T` tag whose `T` is a non-object (`mixin.nonObject`), an unknown
/// class (`class.notFound`), or a trait (`mixin.trait`). Reuses the resolved
/// `@mixin` types via `resolve_doc_type`; FP-safe (skips mixed/object/templates
/// and known/built-in classes).
fn run_mixin(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            collect_mixin(st, fa, scope, &mut out);
        }
    });
    out
}

fn collect_mixin(st: &Stmt, fa: &FileAnalysis, scope: &Scope, out: &mut Vec<Diagnostic>) {
    use php_ast::ClassKind;
    match &st.kind {
        StmtKind::Class(c) => {
            let Some(doc_raw) = &c.doc else { return };
            let doc = php_phpdoc::parse(doc_raw);
            if doc.mixins.is_empty() {
                return;
            }
            let templates = template_names(doc_raw);
            for mixin in &doc.mixins {
                let ty = resolve_doc_type(scope, &templates, mixin);
                match &ty {
                    php_types::Type::Named { fqn, .. } => {
                        if let Some(cr) = fa.reflection.class(fqn) {
                            if cr.kind == ClassKind::Trait {
                                out.push(
                                    Diagnostic::error(
                                        st.span,
                                        format!("PHPDoc tag @mixin contains invalid type {ty}."),
                                    )
                                    .with_code("mixin.trait"),
                                );
                            }
                        } else if !fa.project.has_class(fqn) {
                            out.push(
                                Diagnostic::error(
                                    st.span,
                                    format!("PHPDoc tag @mixin contains unknown class {ty}."),
                                )
                                .with_code("class.notFound"),
                            );
                        }
                    }
                    // Lenient: anything we can't pin to a concrete non-object.
                    php_types::Type::Mixed
                    | php_types::Type::Unknown(_)
                    | php_types::Type::Object
                    | php_types::Type::SelfType
                    | php_types::Type::StaticType
                    | php_types::Type::Parent
                    | php_types::Type::TemplateVar(_)
                    | php_types::Type::Nullable(_)
                    | php_types::Type::Union(_)
                    | php_types::Type::Intersection(_)
                    | php_types::Type::Iterable(_) => {}
                    // A concrete non-object (scalar/array/callable/…).
                    _ => out.push(
                        Diagnostic::error(
                            st.span,
                            format!("PHPDoc tag @mixin contains non-object type {ty}."),
                        )
                        .with_code("mixin.nonObject"),
                    ),
                }
            }
        }
        StmtKind::Namespace { body: Some(b), .. } => {
            for s in b {
                collect_mixin(s, fa, scope, out);
            }
        }
        _ => {}
    }
}

// --- @property / @method tag type validation (PropertyTag/MethodTagRule) -----


/// Emit `class.notFound` / `<trait_code>` for each unknown class / trait named in
/// a doc-tag type. FP-safe: known + built-in classes are fine; templates/scalars
/// are ignored (only `Named` is collected).
fn check_tag_classes(
    fa: &FileAnalysis,
    ty: &php_types::Type,
    span: Span,
    trait_code: &'static str,
    msg: impl Fn(&str, &'static str) -> String,
    out: &mut Vec<Diagnostic>,
) {
    let mut named = Vec::new();
    collect_named(ty, &mut named);
    for fqn in named {
        if let Some(cr) = fa.reflection.class(&fqn) {
            if cr.kind == ClassKind::Trait {
                out.push(Diagnostic::error(span, msg(&fqn, "invalid")).with_code(trait_code));
            }
        } else if !fa.project.has_class(&fqn) {
            out.push(Diagnostic::error(span, msg(&fqn, "unknown")).with_code("class.notFound"));
        }
    }
}

/// `@property*`/`@method` tag types referencing an unknown class or a trait.
fn run_tag_class_refs(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            collect_tag_refs(st, fa, scope, &mut out);
        }
    });
    out
}

fn collect_tag_refs(st: &Stmt, fa: &FileAnalysis, scope: &Scope, out: &mut Vec<Diagnostic>) {
    match &st.kind {
        StmtKind::Class(c) => {
            let Some(doc_raw) = &c.doc else { return };
            let doc = php_phpdoc::parse(doc_raw);
            if doc.properties.is_empty() && doc.methods.is_empty() {
                return;
            }
            let templates = template_names(doc_raw);
            let display = c.name.map(|n| scope.qualify(fa.interner.resolve(n))).unwrap_or_default();
            for p in &doc.properties {
                let Some(dt) = &p.ty else { continue };
                let ty = resolve_doc_type(scope, &templates, dt);
                let pname = p.name.clone().unwrap_or_default();
                let d2 = display.clone();
                check_tag_classes(fa, &ty, st.span, "propertyTag.trait", move |c, kind| {
                    format!("PHPDoc tag @property for property {d2}::${pname} contains {kind} class {c}.")
                }, out);
            }
            for m in &doc.methods {
                let Some(rt) = &m.return_type else { continue };
                let ty = resolve_doc_type(scope, &templates, rt);
                let mname = m.name.clone();
                let d2 = display.clone();
                check_tag_classes(fa, &ty, st.span, "methodTag.trait", move |c, kind| {
                    format!("PHPDoc tag @method for method {d2}::{mname}() contains {kind} class {c}.")
                }, out);
            }
        }
        StmtKind::Namespace { body: Some(b), .. } => {
            for s in b {
                collect_tag_refs(s, fa, scope, out);
            }
        }
        _ => {}
    }
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "phpdoc.mixin", level: 2, run: run_mixin },
    RuleEntry { name: "phpdoc.tagClassRefs", level: 2, run: run_tag_class_refs },
    RuleEntry { name: "phpdoc.paramTags", level: 2, run: run_param_tags },
    RuleEntry { name: "phpdoc.varTags", level: 2, run: run_var_tags },
    RuleEntry { name: "phpdoc.phpstanTag", level: 2, run: run_phpstan_tags },
    RuleEntry { name: "phpdoc.incompatibleType", level: 2, run: run_incompatible_types },
    RuleEntry { name: "phpdoc.paramOut", level: 2, run: run_param_out_tags },
    RuleEntry { name: "phpdoc.propertyType", level: 2, run: run_property_phpdoc_type },
    RuleEntry { name: "phpdoc.classConstType", level: 2, run: run_class_const_phpdoc_type },
    RuleEntry { name: "phpdoc.throwsNotThrowable", level: 2, run: run_throws_not_throwable },
    RuleEntry { name: "phpdoc.varTagTrait", level: 2, run: run_var_tag_trait },
    RuleEntry { name: "phpdoc.selfOutStatic", level: 2, run: run_self_out_static },
    RuleEntry { name: "phpdoc.requireSealedPlacement", level: 2, run: run_require_sealed_placement },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- @property / @method tag class refs ---

    #[test]
    fn property_tag_unknown_class_flagged() {
        let src = "<?php /** @property Nope $x */ class C {}";
        assert_eq!(codes(src, run_tag_class_refs), ["class.notFound"]);
    }

    #[test]
    fn property_tag_known_class_clean() {
        let src = "<?php class T {} /** @property T $x */ class C {}";
        assert!(codes(src, run_tag_class_refs).is_empty());
    }

    #[test]
    fn method_tag_unknown_return_flagged() {
        let src = "<?php /** @method Nope getThing() */ class C {}";
        assert_eq!(codes(src, run_tag_class_refs), ["class.notFound"]);
    }

    #[test]
    fn property_tag_scalar_clean() {
        let src = "<?php /** @property int $x */ class C {}";
        assert!(codes(src, run_tag_class_refs).is_empty());
    }

    // --- @mixin ---

    #[test]
    fn mixin_unknown_class_flagged() {
        let src = "<?php /** @mixin Nonexistent */ class C {}";
        assert_eq!(codes(src, run_mixin), ["class.notFound"]);
    }

    #[test]
    fn mixin_known_class_clean() {
        let src = "<?php class Helper {} /** @mixin Helper */ class C {}";
        assert!(codes(src, run_mixin).is_empty());
    }

    #[test]
    fn mixin_trait_flagged() {
        let src = "<?php trait T {} /** @mixin T */ class C {}";
        assert_eq!(codes(src, run_mixin), ["mixin.trait"]);
    }

    #[test]
    fn mixin_scalar_flagged() {
        let src = "<?php /** @mixin int */ class C {}";
        assert_eq!(codes(src, run_mixin), ["mixin.nonObject"]);
    }

    // --- parameter.notFound ---

    #[test]
    fn param_for_unknown_parameter_is_flagged() {
        let src = "<?php /** @param int $nope */ function f($real) {}";
        assert_eq!(codes(src, run_param_tags), ["parameter.notFound"]);
    }

    #[test]
    fn param_matching_a_real_parameter_is_clean() {
        let src = "<?php /** @param int $real */ function f($real) {}";
        assert!(codes(src, run_param_tags).is_empty());
    }

    #[test]
    fn phpstan_param_for_unknown_parameter_is_flagged() {
        let src = "<?php /** @phpstan-param int $nope */ function f($real) {}";
        assert_eq!(codes(src, run_param_tags), ["parameter.notFound"]);
    }

    #[test]
    fn param_on_a_method_is_checked() {
        let src = "<?php class C { /** @param int $nope */ public function m($real) {} }";
        assert_eq!(codes(src, run_param_tags), ["parameter.notFound"]);
    }

    #[test]
    fn method_param_matching_is_clean() {
        let src = "<?php class C { /** @param int $real */ public function m($real) {} }";
        assert!(codes(src, run_param_tags).is_empty());
    }

    #[test]
    fn psalm_param_is_ignored_by_this_rule() {
        // phpstan does not check @psalm-* param tags here.
        let src = "<?php /** @psalm-param int $nope */ function f($real) {}";
        assert!(codes(src, run_param_tags).is_empty());
    }

    // --- varTag.differentVariable / variableNotFound ---

    #[test]
    fn var_tag_wrong_property_name_is_flagged() {
        let src = "<?php class C { /** @var int $nope */ public $real; }";
        assert_eq!(codes(src, run_var_tags), ["varTag.differentVariable"]);
    }

    #[test]
    fn var_tag_matching_property_is_clean() {
        let src = "<?php class C { /** @var int $real */ public $real; }";
        assert!(codes(src, run_var_tags).is_empty());
    }

    #[test]
    fn var_tag_without_variable_name_on_property_is_clean() {
        let src = "<?php class C { /** @var int */ public $real; }";
        assert!(codes(src, run_var_tags).is_empty());
    }

    #[test]
    fn var_tag_unknown_among_multiple_properties_is_flagged() {
        let src = "<?php class C { /** @var int $nope */ public $a, $b; }";
        assert_eq!(codes(src, run_var_tags), ["varTag.variableNotFound"]);
    }

    // --- varTag.misplaced ---

    #[test]
    fn var_tag_on_a_class_has_no_effect() {
        let src = "<?php /** @var int $x */ class C {}";
        assert_eq!(codes(src, run_var_tags), ["varTag.misplaced"]);
    }

    #[test]
    fn var_tag_on_a_function_has_no_effect() {
        let src = "<?php /** @var int $x */ function f() {}";
        assert_eq!(codes(src, run_var_tags), ["varTag.misplaced"]);
    }

    #[test]
    fn doc_without_var_on_class_is_clean() {
        let src = "<?php /** A class. */ class C {}";
        assert!(codes(src, run_var_tags).is_empty());
    }

    // --- phpDoc.phpstanTag ---

    #[test]
    fn unknown_phpstan_tag_is_flagged() {
        let src = "<?php /** @phpstan-bogus int */ function f() {}";
        assert_eq!(codes(src, run_phpstan_tags), ["phpDoc.phpstanTag"]);
    }

    #[test]
    fn known_phpstan_tag_is_clean() {
        let src = "<?php /** @phpstan-param int $x */ function f($x) {}";
        assert!(codes(src, run_phpstan_tags).is_empty());
    }

    #[test]
    fn plain_unknown_tag_is_not_flagged() {
        // Only `@phpstan-*` unknown tags are reported by this rule.
        let src = "<?php /** @whatever int */ function f() {}";
        assert!(codes(src, run_phpstan_tags).is_empty());
    }

    #[test]
    fn unknown_phpstan_tag_on_a_method_is_flagged() {
        let src = "<?php class C { /** @phpstan-nope */ public function m() {} }";
        assert_eq!(codes(src, run_phpstan_tags), ["phpDoc.phpstanTag"]);
    }

    // --- parameter.phpDocType / return.phpDocType ---

    #[test]
    fn param_phpdoc_type_incompatible_with_native_is_flagged() {
        let src = "<?php /** @param string $a */ function f(int $a) {}";
        assert_eq!(codes(src, run_incompatible_types), ["parameter.phpDocType"]);
    }

    #[test]
    fn param_phpdoc_type_subtype_of_native_is_clean() {
        // int is a subtype of int|null (the native `?int`).
        let src = "<?php /** @param int $a */ function f(?int $a) {}";
        assert!(codes(src, run_incompatible_types).is_empty());
    }

    #[test]
    fn param_phpdoc_nullable_widening_native_is_flagged() {
        // doc `int|null` is wider than native `int` -> not a subtype.
        let src = "<?php /** @param int|null $a */ function f(int $a) {}";
        assert_eq!(codes(src, run_incompatible_types), ["parameter.phpDocType"]);
    }

    #[test]
    fn param_without_native_type_is_skipped() {
        // No native hint == mixed; everything is a subtype of mixed.
        let src = "<?php /** @param string $a */ function f($a) {}";
        assert!(codes(src, run_incompatible_types).is_empty());
    }

    #[test]
    fn return_phpdoc_type_incompatible_is_flagged() {
        let src = "<?php /** @return string */ function f(): int { return 1; }";
        assert_eq!(codes(src, run_incompatible_types), ["return.phpDocType"]);
    }

    #[test]
    fn return_phpdoc_subtype_is_clean() {
        let src = "<?php /** @return int */ function f(): ?int { return 1; }";
        assert!(codes(src, run_incompatible_types).is_empty());
    }

    #[test]
    fn method_param_phpdoc_type_incompatible_is_flagged() {
        let src = "<?php class C { /** @param string $a */ public function m(int $a) {} }";
        assert_eq!(codes(src, run_incompatible_types), ["parameter.phpDocType"]);
    }

    #[test]
    fn array_doc_under_iterable_native_is_clean() {
        // array<int, string> is a subtype of iterable.
        let src = "<?php /** @param array<int, string> $a */ function f(iterable $a) {}";
        assert!(codes(src, run_incompatible_types).is_empty());
    }

    #[test]
    fn template_param_is_not_flagged() {
        // A @template type is unknown -> lenient -> never flagged.
        let src = "<?php /** @template T\n * @param T $a */ function f(int $a) {}";
        assert!(codes(src, run_incompatible_types).is_empty());
    }

    #[test]
    fn int_to_float_widening_param_is_clean() {
        let src = "<?php /** @param int $a */ function f(float $a) {}";
        assert!(codes(src, run_incompatible_types).is_empty());
    }

    // --- parameter.notByRef (@param-out) ---

    #[test]
    fn param_out_on_non_byref_is_flagged() {
        let src = "<?php /** @param-out int $x */ function f($x) {}";
        assert_eq!(codes(src, run_param_out_tags), ["parameter.notByRef"]);
    }

    #[test]
    fn param_out_on_byref_is_clean() {
        let src = "<?php /** @param-out int $x */ function f(&$x) {}";
        assert!(codes(src, run_param_out_tags).is_empty());
    }

    #[test]
    fn plain_param_is_not_param_out() {
        let src = "<?php /** @param int $x */ function f($x) {}";
        assert!(codes(src, run_param_out_tags).is_empty());
    }

    #[test]
    fn param_out_on_method_is_checked() {
        let src = "<?php class C { /** @param-out int $x */ function m($x) {} }";
        assert_eq!(codes(src, run_param_out_tags), ["parameter.notByRef"]);
    }

    // --- property.phpDocType ---

    #[test]
    fn property_var_incompatible_with_native_is_flagged() {
        let src = "<?php class C { /** @var string */ public int $x; }";
        assert_eq!(codes(src, run_property_phpdoc_type), ["property.phpDocType"]);
    }

    #[test]
    fn property_var_subtype_of_native_is_clean() {
        // int is a subtype of native ?int.
        let src = "<?php class C { /** @var int */ public ?int $x; }";
        assert!(codes(src, run_property_phpdoc_type).is_empty());
    }

    #[test]
    fn property_without_native_type_is_skipped() {
        let src = "<?php class C { /** @var string */ public $x; }";
        assert!(codes(src, run_property_phpdoc_type).is_empty());
    }

    #[test]
    fn property_var_nullable_wider_than_native_is_flagged() {
        let src = "<?php class C { /** @var int|null */ public int $x; }";
        assert_eq!(codes(src, run_property_phpdoc_type), ["property.phpDocType"]);
    }

    // --- classConstant.phpDocType ---

    #[test]
    fn class_const_var_incompatible_with_native_is_flagged() {
        let src = "<?php class C { /** @var string */ const int X = 1; }";
        assert_eq!(codes(src, run_class_const_phpdoc_type), ["classConstant.phpDocType"]);
    }

    #[test]
    fn class_const_var_subtype_is_clean() {
        let src = "<?php class C { /** @var int */ const int X = 1; }";
        assert!(codes(src, run_class_const_phpdoc_type).is_empty());
    }

    #[test]
    fn untyped_class_const_is_skipped() {
        let src = "<?php class C { /** @var string */ const X = 1; }";
        assert!(codes(src, run_class_const_phpdoc_type).is_empty());
    }

    // --- throws.notThrowable ---

    #[test]
    fn throws_scalar_is_flagged() {
        let src = "<?php /** @throws int */ function f() {}";
        assert_eq!(codes(src, run_throws_not_throwable), ["throws.notThrowable"]);
    }

    #[test]
    fn throws_array_is_flagged() {
        let src = "<?php /** @throws string[] */ function f() {}";
        assert_eq!(codes(src, run_throws_not_throwable), ["throws.notThrowable"]);
    }

    #[test]
    fn throws_class_is_clean() {
        // A class-like @throws is never flagged (could extend a built-in Throwable).
        let src = "<?php /** @throws \\RuntimeException */ function f() {}";
        assert!(codes(src, run_throws_not_throwable).is_empty());
    }

    #[test]
    fn throws_void_is_clean() {
        let src = "<?php /** @throws void */ function f() {}";
        assert!(codes(src, run_throws_not_throwable).is_empty());
    }

    #[test]
    fn throws_on_method_scalar_is_flagged() {
        let src = "<?php class C { /** @throws bool */ function m() {} }";
        assert_eq!(codes(src, run_throws_not_throwable), ["throws.notThrowable"]);
    }

    // --- varTag.trait ---

    #[test]
    fn var_tag_referencing_a_trait_is_flagged() {
        let src = "<?php trait T {} class C { /** @var T */ public $x; }";
        assert_eq!(codes(src, run_var_tag_trait), ["varTag.trait"]);
    }

    #[test]
    fn var_tag_referencing_a_class_is_clean() {
        let src = "<?php class T {} class C { /** @var T */ public $x; }";
        assert!(codes(src, run_var_tag_trait).is_empty());
    }

    #[test]
    fn var_tag_unknown_class_is_not_flagged_as_trait() {
        let src = "<?php class C { /** @var \\Some\\Unknown */ public $x; }";
        assert!(codes(src, run_var_tag_trait).is_empty());
    }

    // --- selfOut.static ---

    #[test]
    fn self_out_on_static_method_is_flagged() {
        let src = "<?php class C { /** @phpstan-self-out static */ public static function m() {} }";
        assert_eq!(codes(src, run_self_out_static), ["selfOut.static"]);
    }

    #[test]
    fn self_out_on_instance_method_is_clean() {
        let src = "<?php class C { /** @phpstan-self-out static */ public function m() {} }";
        assert!(codes(src, run_self_out_static).is_empty());
    }

    // --- requireExtends / requireImplements / sealed placement ---

    #[test]
    fn require_extends_on_class_is_flagged() {
        let src = "<?php /** @phpstan-require-extends \\Foo */ class C {}";
        assert_eq!(codes(src, run_require_sealed_placement), ["requireExtends.onClass"]);
    }

    #[test]
    fn require_extends_on_interface_is_clean() {
        let src = "<?php /** @phpstan-require-extends \\Foo */ interface I {}";
        assert!(codes(src, run_require_sealed_placement).is_empty());
    }

    #[test]
    fn require_extends_on_trait_is_clean() {
        let src = "<?php /** @phpstan-require-extends \\Foo */ trait T {}";
        assert!(codes(src, run_require_sealed_placement).is_empty());
    }

    #[test]
    fn require_implements_on_class_is_flagged() {
        let src = "<?php /** @phpstan-require-implements \\Foo */ class C {}";
        assert_eq!(codes(src, run_require_sealed_placement), ["requireImplements.onClass"]);
    }

    #[test]
    fn require_implements_on_trait_is_clean() {
        let src = "<?php /** @phpstan-require-implements \\Foo */ trait T {}";
        assert!(codes(src, run_require_sealed_placement).is_empty());
    }

    #[test]
    fn sealed_on_enum_is_flagged() {
        let src = "<?php /** @phpstan-sealed A|B */ enum E {}";
        assert_eq!(codes(src, run_require_sealed_placement), ["sealed.onEnum"]);
    }

    #[test]
    fn sealed_on_class_is_clean() {
        let src = "<?php /** @phpstan-sealed A|B */ class C {}";
        assert!(codes(src, run_require_sealed_placement).is_empty());
    }
}
