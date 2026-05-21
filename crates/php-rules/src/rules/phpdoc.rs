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
//! - `phpDoc.parseError`      — a malformed value in a type-bearing PHPDoc tag
//!   (`InvalidPhpDocTagValueRule`), limited to cases our PHPDoc parser can
//!   identify without PHPStan's exception-rich parser.
//! - `assert.*` / `conditionalType.*` — conservative syntactic + definite
//!   scalar checks for `@phpstan-assert*` and conditional return types.
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
//! - `selfOut.type` — a `@phpstan-self-out` type that is definitely not a
//!   subtype of the declaring class.
//! - `requireExtends.*` / `requireImplements.*` / `sealed.*` — structural
//!   validation for `@phpstan-require-extends`, `@phpstan-require-implements`,
//!   and `@phpstan-sealed` definitions (placement, duplicate/non-object tags,
//!   unknown/wrong-kind targets where we can prove them from the project index).
//!
//! Deferred (need machinery our pipeline doesn't yet expose):
//! - `InvalidPhpDocTagValueRule` (`phpDoc.parseError`): the safe subset is
//!   implemented, but phpstan reports the *parse exception* from its own PHPDoc
//!   parser. Our `php_phpdoc` parser is intentionally lenient, so we cannot
//!   reproduce every phpstan parse error or its exact wording.
//! - `InvalidPhpDocVarTagTypeRule` (`class.notFound`): we deliberately do NOT
//!   flag unknown classes inside `@var` — our builtin/stub class coverage isn't
//!   complete enough to avoid false positives on namespaced/relative names. The
//!   `varTag.trait` half (a definite indexed trait) is done above.
//! - `missingType.iterableValue` / `missingType.generics`: "missing value type"
//!   checks are a separate strictness mode (level 6) — out of this category's
//!   level-2 scope.
//! - The deeper assert / conditional-return branches (generic validation,
//!   expression-property validation, and param-out/closure-this conditionals)
//!   need richer PHPDoc reflection and expression typing.

use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{
    ClassDecl, ClassKind, Expr, ExprKind, Member, Name, NameFq, Param, PropertyDecl, PropertyHook,
    Stmt, StmtKind,
};
use php_diagnostics::Diagnostic;
use php_intern::Interner;
use php_phpdoc::DocType;
use php_reflect::{resolve_ast_type, resolve_doc_type};
use php_resolve::{for_each_region, Resolution, Scope};
use php_span::Span;
use php_types::Type;
use std::collections::HashMap;

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

    let native: Vec<String> = params
        .iter()
        .map(|p| interner.resolve(p.name).to_string())
        .collect();

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
        let Some(param) = parsed.params.first() else {
            continue;
        };
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
        let Some(p) = parsed.params.first() else {
            continue;
        };
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

// --- paramImmediatelyInvokedCallable.* / paramLaterInvokedCallable.* -------

/// `@param-immediately-invoked-callable` / `@param-later-invoked-callable`
/// must reference a real parameter whose native type can be callable. This is
/// intentionally narrower than phpstan: strings/arrays/objects/classes are
/// skipped because PHP can treat some runtime values of those types as callable.
fn check_param_invoked_callable_tags(
    doc_raw: &str,
    params: &[Param],
    interner: &Interner,
    scope: &Scope,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    let block = php_phpdoc::parse_block(doc_raw);
    for tag in &block.tags {
        let (base, prefix) = strip_doc_prefix(&tag.name);
        let Some(immediately) = (match base {
            "param-immediately-invoked-callable" => Some(true),
            "param-later-invoked-callable" => Some(false),
            _ => None,
        }) else {
            continue;
        };
        if prefix == Some("psalm") {
            continue;
        }

        let Some(name) = parse_callable_tag_parameter(&tag.value) else {
            continue;
        };
        let tag_name = if prefix == Some("phpstan") {
            format!("@phpstan-{base}")
        } else {
            format!("@{base}")
        };

        let Some(native) = params.iter().find(|p| interner.resolve(p.name) == name) else {
            out.push(
                Diagnostic::error(
                    span,
                    format!("PHPDoc tag {tag_name} references unknown parameter: ${name}"),
                )
                .with_code("parameter.notFound"),
            );
            continue;
        };
        let Some(native_ast) = &native.ty else {
            continue;
        };
        let native_ty = resolve_ast_type(scope, native_ast);
        if definitely_not_callable_type(&native_ty) {
            let code = if immediately {
                "paramImmediatelyInvokedCallable.nonCallable"
            } else {
                "paramLaterInvokedCallable.nonCallable"
            };
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "PHPDoc tag {tag_name} is for parameter ${name} with non-callable type {native_ty}."
                    ),
                )
                .with_code(code),
            );
        }
    }
}

fn parse_callable_tag_parameter(value: &str) -> Option<String> {
    let rest = value.trim_start().strip_prefix('$')?;
    let end = rest
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .unwrap_or(rest.len());
    (end > 0).then(|| rest[..end].to_string())
}

fn definitely_not_callable_type(t: &Type) -> bool {
    match t {
        Type::Callable(_) => false,
        Type::Nullable(inner) => {
            definitely_not_callable_type(inner) && definitely_not_callable_type(&Type::Null)
        }
        Type::Union(parts) => parts.iter().all(definitely_not_callable_type),
        Type::LiteralInt(_)
        | Type::Int
        | Type::IntRange { .. }
        | Type::Float
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Null
        | Type::Void
        | Type::Never => true,
        Type::Mixed
        | Type::ExplicitMixed
        | Type::Unknown(_)
        | Type::TemplateVar(_)
        | Type::Object
        | Type::Resource
        | Type::String
        | Type::LiteralString(_)
        | Type::Array(_)
        | Type::Iterable(_)
        | Type::List(_)
        | Type::Shape { .. }
        | Type::ClassString(_)
        | Type::Named { .. }
        | Type::SelfType
        | Type::StaticType
        | Type::Parent
        | Type::Intersection(_)
        | Type::Conditional { .. } => false,
    }
}

fn run_param_invoked_callable_tags(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            match &st.kind {
                StmtKind::Function(f) => {
                    if let Some(doc) = &f.doc {
                        check_param_invoked_callable_tags(
                            doc,
                            &f.params,
                            fa.interner,
                            scope,
                            st.span,
                            &mut out,
                        );
                    }
                }
                StmtKind::Class(c) => {
                    for m in &c.members {
                        let Member::Method(mth) = m else { continue };
                        let Some(doc) = &mth.doc else { continue };
                        check_param_invoked_callable_tags(
                            doc,
                            &mth.params,
                            fa.interner,
                            scope,
                            st.span,
                            &mut out,
                        );
                    }
                }
                _ => {}
            }
        }
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
fn check_property_var(
    p: &PropertyDecl,
    interner: &Interner,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    let Some(raw) = &p.doc else { return };
    let parsed = php_phpdoc::parse(raw);
    if parsed.vars.is_empty() {
        return;
    }

    let names: Vec<String> = p
        .props
        .iter()
        .map(|pe| interner.resolve(pe.name).to_string())
        .collect();

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
        let Some(rest) = tag.name.strip_prefix("phpstan-") else {
            continue;
        };
        if POSSIBLE_PHPSTAN_TAGS.contains(&rest) {
            continue;
        }
        out.push(
            Diagnostic::error(span, format!("Unknown PHPDoc tag: @{}", tag.name))
                .with_code("phpDoc.phpstanTag"),
        );
    }
}

// --- phpDoc.parseError (InvalidPhpDocTagValueRule, conservative subset) -----

/// `InvalidPhpDocTagValueRule` reports parser exceptions for malformed
/// type-bearing tag values. Our PHPDoc parser is intentionally lenient and does
/// not expose exception messages, so this rule only reports values that are
/// unambiguously malformed under our grammar: missing required type operands,
/// variable-first `@var`, or a value whose leading type cannot be parsed at all.
fn run_invalid_tag_values(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let Some(doc) = &s.doc {
            check_invalid_doc_values(doc, s.span, &mut out);
        }
        match &s.kind {
            StmtKind::Function(f) => {
                if let Some(doc) = &f.doc {
                    check_invalid_doc_values(doc, s.span, &mut out);
                }
            }
            StmtKind::Class(c) => {
                if let Some(doc) = &c.doc {
                    check_invalid_doc_values(doc, s.span, &mut out);
                }
                for m in &c.members {
                    let doc = match m {
                        Member::Method(x) => x.doc.as_ref(),
                        Member::Property(x) => x.doc.as_ref(),
                        Member::ClassConst(x) => x.doc.as_ref(),
                        Member::EnumCase(x) => x.doc.as_ref(),
                        Member::TraitUse(_) => None,
                    };
                    if let Some(doc) = doc {
                        check_invalid_doc_values(doc, s.span, &mut out);
                    }
                }
            }
            _ => {}
        }
    });
    out
}

fn check_invalid_doc_values(raw: &str, span: Span, out: &mut Vec<Diagnostic>) {
    let block = php_phpdoc::parse_block(raw);
    for tag in &block.tags {
        let (base, prefix) = strip_doc_prefix(&tag.name);
        // Mirrored from phpstan: phan/psalm-specific tags are not reported by
        // this rule. We still validate phpstan-prefixed tags.
        if prefix == Some("psalm") || tag.name.starts_with("phan-") {
            continue;
        }

        let invalid = match base {
            "param" | "param-out" => invalid_param_like_value(&tag.value),
            "var" => invalid_var_value(&tag.value),
            "return" | "throws" | "mixin" | "extends" | "implements" | "use"
            | "require-extends" | "require-implements" | "sealed" | "self-out" | "this-out" => {
                invalid_required_type_value(&tag.value)
            }
            "assert" | "assert-if-true" | "assert-if-false" => {
                parse_assert_value(&tag.value).is_none()
            }
            _ => false,
        };
        if invalid {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "PHPDoc tag @{} has invalid value ({}).",
                        tag.name,
                        tag.value.trim()
                    ),
                )
                .with_code("phpDoc.parseError"),
            );
        }
    }
}

fn invalid_required_type_value(value: &str) -> bool {
    let value = value.trim_start();
    value.is_empty() || php_phpdoc::parse_type_prefix(value).is_none()
}

fn invalid_param_like_value(value: &str) -> bool {
    let value = value.trim_start();
    if value.is_empty() {
        return true;
    }
    // Typeless `@param $x` is accepted by our parser and common in legacy PHPDoc;
    // do not treat it as a parse error.
    !value.starts_with('$') && php_phpdoc::parse_type_prefix(value).is_none()
}

fn invalid_var_value(value: &str) -> bool {
    let value = value.trim_start();
    value.is_empty() || value.starts_with('$') || php_phpdoc::parse_type_prefix(value).is_none()
}

// --- FunctionAssertRule / MethodAssertRule (conservative subset) ------------

#[derive(Debug)]
struct AssertDoc {
    negated: bool,
    ty: php_phpdoc::DocType,
    expr: String,
    param_name: String,
}

/// `@phpstan-assert*` / `@psalm-assert*` checks that are safe with our current
/// model: unknown asserted parameters, and scalar assertions that are definitely
/// impossible or definitely fail to narrow the parameter's declared type.
fn run_assert_tags(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            match &st.kind {
                StmtKind::Function(f) => {
                    if let Some(doc) = &f.doc {
                        let (templates, _) = template_context(scope, &[doc.as_str()]);
                        check_assert_doc(
                            fa, scope, &templates, doc, &f.params, false, st.span, &mut out,
                        );
                    }
                }
                StmtKind::Class(c) => {
                    let class_docs = c.doc.as_deref().into_iter().collect::<Vec<_>>();
                    for m in &c.members {
                        let Member::Method(mth) = m else { continue };
                        let Some(doc) = &mth.doc else { continue };
                        let mut docs = class_docs.clone();
                        docs.push(doc.as_str());
                        let (templates, _) = template_context(scope, &docs);
                        check_assert_doc(
                            fa,
                            scope,
                            &templates,
                            doc,
                            &mth.params,
                            !mth.modifiers.is_static,
                            st.span,
                            &mut out,
                        );
                    }
                }
                _ => {}
            }
        }
    });
    out
}

#[allow(clippy::too_many_arguments)]
fn check_assert_doc(
    fa: &FileAnalysis,
    scope: &Scope,
    templates: &[String],
    doc_raw: &str,
    params: &[Param],
    allow_this: bool,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    let param_types = declaration_param_types(fa, scope, templates, doc_raw, params);
    let block = php_phpdoc::parse_block(doc_raw);
    for tag in &block.tags {
        let (base, prefix) = strip_doc_prefix(&tag.name);
        if !matches!(base, "assert" | "assert-if-true" | "assert-if-false") {
            continue;
        }
        if prefix.is_none() {
            continue;
        }
        let Some(assert) = parse_assert_value(&tag.value) else {
            continue; // phpDoc.parseError owns malformed values.
        };
        let expr_ty = if assert.param_name == "this" && allow_this {
            // `$this->prop` and `$this->method()` expression validation needs
            // member lookup at the asserted expression path; skip it for now.
            if assert.expr != "$this" {
                continue;
            }
            Type::Object
        } else if let Some(ty) = param_types.get(&assert.param_name) {
            ty.clone()
        } else {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "Assert references unknown parameter ${}.",
                        assert.param_name
                    ),
                )
                .with_code("parameter.notFound"),
            );
            continue;
        };

        if !doc_type_relation_safe(&assert.ty) {
            continue;
        }
        let asserted_ty = resolve_doc_type(scope, templates, &assert.ty);
        let Some(relation) = definite_supertype_relation(fa, &expr_ty, &asserted_ty) else {
            continue;
        };
        let (code, what) = match (assert.negated, relation) {
            (false, true) => (
                "assert.alreadyNarrowedType",
                "does not narrow down the type",
            ),
            (false, false) => ("assert.impossibleType", "can never happen"),
            (true, true) => ("assert.impossibleType", "can never happen"),
            (true, false) => (
                "assert.alreadyNarrowedType",
                "does not narrow down the type",
            ),
        };
        let neg = if assert.negated { "negated " } else { "" };
        out.push(
            Diagnostic::error(
                span,
                format!(
                    "Asserted {neg}type {asserted_ty} for {} with type {expr_ty} {what}.",
                    assert.expr
                ),
            )
            .with_code(code),
        );
    }
}

fn parse_assert_value(value: &str) -> Option<AssertDoc> {
    let mut value = value.trim_start();
    let negated = value.starts_with('!');
    if negated {
        value = value[1..].trim_start();
    }
    let (ty, consumed) = php_phpdoc::parse_type_prefix(value)?;
    let rest = value[consumed..].trim_start();
    let (expr, param_name) = parse_assert_expr(rest)?;
    Some(AssertDoc {
        negated,
        ty,
        expr,
        param_name,
    })
}

fn parse_assert_expr(rest: &str) -> Option<(String, String)> {
    let rest = rest.trim_start();
    let after_dollar = rest.strip_prefix('$')?;
    let end = after_dollar
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .unwrap_or(after_dollar.len());
    if end == 0 {
        return None;
    }
    let param_name = after_dollar[..end].to_string();
    let expr_end = rest.find(char::is_whitespace).unwrap_or(rest.len());
    Some((rest[..expr_end].to_string(), param_name))
}

// --- FunctionConditionalReturnTypeRule / MethodConditionalReturnTypeRule ----

/// Validate conditional PHPDoc types in a function/method signature. This covers
/// the rule helper's FP-safe branches: unknown `$parameter` subjects, non-template
/// type subjects, and scalar conditions whose truth value is definite.
fn run_conditional_return_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            match &st.kind {
                StmtKind::Function(f) => {
                    if let Some(doc) = &f.doc {
                        check_function_conditionals(
                            fa,
                            scope,
                            &[doc.as_str()],
                            doc,
                            &f.params,
                            st.span,
                            &mut out,
                        );
                    }
                }
                StmtKind::Class(c) => {
                    let class_docs = c.doc.as_deref().into_iter().collect::<Vec<_>>();
                    for m in &c.members {
                        let Member::Method(mth) = m else { continue };
                        let Some(doc) = &mth.doc else { continue };
                        let mut docs = class_docs.clone();
                        docs.push(doc.as_str());
                        check_function_conditionals(
                            fa,
                            scope,
                            &docs,
                            doc,
                            &mth.params,
                            st.span,
                            &mut out,
                        );
                    }
                }
                _ => {}
            }
        }
    });
    out
}

fn check_function_conditionals(
    fa: &FileAnalysis,
    scope: &Scope,
    template_docs: &[&str],
    doc_raw: &str,
    params: &[Param],
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    let (templates, bounds) = template_context(scope, template_docs);
    let param_types = declaration_param_types(fa, scope, &templates, doc_raw, params);
    let doc = php_phpdoc::parse(doc_raw);

    for p in &doc.params {
        if let Some(ty) = &p.ty {
            check_conditionals_in_doc_type(
                fa,
                scope,
                &templates,
                &bounds,
                &param_types,
                ty,
                span,
                out,
            );
        }
    }
    if let Some(ty) = &doc.returns {
        check_conditionals_in_doc_type(fa, scope, &templates, &bounds, &param_types, ty, span, out);
    }

    // `@param-out` is not represented in `Doc::params`, but PHPStan traverses
    // parameter out-types too, so include the tag's type operand when present.
    let block = php_phpdoc::parse_block(doc_raw);
    for tag in &block.tags {
        let (base, prefix) = strip_doc_prefix(&tag.name);
        if base != "param-out" || prefix == Some("psalm") {
            continue;
        }
        if let Some((ty, _)) = php_phpdoc::parse_type_prefix(&tag.value) {
            check_conditionals_in_doc_type(
                fa,
                scope,
                &templates,
                &bounds,
                &param_types,
                &ty,
                span,
                out,
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn check_conditionals_in_doc_type(
    fa: &FileAnalysis,
    scope: &Scope,
    templates: &[String],
    bounds: &HashMap<String, Option<Type>>,
    params: &HashMap<String, Type>,
    ty: &php_phpdoc::DocType,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    use php_phpdoc::DocType;
    match ty {
        DocType::Conditional {
            subject,
            negated,
            target,
            then,
            els,
        } => {
            check_one_conditional(
                fa, scope, templates, bounds, params, subject, *negated, target, span, out,
            );
            check_conditionals_in_doc_type(fa, scope, templates, bounds, params, target, span, out);
            check_conditionals_in_doc_type(fa, scope, templates, bounds, params, then, span, out);
            check_conditionals_in_doc_type(fa, scope, templates, bounds, params, els, span, out);
        }
        DocType::Nullable(inner) | DocType::Array(inner) => {
            check_conditionals_in_doc_type(fa, scope, templates, bounds, params, inner, span, out);
        }
        DocType::Union(parts) | DocType::Intersection(parts) => {
            for p in parts {
                check_conditionals_in_doc_type(fa, scope, templates, bounds, params, p, span, out);
            }
        }
        DocType::Generic { args, .. } => {
            for a in args {
                check_conditionals_in_doc_type(fa, scope, templates, bounds, params, a, span, out);
            }
        }
        DocType::Shape { fields, .. } => {
            for fld in fields {
                check_conditionals_in_doc_type(
                    fa, scope, templates, bounds, params, &fld.ty, span, out,
                );
            }
        }
        DocType::Callable {
            params: ps, ret, ..
        } => {
            for p in ps {
                check_conditionals_in_doc_type(fa, scope, templates, bounds, params, p, span, out);
            }
            if let Some(ret) = ret {
                check_conditionals_in_doc_type(
                    fa, scope, templates, bounds, params, ret, span, out,
                );
            }
        }
        DocType::Named(_)
        | DocType::ConstString(_)
        | DocType::ConstInt(_)
        | DocType::ClassConst(_) => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn check_one_conditional(
    fa: &FileAnalysis,
    scope: &Scope,
    templates: &[String],
    bounds: &HashMap<String, Option<Type>>,
    params: &HashMap<String, Type>,
    subject: &str,
    negated: bool,
    target: &php_phpdoc::DocType,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    let subject_ty = if let Some(name) = subject.strip_prefix('$') {
        match params.get(name) {
            Some(t) => t.clone(),
            None => {
                out.push(
                    Diagnostic::error(
                        span,
                        format!("Conditional return type references unknown parameter ${name}."),
                    )
                    .with_code("parameter.notFound"),
                );
                return;
            }
        }
    } else if subject.eq_ignore_ascii_case("static") {
        return;
    } else if let Some(bound) = bounds.get(subject) {
        match bound {
            Some(t) => t.clone(),
            None => return,
        }
    } else {
        out.push(
            Diagnostic::error(
                span,
                format!(
                    "Conditional return type uses subject type {subject} which is not part of PHPDoc @template tags."
                ),
            )
            .with_code("conditionalType.subjectNotFound"),
        );
        return;
    };

    if !doc_type_relation_safe(target) {
        return;
    }
    let target_ty = resolve_doc_type(scope, templates, target);
    let Some(relation) = definite_supertype_relation(fa, &subject_ty, &target_ty) else {
        return;
    };
    let always_true = if negated { !relation } else { relation };
    let code = if always_true {
        "conditionalType.alwaysTrue"
    } else {
        "conditionalType.alwaysFalse"
    };
    let not = if negated { " not" } else { "" };
    out.push(
        Diagnostic::error(
            span,
            format!(
                "Condition \"{subject_ty} is{not} {target_ty}\" in conditional return type is always {}.",
                if always_true { "true" } else { "false" }
            ),
        )
        .with_code(code),
    );
}

fn declaration_param_types(
    fa: &FileAnalysis,
    scope: &Scope,
    templates: &[String],
    doc_raw: &str,
    params: &[Param],
) -> HashMap<String, Type> {
    let mut out = HashMap::new();
    for p in params {
        let ty =
            p.ty.as_ref()
                .map(|t| resolve_ast_type(scope, t))
                .unwrap_or(Type::Mixed);
        out.insert(scope_param_name(p, fa), ty);
    }

    let doc = php_phpdoc::parse(doc_raw);
    for p in &doc.params {
        let (Some(name), Some(ty)) = (&p.name, &p.ty) else {
            continue;
        };
        if out.contains_key(name) && doc_type_relation_safe(ty) {
            out.insert(name.clone(), resolve_doc_type(scope, templates, ty));
        }
    }
    out
}

fn scope_param_name(p: &Param, fa: &FileAnalysis) -> String {
    fa.interner.resolve(p.name).to_string()
}

fn template_context(scope: &Scope, docs: &[&str]) -> (Vec<String>, HashMap<String, Option<Type>>) {
    let mut names = Vec::new();
    for doc in docs {
        for t in php_phpdoc::parse(doc).templates {
            if !names.iter().any(|n| n == &t.name) {
                names.push(t.name);
            }
        }
    }

    let mut bounds = HashMap::new();
    for doc in docs {
        for t in php_phpdoc::parse(doc).templates {
            let bound = t
                .bound
                .as_ref()
                .filter(|b| doc_type_relation_safe(b))
                .map(|b| resolve_doc_type(scope, &names, b));
            bounds.insert(t.name, bound);
        }
    }
    (names, bounds)
}

fn doc_type_relation_safe(t: &php_phpdoc::DocType) -> bool {
    use php_phpdoc::DocType;
    match t {
        DocType::Named(name) => matches!(
            name.to_ascii_lowercase().as_str(),
            "int"
                | "integer"
                | "float"
                | "double"
                | "string"
                | "bool"
                | "boolean"
                | "null"
                | "true"
                | "false"
        ),
        DocType::Nullable(inner) | DocType::Array(inner) => doc_type_relation_safe(inner),
        DocType::Union(parts) => parts.iter().all(doc_type_relation_safe),
        DocType::ConstString(_) | DocType::ConstInt(_) => true,
        DocType::Intersection(_)
        | DocType::Generic { .. }
        | DocType::Shape { .. }
        | DocType::Callable { .. }
        | DocType::ClassConst(_)
        | DocType::Conditional { .. } => false,
    }
}

/// Return whether `target` is definitely a supertype of `value`. `None` means
/// "maybe" or "not enough precision"; callers must not report.
fn definite_supertype_relation(fa: &FileAnalysis, value: &Type, target: &Type) -> Option<bool> {
    use Type::*;
    match (value, target) {
        (
            Mixed
                | ExplicitMixed
                | Unknown(_)
                | TemplateVar(_)
                | Object
                | Resource
                | Callable(_)
                | ClassString(_),
            _,
        )
        | (
            _,
            Mixed
                | ExplicitMixed
                | Unknown(_)
                | TemplateVar(_)
                | Object
                | Resource
                | Callable(_)
                | ClassString(_),
        ) => None,
        (SelfType | StaticType | Parent, _) | (_, SelfType | StaticType | Parent) => None,
        (Never, _) => Some(true),
        (Nullable(v), t) => {
            definite_supertype_relation(fa, &Type::union(vec![(**v).clone(), Null]), t)
        }
        (v, Nullable(t)) => {
            definite_supertype_relation(fa, v, &Type::union(vec![(**t).clone(), Null]))
        }
        (Union(parts), t) => {
            let rels = parts
                .iter()
                .map(|p| definite_supertype_relation(fa, p, t))
                .collect::<Option<Vec<_>>>()?;
            if rels.iter().all(|r| *r) {
                Some(true)
            } else if rels.iter().all(|r| !*r) {
                Some(false)
            } else {
                None
            }
        }
        (v, Union(parts)) => {
            let rels = parts
                .iter()
                .map(|p| definite_supertype_relation(fa, v, p))
                .collect::<Option<Vec<_>>>()?;
            if rels.iter().any(|r| *r) {
                Some(true)
            } else if rels.iter().all(|r| !*r) {
                Some(false)
            } else {
                None
            }
        }
        (Intersection(_), _) | (_, Intersection(_)) => None,
        (Named { fqn: a, .. }, Named { fqn: b, .. }) => {
            if fa.class_fully_known(a) && fa.class_fully_known(b) {
                Some(fa.reflection.is_subclass_of(a, b))
            } else {
                None
            }
        }
        (Named { .. }, _) | (_, Named { .. }) => None,
        (LiteralInt(a), LiteralInt(b)) => Some(a == b),
        (LiteralInt(_), Int | Float) => Some(true),
        (Int, LiteralInt(_)) => None,
        (Int, Int) => Some(true),
        (Int, Float) => Some(true),
        (
            Int | LiteralInt(_),
            String
            | Bool
            | True
            | False
            | Null
            | Array(_)
            | Iterable(_)
            | List(_)
            | Shape { .. }
            | Void,
        ) => Some(false),
        (Float, Float) => Some(true),
        (
            Float,
            Int
            | String
            | Bool
            | True
            | False
            | Null
            | Array(_)
            | Iterable(_)
            | List(_)
            | Shape { .. }
            | Void,
        ) => Some(false),
        (LiteralString(a), LiteralString(b)) => Some(a == b),
        (LiteralString(_) | String, String) => Some(true),
        (String, LiteralString(_)) => None,
        (
            String | LiteralString(_),
            Int
            | Float
            | Bool
            | True
            | False
            | Null
            | Array(_)
            | Iterable(_)
            | List(_)
            | Shape { .. }
            | Void,
        ) => Some(false),
        (True, True) | (False, False) => Some(true),
        (True | False, Bool) => Some(true),
        (Bool, Bool) => Some(true),
        (Bool, True | False) => None,
        (True, False) | (False, True) => Some(false),
        (
            Bool | True | False,
            Int
            | Float
            | String
            | LiteralString(_)
            | Null
            | Array(_)
            | Iterable(_)
            | List(_)
            | Shape { .. }
            | Void,
        ) => Some(false),
        (Null, Null) => Some(true),
        (
            Null,
            Int
            | Float
            | String
            | LiteralString(_)
            | Bool
            | True
            | False
            | Array(_)
            | Iterable(_)
            | List(_)
            | Shape { .. }
            | Void,
        ) => Some(false),
        (Void, Void) => Some(true),
        (Void, _) | (_, Void) => Some(false),
        (Array(_), Array(_))
        | (Iterable(_), Iterable(_))
        | (List(_), List(_))
        | (Shape { .. }, Shape { .. }) => None,
        (
            Array(_) | Iterable(_) | List(_) | Shape { .. },
            Int | Float | String | LiteralString(_) | Bool | True | False | Null,
        ) => Some(false),
        (IntRange { .. }, _) | (_, IntRange { .. }) => None,
        _ => None,
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
                            fa,
                            scope,
                            &templates,
                            doc,
                            &f.params,
                            f.return_type.as_ref(),
                            st.span,
                            &mut out,
                        );
                    }
                }
                StmtKind::Class(c) => {
                    let class_templates = c.doc.as_deref().map(template_names).unwrap_or_default();
                    for m in &c.members {
                        let Member::Method(mth) = m else { continue };
                        let Some(doc) = &mth.doc else { continue };
                        let mut templates = class_templates.clone();
                        templates.extend(template_names(doc));
                        check_incompat(
                            fa,
                            scope,
                            &templates,
                            doc,
                            &mth.params,
                            mth.return_type.as_ref(),
                            st.span,
                            &mut out,
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
    php_phpdoc::parse(raw)
        .templates
        .into_iter()
        .map(|t| t.name)
        .collect()
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
        let (Some(pname), Some(doc_ty)) = (&p.name, &p.ty) else {
            continue;
        };
        let Some(native) = params
            .iter()
            .find(|np| fa.interner.resolve(np.name) == pname)
        else {
            continue; // unknown param -> parameter.notFound (a different rule).
        };
        let Some(native_ast) = &native.ty else {
            continue;
        }; // no native hint -> mixed.
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
            let StmtKind::Class(c) = &st.kind else {
                continue;
            };
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
                let Some(var) = parsed.vars.first() else {
                    continue;
                };
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

// --- hook parameter.phpDocType / return.phpDocType -------------------------

/// `IncompatiblePropertyHookPhpDocTypeRule`: a property hook's own PHPDoc is
/// checked against the hook's native method-like signature. The property's
/// docblock is deliberately ignored here; phpstan receives an
/// `InPropertyHookNode` with the hook doc comment only.
fn run_property_hook_phpdoc_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            let StmtKind::Class(c) = &st.kind else {
                continue;
            };
            let class_templates = c.doc.as_deref().map(template_names).unwrap_or_default();
            for m in &c.members {
                let Member::Property(p) = m else { continue };
                let Some(property_native_ast) = &p.ty else {
                    continue;
                };
                let property_native = resolve_ast_type(scope, property_native_ast);
                for elem in &p.props {
                    let Some(hooks) = &elem.hooks else { continue };
                    for hook in hooks {
                        let Some(doc_raw) = &hook.doc else { continue };
                        let mut templates = class_templates.clone();
                        templates.extend(template_names(doc_raw));
                        check_hook_incompat(
                            fa,
                            scope,
                            &templates,
                            doc_raw,
                            hook,
                            &property_native,
                            st.span,
                            &mut out,
                        );
                    }
                }
            }
        }
    });
    out
}

#[allow(clippy::too_many_arguments)]
fn check_hook_incompat(
    fa: &FileAnalysis,
    scope: &Scope,
    templates: &[String],
    doc_raw: &str,
    hook: &PropertyHook,
    property_native: &Type,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    let doc = php_phpdoc::parse(doc_raw);
    let hook_name = fa.interner.resolve(hook.name);

    for p in &doc.params {
        if p.variadic {
            continue;
        }
        let (Some(pname), Some(doc_ty)) = (&p.name, &p.ty) else {
            continue;
        };
        let Some(native_t) = hook_param_native_type(fa, scope, hook, hook_name, pname, property_native)
        else {
            out.push(
                Diagnostic::error(
                    span,
                    format!("PHPDoc tag @param references unknown parameter: ${pname}"),
                )
                .with_code("parameter.notFound"),
            );
            continue;
        };
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

    let native_return = if hook_name.eq_ignore_ascii_case("get") {
        property_native.clone()
    } else {
        Type::Void
    };
    if let Some(doc_ty) = &doc.returns {
        let doc_t = resolve_doc_type(scope, templates, doc_ty);
        if !crate::is_assignable(fa.reflection, &doc_t, &native_return) {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "PHPDoc tag @return with type {doc_t} \
                         is incompatible with native type {native_return}."
                    ),
                )
                .with_code("return.phpDocType"),
            );
        }
    }
}

fn hook_param_native_type(
    fa: &FileAnalysis,
    scope: &Scope,
    hook: &PropertyHook,
    hook_name: &str,
    pname: &str,
    property_native: &Type,
) -> Option<Type> {
    if let Some(params) = &hook.params {
        let native = params
            .iter()
            .find(|np| fa.interner.resolve(np.name) == pname)?;
        return native.ty.as_ref().map(|t| resolve_ast_type(scope, t));
    }

    if hook_name.eq_ignore_ascii_case("set") && pname == "value" {
        return Some(property_native.clone());
    }

    None
}

// --- classConstant.phpDocType (IncompatibleClassConstantPhpDocTypeRule) ------

/// A class constant's `@var` PHPDoc type must be a *subtype* of the constant's
/// native type hint (8.3 typed constants). Mirrors phpstan's
/// `IncompatibleClassConstantPhpDocTypeRule` (`classConstant.phpDocType`).
fn run_class_const_phpdoc_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            let StmtKind::Class(c) = &st.kind else {
                continue;
            };
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
                let Some(var) = parsed.vars.first() else {
                    continue;
                };
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
        | Type::ExplicitMixed
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
                                    format!("PHPDoc tag @var has invalid type {}.", entry.fqn),
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

// --- missingType.* for inline @var (InvalidPhpDocVarTagTypeRule) ------------

/// `@var` types on ordinary statements should specify value types for iterable
/// words, signatures for callables, and template arguments for known generic
/// classes. Unknown classes are deliberately silent here: `class.notFound` for
/// `@var` is disabled by project policy because class/stub coverage is not yet
/// complete enough.
fn run_var_tag_missing_types(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            check_var_tag_missing_types_in_stmt(fa, scope, &TemplateEnv::default(), st, &mut out);
        }
    });
    out
}

#[derive(Clone, Default)]
struct TemplateEnv {
    all: Vec<String>,
    class_fqn: Option<String>,
    class_templates: Vec<String>,
}

impl TemplateEnv {
    fn function(doc: Option<&str>) -> Self {
        Self {
            all: doc.map(template_names).unwrap_or_default(),
            class_fqn: None,
            class_templates: Vec::new(),
        }
    }

    fn method(class_fqn: String, class_templates: Vec<String>, doc: Option<&str>) -> Self {
        let mut all = class_templates.clone();
        all.extend(doc.map(template_names).unwrap_or_default());
        Self {
            all,
            class_fqn: Some(class_fqn),
            class_templates,
        }
    }
}

fn check_var_tag_missing_types_in_stmt(
    fa: &FileAnalysis,
    scope: &Scope,
    env: &TemplateEnv,
    st: &Stmt,
    out: &mut Vec<Diagnostic>,
) {
    if let Some(doc) = &st.doc {
        if var_tag_missing_type_applies_to_stmt(st) {
            check_var_tag_missing_types(fa, scope, env, doc, st.span, out);
        }
    }

    match &st.kind {
        StmtKind::Block(body) => {
            for s in body {
                check_var_tag_missing_types_in_stmt(fa, scope, env, s, out);
            }
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            check_var_tag_missing_types_in_stmt(fa, scope, env, then, out);
            for ei in elseifs {
                check_var_tag_missing_types_in_stmt(fa, scope, env, &ei.body, out);
            }
            if let Some(els) = els {
                check_var_tag_missing_types_in_stmt(fa, scope, env, els, out);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => {
            check_var_tag_missing_types_in_stmt(fa, scope, env, body, out);
        }
        StmtKind::Switch { cases, .. } => {
            for case in cases {
                for s in &case.body {
                    check_var_tag_missing_types_in_stmt(fa, scope, env, s, out);
                }
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for s in body {
                check_var_tag_missing_types_in_stmt(fa, scope, env, s, out);
            }
            for c in catches {
                for s in &c.body {
                    check_var_tag_missing_types_in_stmt(fa, scope, env, s, out);
                }
            }
            if let Some(finally) = finally {
                for s in finally {
                    check_var_tag_missing_types_in_stmt(fa, scope, env, s, out);
                }
            }
        }
        StmtKind::Declare {
            body: Some(body), ..
        } => {
            check_var_tag_missing_types_in_stmt(fa, scope, env, body, out);
        }
        StmtKind::Namespace {
            body: Some(body), ..
        } => {
            for s in body {
                check_var_tag_missing_types_in_stmt(fa, scope, env, s, out);
            }
        }
        StmtKind::Function(f) => {
            let fn_env = TemplateEnv::function(f.doc.as_deref());
            for s in &f.body {
                check_var_tag_missing_types_in_stmt(fa, scope, &fn_env, s, out);
            }
        }
        StmtKind::Class(c) => {
            let Some(name) = c.name else { return };
            let class_fqn = scope.qualify(fa.interner.resolve(name));
            let class_templates = c.doc.as_deref().map(template_names).unwrap_or_default();
            for m in &c.members {
                let Member::Method(mth) = m else { continue };
                let Some(body) = &mth.body else { continue };
                let method_env = TemplateEnv::method(
                    class_fqn.clone(),
                    class_templates.clone(),
                    mth.doc.as_deref(),
                );
                for s in body {
                    check_var_tag_missing_types_in_stmt(fa, scope, &method_env, s, out);
                }
            }
        }
        _ => {}
    }
}

fn var_tag_missing_type_applies_to_stmt(st: &Stmt) -> bool {
    !matches!(
        &st.kind,
        StmtKind::Function(_)
            | StmtKind::Class(_)
            | StmtKind::ConstDecl { .. }
            | StmtKind::Namespace { .. }
            | StmtKind::Use(_)
            | StmtKind::GroupUse { .. }
    )
}

fn check_var_tag_missing_types(
    fa: &FileAnalysis,
    scope: &Scope,
    env: &TemplateEnv,
    doc_raw: &str,
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    for var in php_phpdoc::parse(doc_raw).vars {
        let Some(ty) = var.ty else { continue };
        let ident = match &var.name {
            Some(name) => format!("PHPDoc tag @var for variable ${name}"),
            None => "PHPDoc tag @var".to_string(),
        };

        if let Some(word) = missing_iterable_word_doc(&ty) {
            out.push(
                Diagnostic::error(
                    span,
                    format!("{ident} has no value type specified in iterable type {word}."),
                )
                .with_code("missingType.iterableValue"),
            );
        }

        for (name, generics) in missing_generic_doc(fa, scope, env, &ty) {
            out.push(
                Diagnostic::error(
                    span,
                    format!("{ident} contains generic {name} but does not specify its types: {generics}"),
                )
                .with_code("missingType.generics"),
            );
        }

        if missing_callable_signature_doc(&ty) {
            out.push(
                Diagnostic::error(
                    span,
                    format!("{ident} has no signature specified for callable."),
                )
                .with_code("missingType.callable"),
            );
        }
    }
}

fn missing_iterable_word_doc(t: &DocType) -> Option<&'static str> {
    match t {
        DocType::Named(n) if n.eq_ignore_ascii_case("array") => Some("array"),
        DocType::Named(n) if n.eq_ignore_ascii_case("iterable") => Some("iterable"),
        DocType::Nullable(inner) | DocType::Array(inner) => missing_iterable_word_doc(inner),
        DocType::Union(parts) | DocType::Intersection(parts) => {
            parts.iter().find_map(missing_iterable_word_doc)
        }
        DocType::Generic { args, .. } => args.iter().find_map(missing_iterable_word_doc),
        DocType::Shape { fields, .. } => {
            fields.iter().find_map(|f| missing_iterable_word_doc(&f.ty))
        }
        DocType::Callable { params, ret, .. } => params
            .iter()
            .find_map(missing_iterable_word_doc)
            .or_else(|| ret.as_deref().and_then(missing_iterable_word_doc)),
        DocType::Conditional {
            target, then, els, ..
        } => missing_iterable_word_doc(target)
            .or_else(|| missing_iterable_word_doc(then))
            .or_else(|| missing_iterable_word_doc(els)),
        _ => None,
    }
}

fn missing_generic_doc(
    fa: &FileAnalysis,
    scope: &Scope,
    env: &TemplateEnv,
    t: &DocType,
) -> Vec<(String, String)> {
    let mut out = Vec::new();
    collect_missing_generic_doc(fa, scope, env, t, &mut out);
    out
}

fn collect_missing_generic_doc(
    fa: &FileAnalysis,
    scope: &Scope,
    env: &TemplateEnv,
    t: &DocType,
    out: &mut Vec<(String, String)>,
) {
    match t {
        DocType::Named(n) => {
            if let Some((name, templates)) = generic_class_without_args(fa, scope, env, n) {
                out.push((name, templates));
            }
        }
        DocType::Generic { args, .. } => {
            for arg in args {
                collect_missing_generic_doc(fa, scope, env, arg, out);
            }
        }
        DocType::Nullable(inner) | DocType::Array(inner) => {
            collect_missing_generic_doc(fa, scope, env, inner, out);
        }
        DocType::Union(parts) | DocType::Intersection(parts) => {
            for p in parts {
                collect_missing_generic_doc(fa, scope, env, p, out);
            }
        }
        DocType::Shape { fields, .. } => {
            for f in fields {
                collect_missing_generic_doc(fa, scope, env, &f.ty, out);
            }
        }
        DocType::Callable { params, ret, .. } => {
            for p in params {
                collect_missing_generic_doc(fa, scope, env, p, out);
            }
            if let Some(ret) = ret {
                collect_missing_generic_doc(fa, scope, env, ret, out);
            }
        }
        DocType::Conditional {
            target, then, els, ..
        } => {
            for p in [target.as_ref(), then.as_ref(), els.as_ref()] {
                collect_missing_generic_doc(fa, scope, env, p, out);
            }
        }
        _ => {}
    }
}

fn generic_class_without_args(
    fa: &FileAnalysis,
    scope: &Scope,
    env: &TemplateEnv,
    name: &str,
) -> Option<(String, String)> {
    if is_doc_keyword(name) || env.all.iter().any(|t| t == name) {
        return None;
    }

    let fqn = match name.to_ascii_lowercase().as_str() {
        "self" | "static" | "$this" => env.class_fqn.clone()?,
        _ => match scope.resolve_class(&name_from_doc(name)) {
            Resolution::Fqn(fqn) => fqn,
            Resolution::Fallback { namespaced, .. } => namespaced,
            _ => return None,
        },
    };

    let class_ref = fa.reflection.class(&fqn)?;
    if class_ref.kind == ClassKind::Trait {
        return None;
    }

    let templates = if env
        .class_fqn
        .as_deref()
        .is_some_and(|current| fqn.trim_start_matches('\\').eq_ignore_ascii_case(current))
    {
        env.class_templates.clone()
    } else {
        class_ref.templates.clone()
    };
    if templates.is_empty() {
        return None;
    }

    Some((
        class_ref.fqn.trim_start_matches('\\').to_string(),
        templates.join(", "),
    ))
}

fn name_from_doc(text: &str) -> Name {
    let fq = if text.starts_with("namespace\\") {
        NameFq::Relative
    } else if text.starts_with('\\') {
        NameFq::Fq
    } else {
        NameFq::NotFq
    };
    Name {
        span: Span::new(0, 0),
        fq,
        text: text.to_string(),
    }
}

fn is_doc_keyword(name: &str) -> bool {
    matches!(
        name.to_ascii_lowercase().as_str(),
        "array"
            | "iterable"
            | "callable"
            | "int"
            | "integer"
            | "float"
            | "double"
            | "string"
            | "bool"
            | "boolean"
            | "void"
            | "never"
            | "mixed"
            | "object"
            | "resource"
            | "null"
            | "true"
            | "false"
            | "scalar"
            | "array-key"
            | "list"
            | "non-empty-array"
            | "non-empty-list"
            | "class-string"
            | "interface-string"
            | "trait-string"
            | "enum-string"
    )
}

fn missing_callable_signature_doc(t: &DocType) -> bool {
    match t {
        DocType::Named(n) => n.eq_ignore_ascii_case("callable"),
        DocType::Nullable(inner) | DocType::Array(inner) => missing_callable_signature_doc(inner),
        DocType::Union(parts) | DocType::Intersection(parts) => {
            parts.iter().any(missing_callable_signature_doc)
        }
        DocType::Generic { args, .. } => args.iter().any(missing_callable_signature_doc),
        DocType::Shape { fields, .. } => {
            fields.iter().any(|f| missing_callable_signature_doc(&f.ty))
        }
        DocType::Callable { params, ret, .. } => {
            params.iter().any(missing_callable_signature_doc)
                || ret.as_deref().is_some_and(missing_callable_signature_doc)
        }
        DocType::Conditional {
            target, then, els, ..
        } => {
            missing_callable_signature_doc(target)
                || missing_callable_signature_doc(then)
                || missing_callable_signature_doc(els)
        }
        _ => false,
    }
}

// --- varTag.nativeType / varTag.type (VarTagChangedExpressionTypeRule) -----

/// Inline `@var` above a statement can "change" the expression's type. This is
/// the tiny FP-safe subset of phpstan's `VarTagChangedExpressionTypeRule`: only
/// a simple parameter variable in a non-assignment statement, before any local
/// reassignment to that parameter, and only when the scalar-ish relation is
/// definite.
fn run_var_tag_changed_expression_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            match &st.kind {
                StmtKind::Function(f) => {
                    let templates = f.doc.as_deref().map(template_names).unwrap_or_default();
                    let param_types = declaration_param_types(
                        fa,
                        scope,
                        &templates,
                        f.doc.as_deref().unwrap_or("/** */"),
                        &f.params,
                    );
                    let native_param_types = native_param_types(scope, fa, &f.params);
                    check_var_tag_changed_block(
                        fa,
                        scope,
                        &templates,
                        &param_types,
                        &native_param_types,
                        &f.body,
                        &mut Vec::new(),
                        &mut out,
                    );
                }
                StmtKind::Class(c) => {
                    let class_templates = c.doc.as_deref().map(template_names).unwrap_or_default();
                    for m in &c.members {
                        let Member::Method(mth) = m else { continue };
                        let Some(body) = &mth.body else { continue };
                        let mut templates = class_templates.clone();
                        templates
                            .extend(mth.doc.as_deref().map(template_names).unwrap_or_default());
                        let param_types = declaration_param_types(
                            fa,
                            scope,
                            &templates,
                            mth.doc.as_deref().unwrap_or("/** */"),
                            &mth.params,
                        );
                        let native_param_types = native_param_types(scope, fa, &mth.params);
                        check_var_tag_changed_block(
                            fa,
                            scope,
                            &templates,
                            &param_types,
                            &native_param_types,
                            body,
                            &mut Vec::new(),
                            &mut out,
                        );
                    }
                }
                _ => {}
            }
        }
    });
    out
}

fn native_param_types(scope: &Scope, fa: &FileAnalysis, params: &[Param]) -> HashMap<String, Type> {
    let mut out = HashMap::new();
    for p in params {
        let Some(ty) = &p.ty else { continue };
        out.insert(scope_param_name(p, fa), resolve_ast_type(scope, ty));
    }
    out
}

#[allow(clippy::too_many_arguments)]
fn check_var_tag_changed_block(
    fa: &FileAnalysis,
    scope: &Scope,
    templates: &[String],
    param_types: &HashMap<String, Type>,
    native_param_types: &HashMap<String, Type>,
    body: &[Stmt],
    assigned: &mut Vec<String>,
    out: &mut Vec<Diagnostic>,
) {
    for st in body {
        check_var_tag_changed_stmt(
            fa,
            scope,
            templates,
            param_types,
            native_param_types,
            st,
            assigned,
            out,
        );
        collect_assigned_vars(st, fa.interner, assigned);
    }
}

#[allow(clippy::too_many_arguments)]
fn check_var_tag_changed_stmt(
    fa: &FileAnalysis,
    scope: &Scope,
    templates: &[String],
    param_types: &HashMap<String, Type>,
    native_param_types: &HashMap<String, Type>,
    st: &Stmt,
    assigned: &[String],
    out: &mut Vec<Diagnostic>,
) {
    if let (Some(doc), Some(expr)) = (st.doc.as_deref(), var_tag_changed_target_expr(st)) {
        check_var_tag_changed_doc(
            fa,
            scope,
            templates,
            param_types,
            native_param_types,
            doc,
            expr,
            st.span,
            assigned,
            out,
        );
    }

    match &st.kind {
        StmtKind::Block(body) => {
            let mut inner = assigned.to_vec();
            check_var_tag_changed_block(
                fa,
                scope,
                templates,
                param_types,
                native_param_types,
                body,
                &mut inner,
                out,
            );
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            let mut inner = assigned.to_vec();
            check_var_tag_changed_stmt(
                fa,
                scope,
                templates,
                param_types,
                native_param_types,
                then,
                &inner,
                out,
            );
            collect_assigned_vars(then, fa.interner, &mut inner);
            for ei in elseifs {
                let mut branch = assigned.to_vec();
                check_var_tag_changed_stmt(
                    fa,
                    scope,
                    templates,
                    param_types,
                    native_param_types,
                    &ei.body,
                    &branch,
                    out,
                );
                collect_assigned_vars(&ei.body, fa.interner, &mut branch);
            }
            if let Some(els) = els {
                let branch = assigned.to_vec();
                check_var_tag_changed_stmt(
                    fa,
                    scope,
                    templates,
                    param_types,
                    native_param_types,
                    els,
                    &branch,
                    out,
                );
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Foreach { body, .. } => {
            let inner = assigned.to_vec();
            check_var_tag_changed_stmt(
                fa,
                scope,
                templates,
                param_types,
                native_param_types,
                body,
                &inner,
                out,
            );
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn check_var_tag_changed_doc(
    fa: &FileAnalysis,
    scope: &Scope,
    templates: &[String],
    param_types: &HashMap<String, Type>,
    native_param_types: &HashMap<String, Type>,
    doc_raw: &str,
    expr: &Expr,
    span: Span,
    assigned: &[String],
    out: &mut Vec<Diagnostic>,
) {
    let doc = php_phpdoc::parse(doc_raw);
    let [var] = doc.vars.as_slice() else { return };
    let Some(doc_ty) = &var.ty else { return };
    if !doc_type_relation_safe(doc_ty) {
        return;
    }
    let Some(expr_name) = simple_variable_name(expr, fa.interner) else {
        return;
    };
    if assigned.iter().any(|name| name == &expr_name) {
        return;
    }
    if var.name.as_ref().is_some_and(|name| name != &expr_name) {
        return;
    }
    let doc_t = resolve_doc_type(scope, templates, doc_ty);

    if let Some(native_t) = native_param_types.get(&expr_name) {
        if definite_supertype_relation(fa, &doc_t, native_t) == Some(false) {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "PHPDoc tag @var with type {doc_t} is not subtype of native type {native_t}."
                    ),
                )
                .with_code("varTag.nativeType"),
            );
            return;
        }
    }

    if fa.treat_phpdoc_types_as_certain {
        if let Some(param_t) = param_types.get(&expr_name) {
            if definite_supertype_relation(fa, &doc_t, param_t) == Some(false) {
                out.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "PHPDoc tag @var with type {doc_t} is not subtype of type {param_t}."
                        ),
                    )
                    .with_code("varTag.type"),
                );
            }
        }
    }
}

fn var_tag_changed_target_expr(st: &Stmt) -> Option<&Expr> {
    match &st.kind {
        StmtKind::Return(Some(e)) | StmtKind::Expr(e) => Some(e),
        StmtKind::If { cond, .. }
        | StmtKind::While { cond, .. }
        | StmtKind::DoWhile { cond, .. } => Some(cond),
        _ => None,
    }
}

fn simple_variable_name(e: &Expr, interner: &Interner) -> Option<String> {
    match &e.kind {
        ExprKind::Variable(v) => Some(interner.resolve(*v).to_string()),
        ExprKind::Paren(inner) => simple_variable_name(inner, interner),
        _ => None,
    }
}

fn collect_assigned_vars(st: &Stmt, interner: &Interner, out: &mut Vec<String>) {
    walk::for_each_expr_in_scope(st, &mut |e| {
        let target = match &e.kind {
            ExprKind::Assign { target, .. }
            | ExprKind::AssignOp { target, .. }
            | ExprKind::AssignRef { target, .. } => target,
            ExprKind::PreInc(target)
            | ExprKind::PreDec(target)
            | ExprKind::PostInc(target)
            | ExprKind::PostDec(target) => target,
            _ => return,
        };
        if let Some(name) = simple_variable_name(target, interner) {
            if !out.iter().any(|n| n == &name) {
                out.push(name);
            }
        }
    });
}

// --- selfOut.* (IncompatibleSelfOutTypeRule) --------------------------------

/// `@phpstan-self-out` (and `@psalm-self-out`) cannot be used on a static
/// method, and its type must be a subtype of the declaring class. The subtype
/// check is definite-only: unknowns/templates/intersections are skipped, and
/// class names rely on the lenient assignability relation.
fn run_self_out(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            let StmtKind::Class(c) = &st.kind else {
                continue;
            };
            let class_name = c
                .name
                .map(|n| scope.qualify(fa.interner.resolve(n)))
                .unwrap_or_else(|| "class@anonymous".to_string());
            let class_target = Type::Named {
                fqn: class_name.clone(),
                args: Vec::new(),
            };
            let class_docs = c.doc.as_deref().into_iter().collect::<Vec<_>>();
            for m in &c.members {
                let Member::Method(mth) = m else { continue };
                let Some(doc) = &mth.doc else { continue };
                let self_out_tags = doc_tag_types(doc, "self-out");
                if self_out_tags.is_empty() {
                    continue;
                }
                let mname = fa.interner.resolve(mth.name);
                if mth.modifiers.is_static {
                    out.push(
                        Diagnostic::error(
                            st.span,
                            format!(
                                "PHPDoc tag @phpstan-self-out is not supported above static method \
                                 {class_name}::{mname}()."
                            ),
                        )
                        .with_code("selfOut.static"),
                    );
                }

                let mut docs = class_docs.clone();
                docs.push(doc.as_str());
                let (templates, _) = template_context(scope, &docs);
                for tag in self_out_tags {
                    let ty = resolve_doc_type(scope, &templates, &tag);
                    if self_out_type_uncertain(&ty) {
                        continue;
                    }
                    if !crate::is_assignable(fa.reflection, &ty, &class_target) {
                        out.push(
                            Diagnostic::error(
                                st.span,
                                format!(
                                    "Self-out type {ty} of method {class_name}::{mname} is not subtype of {class_name}."
                                ),
                            )
                            .with_code("selfOut.type"),
                        );
                    }
                }
            }
        }
    });
    out
}

fn self_out_type_uncertain(t: &Type) -> bool {
    match t {
        Type::Mixed
        | Type::Unknown(_)
        | Type::TemplateVar(_)
        | Type::Object
        | Type::Intersection(_) => true,
        Type::Nullable(inner) | Type::List(inner) | Type::ClassString(Some(inner)) => {
            self_out_type_uncertain(inner)
        }
        Type::Union(parts) => parts.iter().any(self_out_type_uncertain),
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            self_out_type_uncertain(&kv.0) || self_out_type_uncertain(&kv.1)
        }
        Type::Named { args, .. } => args.iter().any(self_out_type_uncertain),
        _ => false,
    }
}

// --- requireExtends.* / requireImplements.* / sealed.* ----------------------

/// Definition-side validation for:
/// - `RequireExtendsDefinitionClassRule` / `RequireExtendsDefinitionTraitRule`
/// - `RequireImplementsDefinitionClassRule` / `RequireImplementsDefinitionTraitRule`
/// - `SealedDefinitionClassRule` / `SealedDefinitionTraitRule`
///
/// This mirrors phpstan's structural checks: placement, duplicate
/// `@require-extends`, non-object targets, unknown classes, wrong class-like
/// kinds, and final classes in `@require-extends`. The generic/case-sensitivity
/// refinements are intentionally left to their dedicated generic/name rules.
fn run_require_sealed_placement(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            let StmtKind::Class(c) = &st.kind else {
                continue;
            };
            let Some(doc) = &c.doc else { continue };
            let templates = template_names(doc);

            let require_extends = doc_tag_types(doc, "require-extends");
            if !require_extends.is_empty() {
                if !matches!(c.kind, ClassKind::Interface | ClassKind::Trait) {
                    out.push(
                        Diagnostic::error(
                            st.span,
                            "PHPDoc tag @phpstan-require-extends is only valid on trait or interface."
                                .to_string(),
                        )
                        .with_code(require_extends_id(c.kind)),
                    );
                } else {
                    check_require_extends_tags(
                        fa,
                        scope,
                        &templates,
                        &require_extends,
                        st.span,
                        &mut out,
                    );
                }
            }

            let require_implements = doc_tag_types(doc, "require-implements");
            if !require_implements.is_empty() {
                if c.kind != ClassKind::Trait {
                    out.push(
                        Diagnostic::error(
                            st.span,
                            "PHPDoc tag @phpstan-require-implements is only valid on trait."
                                .to_string(),
                        )
                        .with_code(require_implements_id(c.kind)),
                    );
                } else {
                    check_require_implements_tags(
                        fa,
                        scope,
                        &templates,
                        &require_implements,
                        st.span,
                        &mut out,
                    );
                }
            }

            let sealed = doc_tag_types(doc, "sealed");
            if !sealed.is_empty() {
                match c.kind {
                    ClassKind::Enum => out.push(
                        Diagnostic::error(
                            st.span,
                            "PHPDoc tag @phpstan-sealed is only valid on class or interface."
                                .to_string(),
                        )
                        .with_code("sealed.onEnum"),
                    ),
                    ClassKind::Trait => out.push(
                        Diagnostic::error(
                            st.span,
                            "PHPDoc tag @phpstan-sealed is only valid on class or interface."
                                .to_string(),
                        )
                        .with_code("sealed.onTrait"),
                    ),
                    ClassKind::Class | ClassKind::Interface => {
                        check_sealed_tags(fa, scope, &templates, &sealed, st.span, &mut out);
                    }
                }
            }
        }
    });
    out
}

fn check_require_extends_tags(
    fa: &FileAnalysis,
    scope: &Scope,
    templates: &[String],
    tags: &[php_phpdoc::DocType],
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    if tags.len() > 1 {
        out.push(
            Diagnostic::error(
                span,
                "PHPDoc tag @phpstan-require-extends can only be used once.".to_string(),
            )
            .with_code("requireExtends.duplicate"),
        );
    }

    for tag in tags {
        let ty = resolve_doc_type(scope, templates, tag);
        let class_names = object_class_names(&ty);
        if class_names.is_empty() {
            out.push(
                Diagnostic::error(
                    span,
                    format!("PHPDoc tag @phpstan-require-extends contains non-object type {ty}."),
                )
                .with_code("requireExtends.nonObject"),
            );
            continue;
        }
        for class in class_names {
            let Some(entry) = fa.project.class(&class) else {
                out.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "PHPDoc tag @phpstan-require-extends contains unknown class {class}."
                        ),
                    )
                    .with_code("class.notFound"),
                );
                continue;
            };
            match entry.kind {
                ClassKind::Interface => out.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "PHPDoc tag @phpstan-require-extends cannot contain an interface {class}, expected a class."
                        ),
                    )
                    .with_code("requireExtends.interface"),
                ),
                ClassKind::Trait | ClassKind::Enum => out.push(
                    Diagnostic::error(
                        span,
                        format!("PHPDoc tag @phpstan-require-extends cannot contain non-class type {class}."),
                    )
                    .with_code(require_extends_target_id(entry.kind)),
                ),
                ClassKind::Class if fa.reflection.class(&class).is_some_and(|c| c.is_final) => {
                    out.push(
                        Diagnostic::error(
                            span,
                            format!("PHPDoc tag @phpstan-require-extends cannot contain final class {class}."),
                        )
                        .with_code("requireExtends.finalClass"),
                    );
                }
                ClassKind::Class => {}
            }
        }
    }
}

fn check_require_implements_tags(
    fa: &FileAnalysis,
    scope: &Scope,
    templates: &[String],
    tags: &[php_phpdoc::DocType],
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    for tag in tags {
        let ty = resolve_doc_type(scope, templates, tag);
        let class_names = object_class_names(&ty);
        if class_names.is_empty() {
            out.push(
                Diagnostic::error(
                    span,
                    format!(
                        "PHPDoc tag @phpstan-require-implements contains non-object type {ty}."
                    ),
                )
                .with_code("requireImplements.nonObject"),
            );
            continue;
        }
        for class in class_names {
            let Some(entry) = fa.project.class(&class) else {
                out.push(
                    Diagnostic::error(
                        span,
                        format!("PHPDoc tag @phpstan-require-implements contains unknown class {class}."),
                    )
                    .with_code("class.notFound"),
                );
                continue;
            };
            if entry.kind != ClassKind::Interface {
                out.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "PHPDoc tag @phpstan-require-implements cannot contain non-interface type {class}."
                        ),
                    )
                    .with_code(require_implements_target_id(entry.kind)),
                );
            }
        }
    }
}

fn check_sealed_tags(
    fa: &FileAnalysis,
    scope: &Scope,
    templates: &[String],
    tags: &[php_phpdoc::DocType],
    span: Span,
    out: &mut Vec<Diagnostic>,
) {
    for tag in tags {
        let ty = resolve_doc_type(scope, templates, tag);
        let class_names = object_class_names(&ty);
        if class_names.is_empty() {
            out.push(
                Diagnostic::error(
                    span,
                    format!("PHPDoc tag @phpstan-sealed contains non-object type {ty}."),
                )
                .with_code("sealed.nonObject"),
            );
            continue;
        }
        for class in class_names {
            if !fa.project.has_class(&class) {
                out.push(
                    Diagnostic::error(
                        span,
                        format!("PHPDoc tag @phpstan-sealed contains unknown class {class}."),
                    )
                    .with_code("class.notFound"),
                );
            }
        }
    }
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

fn require_extends_target_id(kind: ClassKind) -> &'static str {
    match kind {
        ClassKind::Interface => "requireExtends.interface",
        ClassKind::Trait => "requireExtends.trait",
        ClassKind::Enum => "requireExtends.enum",
        ClassKind::Class => "requireExtends.class",
    }
}

fn require_implements_target_id(kind: ClassKind) -> &'static str {
    match kind {
        ClassKind::Interface => "requireImplements.interface",
        ClassKind::Trait => "requireImplements.trait",
        ClassKind::Enum => "requireImplements.enum",
        ClassKind::Class => "requireImplements.class",
    }
}

fn doc_tag_types(doc_raw: &str, base: &str) -> Vec<php_phpdoc::DocType> {
    let block = php_phpdoc::parse_block(doc_raw);
    block
        .tags
        .iter()
        .filter_map(|tag| {
            let (b, _) = strip_doc_prefix(&tag.name);
            if b != base {
                return None;
            }
            php_phpdoc::parse_type_prefix(&tag.value).map(|(ty, _)| ty)
        })
        .collect()
}

fn object_class_names(t: &Type) -> Vec<String> {
    let mut out = Vec::new();
    collect_object_class_names(t, &mut out);
    out
}

fn collect_object_class_names(t: &Type, out: &mut Vec<String>) {
    match t {
        Type::Named { fqn, .. } => out.push(fqn.clone()),
        Type::Nullable(inner) => collect_object_class_names(inner, out),
        Type::Union(parts) | Type::Intersection(parts) => {
            for p in parts {
                collect_object_class_names(p, out);
            }
        }
        _ => {}
    }
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
            let display = c
                .name
                .map(|n| scope.qualify(fa.interner.resolve(n)))
                .unwrap_or_default();
            for p in &doc.properties {
                let Some(dt) = &p.ty else { continue };
                let ty = resolve_doc_type(scope, &templates, dt);
                let pname = p.name.clone().unwrap_or_default();
                let d2 = display.clone();
                check_tag_classes(
                    fa,
                    &ty,
                    st.span,
                    "propertyTag.trait",
                    move |c, kind| {
                        format!("PHPDoc tag @property for property {d2}::${pname} contains {kind} class {c}.")
                    },
                    out,
                );
            }
            for m in &doc.methods {
                let Some(rt) = &m.return_type else { continue };
                let ty = resolve_doc_type(scope, &templates, rt);
                let mname = m.name.clone();
                let d2 = display.clone();
                check_tag_classes(
                    fa,
                    &ty,
                    st.span,
                    "methodTag.trait",
                    move |c, kind| {
                        format!("PHPDoc tag @method for method {d2}::{mname}() contains {kind} class {c}.")
                    },
                    out,
                );
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
    RuleEntry {
        name: "phpdoc.mixin",
        level: 2,
        run: run_mixin,
    },
    RuleEntry {
        name: "phpdoc.tagClassRefs",
        level: 2,
        run: run_tag_class_refs,
    },
    RuleEntry {
        name: "phpdoc.paramTags",
        level: 2,
        run: run_param_tags,
    },
    RuleEntry {
        name: "phpdoc.varTags",
        level: 2,
        run: run_var_tags,
    },
    RuleEntry {
        name: "phpdoc.phpstanTag",
        level: 2,
        run: run_phpstan_tags,
    },
    RuleEntry {
        name: "phpdoc.invalidTagValue",
        level: 2,
        run: run_invalid_tag_values,
    },
    RuleEntry {
        name: "phpdoc.assertTags",
        level: 2,
        run: run_assert_tags,
    },
    RuleEntry {
        name: "phpdoc.conditionalReturnTypes",
        level: 2,
        run: run_conditional_return_types,
    },
    RuleEntry {
        name: "phpdoc.incompatibleType",
        level: 2,
        run: run_incompatible_types,
    },
    RuleEntry {
        name: "phpdoc.paramInvokedCallable",
        level: 2,
        run: run_param_invoked_callable_tags,
    },
    RuleEntry {
        name: "phpdoc.paramOut",
        level: 2,
        run: run_param_out_tags,
    },
    RuleEntry {
        name: "phpdoc.propertyType",
        level: 2,
        run: run_property_phpdoc_type,
    },
    RuleEntry {
        name: "phpdoc.propertyHookType",
        level: 2,
        run: run_property_hook_phpdoc_type,
    },
    RuleEntry {
        name: "phpdoc.classConstType",
        level: 2,
        run: run_class_const_phpdoc_type,
    },
    RuleEntry {
        name: "phpdoc.throwsNotThrowable",
        level: 2,
        run: run_throws_not_throwable,
    },
    RuleEntry {
        name: "phpdoc.varTagTrait",
        level: 2,
        run: run_var_tag_trait,
    },
    RuleEntry {
        name: "phpdoc.varTagMissingType",
        level: 6,
        run: run_var_tag_missing_types,
    },
    RuleEntry {
        name: "phpdoc.varTagChangedExpressionType",
        level: 2,
        run: run_var_tag_changed_expression_type,
    },
    RuleEntry {
        name: "phpdoc.selfOut",
        level: 2,
        run: run_self_out,
    },
    RuleEntry {
        name: "phpdoc.requireSealedPlacement",
        level: 2,
        run: run_require_sealed_placement,
    },
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

    // --- phpDoc.parseError ---

    #[test]
    fn invalid_empty_return_tag_value_is_flagged() {
        let src = "<?php /** @return */ function f() {}";
        assert_eq!(codes(src, run_invalid_tag_values), ["phpDoc.parseError"]);
    }

    #[test]
    fn invalid_var_tag_without_type_is_flagged() {
        let src = "<?php /** @var $x */ $x = 1;";
        assert_eq!(codes(src, run_invalid_tag_values), ["phpDoc.parseError"]);
    }

    #[test]
    fn typeless_param_tag_is_not_parse_error() {
        let src = "<?php /** @param $x legacy */ function f($x) {}";
        assert!(codes(src, run_invalid_tag_values).is_empty());
    }

    // --- FunctionAssertRule / MethodAssertRule ---

    #[test]
    fn assert_referencing_unknown_parameter_is_flagged() {
        let src = "<?php /** @phpstan-assert int $missing */ function f(int $x): void {}";
        assert_eq!(codes(src, run_assert_tags), ["parameter.notFound"]);
    }

    #[test]
    fn assert_that_does_not_narrow_native_param_is_flagged() {
        let src = "<?php /** @phpstan-assert int $x */ function f(int $x): void {}";
        assert_eq!(codes(src, run_assert_tags), ["assert.alreadyNarrowedType"]);
    }

    #[test]
    fn impossible_assertion_against_native_param_is_flagged() {
        let src = "<?php /** @phpstan-assert string $x */ function f(int $x): void {}";
        assert_eq!(codes(src, run_assert_tags), ["assert.impossibleType"]);
    }

    #[test]
    fn refined_assertion_is_skipped_when_model_collapses_it() {
        let src = "<?php /** @phpstan-assert positive-int $x */ function f(int $x): void {}";
        assert!(codes(src, run_assert_tags).is_empty());
    }

    #[test]
    fn method_assert_allows_this_on_instance_methods() {
        let src = "<?php class C { /** @phpstan-assert !null $this */ function f(): void {} }";
        assert!(codes(src, run_assert_tags).is_empty());
    }

    // --- FunctionConditionalReturnTypeRule / MethodConditionalReturnTypeRule ---

    #[test]
    fn conditional_return_unknown_parameter_is_flagged() {
        let src = "<?php /** @return ($missing is int ? string : int) */ function f(int $x) {}";
        assert_eq!(
            codes(src, run_conditional_return_types),
            ["parameter.notFound"]
        );
    }

    #[test]
    fn conditional_return_subject_not_template_is_flagged() {
        let src = "<?php /** @return (stdClass is object ? string : int) */ function f() {}";
        assert_eq!(
            codes(src, run_conditional_return_types),
            ["conditionalType.subjectNotFound"]
        );
    }

    #[test]
    fn conditional_return_always_true_is_flagged() {
        let src = "<?php /** @return ($x is int ? string : int) */ function f(int $x) {}";
        assert_eq!(
            codes(src, run_conditional_return_types),
            ["conditionalType.alwaysTrue"]
        );
    }

    #[test]
    fn conditional_return_always_false_is_flagged() {
        let src = "<?php /** @return ($x is string ? string : int) */ function f(int $x) {}";
        assert_eq!(
            codes(src, run_conditional_return_types),
            ["conditionalType.alwaysFalse"]
        );
    }

    #[test]
    fn conditional_return_template_bound_is_checked() {
        let src = "<?php /** @template T of int\n * @param T $x\n * @return (T is int ? string : int) */ function f($x) {}";
        assert_eq!(
            codes(src, run_conditional_return_types),
            ["conditionalType.alwaysTrue"]
        );
    }

    #[test]
    fn conditional_return_unbound_template_is_skipped() {
        let src = "<?php /** @template T\n * @param T $x\n * @return (T is int ? string : int) */ function f($x) {}";
        assert!(codes(src, run_conditional_return_types).is_empty());
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

    // --- IncompatibleParamImmediatelyInvokedCallableRule ---

    #[test]
    fn immediately_invoked_callable_unknown_param_is_flagged() {
        let src =
            "<?php /** @param-immediately-invoked-callable $missing */ function f(callable $cb) {}";
        assert_eq!(
            codes(src, run_param_invoked_callable_tags),
            ["parameter.notFound"]
        );
    }

    #[test]
    fn later_invoked_callable_non_callable_int_is_flagged() {
        let src = "<?php /** @param-later-invoked-callable $x */ function f(int $x) {}";
        assert_eq!(
            codes(src, run_param_invoked_callable_tags),
            ["paramLaterInvokedCallable.nonCallable"]
        );
    }

    #[test]
    fn immediately_invoked_callable_native_callable_is_clean() {
        let src =
            "<?php /** @param-immediately-invoked-callable $cb */ function f(callable $cb) {}";
        assert!(codes(src, run_param_invoked_callable_tags).is_empty());
    }

    #[test]
    fn immediately_invoked_callable_string_is_skipped_as_maybe_callable() {
        let src = "<?php /** @param-immediately-invoked-callable $cb */ function f(string $cb) {}";
        assert!(codes(src, run_param_invoked_callable_tags).is_empty());
    }

    // --- property.phpDocType ---

    #[test]
    fn property_var_incompatible_with_native_is_flagged() {
        let src = "<?php class C { /** @var string */ public int $x; }";
        assert_eq!(
            codes(src, run_property_phpdoc_type),
            ["property.phpDocType"]
        );
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
        assert_eq!(
            codes(src, run_property_phpdoc_type),
            ["property.phpDocType"]
        );
    }

    // --- property-hook parameter.phpDocType / return.phpDocType ---

    #[test]
    fn hook_return_phpdoc_type_is_checked_against_property_type() {
        let src = r#"<?php
            class C {
                public int $p {
                    /** @return string */
                    get => "x";
                }
            }"#;
        assert_eq!(
            codes(src, run_property_hook_phpdoc_type),
            ["return.phpDocType"]
        );
    }

    #[test]
    fn hook_param_phpdoc_type_is_checked_against_explicit_set_param() {
        let src = r#"<?php
            class C {
                public int $p {
                    /** @param string $value */
                    set(int $value) {}
                }
            }"#;
        assert_eq!(
            codes(src, run_property_hook_phpdoc_type),
            ["parameter.phpDocType"]
        );
    }

    #[test]
    fn hook_param_phpdoc_type_uses_implicit_set_value() {
        let src = r#"<?php
            class C {
                public int $p {
                    /** @param string $value */
                    set {}
                }
            }"#;
        assert_eq!(
            codes(src, run_property_hook_phpdoc_type),
            ["parameter.phpDocType"]
        );
    }

    #[test]
    fn property_docblock_does_not_count_as_hook_docblock() {
        let src = r#"<?php
            class C {
                /** @return string */
                public int $p {
                    get => 1;
                }
            }"#;
        assert!(codes(src, run_property_hook_phpdoc_type).is_empty());
    }

    // --- classConstant.phpDocType ---

    #[test]
    fn class_const_var_incompatible_with_native_is_flagged() {
        let src = "<?php class C { /** @var string */ const int X = 1; }";
        assert_eq!(
            codes(src, run_class_const_phpdoc_type),
            ["classConstant.phpDocType"]
        );
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
        assert_eq!(
            codes(src, run_throws_not_throwable),
            ["throws.notThrowable"]
        );
    }

    #[test]
    fn throws_array_is_flagged() {
        let src = "<?php /** @throws string[] */ function f() {}";
        assert_eq!(
            codes(src, run_throws_not_throwable),
            ["throws.notThrowable"]
        );
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
        assert_eq!(
            codes(src, run_throws_not_throwable),
            ["throws.notThrowable"]
        );
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

    // --- missingType.* for inline @var ---

    #[test]
    fn inline_var_bare_array_is_flagged() {
        let src = "<?php /** @var array $x */ $x = [];";
        assert_eq!(
            codes(src, run_var_tag_missing_types),
            ["missingType.iterableValue"]
        );
    }

    #[test]
    fn inline_var_typed_array_is_clean() {
        let src = "<?php /** @var array<int, string> $x */ $x = [];";
        assert!(codes(src, run_var_tag_missing_types).is_empty());
    }

    #[test]
    fn inline_var_bare_callable_is_flagged() {
        let src = "<?php /** @var callable $cb */ $cb = 'strlen';";
        assert_eq!(
            codes(src, run_var_tag_missing_types),
            ["missingType.callable"]
        );
    }

    #[test]
    fn inline_var_callable_signature_is_clean() {
        let src = "<?php /** @var callable(string): int $cb */ $cb = 'strlen';";
        assert!(codes(src, run_var_tag_missing_types).is_empty());
    }

    #[test]
    fn inline_var_generic_class_without_args_is_flagged() {
        let src = r#"<?php
            /** @template T */
            class Box {}
            /** @var Box $box */
            $box = new Box();
        "#;
        assert_eq!(
            codes(src, run_var_tag_missing_types),
            ["missingType.generics"]
        );
    }

    #[test]
    fn inline_var_generic_class_with_args_is_clean() {
        let src = r#"<?php
            /** @template T */
            class Box {}
            /** @var Box<int> $box */
            $box = new Box();
        "#;
        assert!(codes(src, run_var_tag_missing_types).is_empty());
    }

    #[test]
    fn inline_var_unknown_class_is_not_missing_generics() {
        let src = "<?php /** @var Missing $x */ $x = null;";
        assert!(codes(src, run_var_tag_missing_types).is_empty());
    }

    #[test]
    fn misplaced_var_on_function_is_not_missing_type() {
        let src = "<?php /** @var array $x */ function f(): void {}";
        assert!(codes(src, run_var_tag_missing_types).is_empty());
    }

    #[test]
    fn inline_var_template_name_shadows_generic_class() {
        let src = r#"<?php
            /** @template U */
            class T {}
            /** @template T */
            function f($x): void {
                /** @var T $x */
                $x = $x;
            }
        "#;
        assert!(codes(src, run_var_tag_missing_types).is_empty());
    }

    #[test]
    fn inline_var_self_generic_without_args_is_flagged() {
        let src = r#"<?php
            /** @template T */
            class Box {
                public function m(): void {
                    /** @var self $box */
                    $box = $this;
                }
            }
        "#;
        assert_eq!(
            codes(src, run_var_tag_missing_types),
            ["missingType.generics"]
        );
    }

    // --- VarTagChangedExpressionTypeRule ---

    #[test]
    fn inline_var_return_param_incompatible_with_native_is_flagged() {
        let src = "<?php function f(int $x) { /** @var string */ return $x; }";
        assert_eq!(
            codes(src, run_var_tag_changed_expression_type),
            ["varTag.nativeType"]
        );
    }

    #[test]
    fn inline_var_if_param_incompatible_with_native_is_flagged() {
        let src = "<?php function f(int $x) { /** @var string $x */ if ($x) {} }";
        assert_eq!(
            codes(src, run_var_tag_changed_expression_type),
            ["varTag.nativeType"]
        );
    }

    #[test]
    fn inline_var_return_param_subtype_of_native_is_clean() {
        let src = "<?php function f(?int $x) { /** @var int */ return $x; }";
        assert!(codes(src, run_var_tag_changed_expression_type).is_empty());
    }

    #[test]
    fn inline_var_reassigned_param_is_skipped() {
        let src = "<?php function f(int $x) { $x = 's'; /** @var string */ return $x; }";
        assert!(codes(src, run_var_tag_changed_expression_type).is_empty());
    }

    #[test]
    fn inline_var_untyped_param_with_param_doc_is_checked_as_phpdoc_type() {
        let src = "<?php /** @param int $x */ function f($x) { /** @var string */ return $x; }";
        assert_eq!(
            codes(src, run_var_tag_changed_expression_type),
            ["varTag.type"]
        );
    }

    // --- selfOut.static ---

    #[test]
    fn self_out_on_static_method_is_flagged() {
        let src = "<?php class C { /** @phpstan-self-out static */ public static function m() {} }";
        assert_eq!(codes(src, run_self_out), ["selfOut.static"]);
    }

    #[test]
    fn self_out_on_instance_method_is_clean() {
        let src = "<?php class C { /** @phpstan-self-out static */ public function m() {} }";
        assert!(codes(src, run_self_out).is_empty());
    }

    #[test]
    fn self_out_scalar_type_is_flagged() {
        let src = "<?php class C { /** @phpstan-self-out int */ public function m() {} }";
        assert_eq!(codes(src, run_self_out), ["selfOut.type"]);
    }

    #[test]
    fn self_out_nullable_self_is_flagged() {
        let src = "<?php class C { /** @phpstan-self-out self|null */ public function m() {} }";
        assert_eq!(codes(src, run_self_out), ["selfOut.type"]);
    }

    #[test]
    fn self_out_unknown_named_type_is_skipped() {
        let src = "<?php class C { /** @phpstan-self-out Missing */ public function m() {} }";
        assert!(codes(src, run_self_out).is_empty());
    }

    // --- requireExtends / requireImplements / sealed placement ---

    #[test]
    fn require_extends_on_class_is_flagged() {
        let src = "<?php /** @phpstan-require-extends \\Foo */ class C {}";
        assert_eq!(
            codes(src, run_require_sealed_placement),
            ["requireExtends.onClass"]
        );
    }

    #[test]
    fn require_extends_on_interface_is_clean() {
        let src = "<?php class Foo {} /** @phpstan-require-extends \\Foo */ interface I {}";
        assert!(codes(src, run_require_sealed_placement).is_empty());
    }

    #[test]
    fn require_extends_on_trait_is_clean() {
        let src = "<?php class Foo {} /** @phpstan-require-extends \\Foo */ trait T {}";
        assert!(codes(src, run_require_sealed_placement).is_empty());
    }

    #[test]
    fn require_extends_on_trait_rejects_interface() {
        let src = "<?php interface Foo {} /** @phpstan-require-extends \\Foo */ trait T {}";
        assert_eq!(
            codes(src, run_require_sealed_placement),
            ["requireExtends.interface"]
        );
    }

    #[test]
    fn require_extends_on_interface_rejects_trait() {
        let src = "<?php trait Foo {} /** @phpstan-require-extends \\Foo */ interface I {}";
        assert_eq!(
            codes(src, run_require_sealed_placement),
            ["requireExtends.trait"]
        );
    }

    #[test]
    fn require_extends_rejects_final_class() {
        let src = "<?php final class Foo {} /** @phpstan-require-extends \\Foo */ interface I {}";
        assert_eq!(
            codes(src, run_require_sealed_placement),
            ["requireExtends.finalClass"]
        );
    }

    #[test]
    fn require_extends_duplicate_is_flagged() {
        let src = "<?php class A {} class B {} /**
         * @phpstan-require-extends A
         * @phpstan-require-extends B
         */ trait T {}";
        assert_eq!(
            codes(src, run_require_sealed_placement),
            ["requireExtends.duplicate"]
        );
    }

    #[test]
    fn require_extends_non_object_is_flagged() {
        let src = "<?php /** @phpstan-require-extends int */ trait T {}";
        assert_eq!(
            codes(src, run_require_sealed_placement),
            ["requireExtends.nonObject"]
        );
    }

    #[test]
    fn require_implements_on_class_is_flagged() {
        let src = "<?php /** @phpstan-require-implements \\Foo */ class C {}";
        assert_eq!(
            codes(src, run_require_sealed_placement),
            ["requireImplements.onClass"]
        );
    }

    #[test]
    fn require_implements_on_trait_is_clean() {
        let src = "<?php interface Foo {} /** @phpstan-require-implements \\Foo */ trait T {}";
        assert!(codes(src, run_require_sealed_placement).is_empty());
    }

    #[test]
    fn require_implements_rejects_class() {
        let src = "<?php class Foo {} /** @phpstan-require-implements \\Foo */ trait T {}";
        assert_eq!(
            codes(src, run_require_sealed_placement),
            ["requireImplements.class"]
        );
    }

    #[test]
    fn require_implements_non_object_is_flagged() {
        let src = "<?php /** @phpstan-require-implements int */ trait T {}";
        assert_eq!(
            codes(src, run_require_sealed_placement),
            ["requireImplements.nonObject"]
        );
    }

    #[test]
    fn sealed_on_enum_is_flagged() {
        let src = "<?php /** @phpstan-sealed A|B */ enum E {}";
        assert_eq!(codes(src, run_require_sealed_placement), ["sealed.onEnum"]);
    }

    #[test]
    fn sealed_on_class_is_clean() {
        let src = "<?php class A {} class B {} /** @phpstan-sealed A|B */ class C {}";
        assert!(codes(src, run_require_sealed_placement).is_empty());
    }

    #[test]
    fn sealed_on_trait_is_flagged() {
        let src = "<?php /** @phpstan-sealed A */ trait T {}";
        assert_eq!(codes(src, run_require_sealed_placement), ["sealed.onTrait"]);
    }

    #[test]
    fn sealed_unknown_class_is_flagged() {
        let src = "<?php /** @phpstan-sealed Missing */ class C {}";
        assert_eq!(codes(src, run_require_sealed_placement), ["class.notFound"]);
    }

    #[test]
    fn sealed_non_object_is_flagged() {
        let src = "<?php /** @phpstan-sealed int */ interface I {}";
        assert_eq!(
            codes(src, run_require_sealed_placement),
            ["sealed.nonObject"]
        );
    }
}
