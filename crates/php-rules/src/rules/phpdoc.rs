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
//!
//! Deferred (need machinery our pipeline doesn't yet expose):
//! - `InvalidPhpDocTagValueRule` (`phpDoc.parseError`): phpstan reports the
//!   *parse exception* from its own PHPDoc parser. Our `php_phpdoc` parser is
//!   intentionally lenient (malformed operands yield `None`/empty rather than a
//!   structured error with a message), so we cannot reproduce phpstan's
//!   "has invalid value (...): <exception message>" wording faithfully.
//! - `varTag.unknownClass` / `InvalidPhpDocVarTagTypeRule`: still need a
//!   "does this class exist?" query at the `@var` doc/native boundary (the
//!   `@param`/`@return` subtype check is now done — see above).
//! - `parameter.notByRef`: phpstan emits this for `@param-out` tags on a
//!   non-by-ref parameter. Our `php_phpdoc` model does not surface `@param-out`
//!   as a distinct tag, so the rule is deferred (emitting it for `@param &$x`
//!   would be the wrong semantics).
//! - `InvalidThrowsPhpDocValueRule` (`throws.notThrowable`): needs to know
//!   whether the `@throws` type is a `Throwable` subtype — a type/reflection
//!   query, deferred to the type-rule wave.
//! - `Require*`/`Sealed*` definition rules: depend on `@require-extends` /
//!   `@sealed` tags our `php_phpdoc` model does not yet surface.

#![allow(unused_imports)]
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{ClassDecl, FunctionDecl, Member, MethodDecl, Param, PropertyDecl, StmtKind};
use php_diagnostics::Diagnostic;
use php_intern::Interner;
use php_reflect::{resolve_ast_type, resolve_doc_type};
use php_resolve::{for_each_region, Scope};
use php_span::Span;
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

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry { name: "phpdoc.paramTags", level: 2, run: run_param_tags },
    RuleEntry { name: "phpdoc.varTags", level: 2, run: run_var_tags },
    RuleEntry { name: "phpdoc.phpstanTag", level: 2, run: run_phpstan_tags },
    RuleEntry { name: "phpdoc.incompatibleType", level: 2, run: run_incompatible_types },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

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
}
