//! Shared primitives for the `@param-out` rule family.
//!
//! Two rule files check `@param-out` tags from opposite directions —
//! `variables.rs` reports a tag the body contradicts (`paramOut.type`) and
//! `too_wide_typehints.rs` reports a tag wider than the body ever produces
//! (`paramOut.unusedType`) — so both need the same reading of the tag, the same
//! notion of a body simple enough to trust, and the same rendering in messages.
//!
//! They used to carry private copies of all of it. Copies of a *predicate* are
//! how two rules quietly come to disagree about the same source: one gains a
//! `Type` arm the other lacks and the pair starts reporting contradictory things
//! about one tag. Keeping the reading in one place makes that impossible rather
//! than merely unlikely.

use crate::FileAnalysis;
use php_ast::{Expr, ExprKind, Param, Stmt, StmtKind};
use php_infer::TypeCtx;
use php_intern::Interner;
use php_reflect::{resolve_doc_type, ParamReflection};
use php_resolve::Scope;
use php_types::Type;
use std::collections::HashMap;

/// One `@param-out` tag: the parameter it names and the type it promises.
pub(crate) struct ParamOutType {
    pub(crate) name: String,
    pub(crate) ty: Type,
}

/// The `@param-out` tags on a docblock, resolved against `scope`.
///
/// `@psalm-param-out` is skipped outright (phpstan does not honour it), and
/// where a parameter is named more than once the highest-priority tag wins —
/// `@phpstan-param-out` over the plain form.
pub(crate) fn param_out_types(
    scope: &Scope,
    doc: Option<&str>,
    templates: &[String],
) -> Vec<ParamOutType> {
    let Some(raw) = doc else {
        return Vec::new();
    };
    let mut out: Vec<(i8, ParamOutType)> = Vec::new();
    for tag in php_phpdoc::parse_block(raw).tags {
        let (base, pri) = php_phpdoc::query::base_priority(&tag.name);
        if base != "param-out" || pri == 1 {
            continue;
        }
        let parsed = php_phpdoc::parse(&format!("/** @param {} */", tag.value));
        let Some(param) = parsed.params.first() else {
            continue;
        };
        let (Some(name), Some(doc_ty)) = (&param.name, &param.ty) else {
            continue;
        };
        let ty = resolve_doc_type(scope, templates, doc_ty);
        if let Some(existing) = out.iter_mut().find(|(_, p)| p.name == *name) {
            if pri >= existing.0 {
                *existing = (
                    pri,
                    ParamOutType {
                        name: name.clone(),
                        ty,
                    },
                );
            }
        } else {
            out.push((
                pri,
                ParamOutType {
                    name: name.clone(),
                    ty,
                },
            ));
        }
    }
    out.into_iter().map(|(_, p)| p).collect()
}

/// The final type of every variable in a body, but **only** for bodies simple
/// enough that "final" is unambiguous: a straight line of assignments whose
/// right-hand sides are self-evident.
///
/// Returns `None` the moment the body does anything else — a branch, a loop, a
/// call. Both consumers report on the gap between a tag and reality, so a body
/// they cannot fully account for must produce no verdict at all rather than a
/// guessed one.
pub(crate) fn straight_line_final_vars(
    body: &[Stmt],
    params: &[ParamReflection],
    scope: &Scope,
    class_fqn: Option<&str>,
    fa: &FileAnalysis,
) -> Option<HashMap<String, Type>> {
    let mut ctx = TypeCtx::new(fa.reflection, scope, fa.interner);
    ctx.class = class_fqn.map(ToString::to_string);
    for p in params {
        ctx.vars.insert(p.name.clone(), p.local_type());
    }

    for st in body {
        match &st.kind {
            StmtKind::Nop => {}
            StmtKind::Expr(e) => {
                let (name, rhs) = direct_variable_assignment(e, fa)?;
                if !rhs_is_obvious(rhs) {
                    return None;
                }
                let ty = ctx.infer(rhs);
                ctx.vars.insert(name, ty);
            }
            _ => return None,
        }
    }

    Some(ctx.vars)
}

/// `$x = <rhs>` (through parentheses), if the target is a plain variable.
pub(crate) fn direct_variable_assignment<'a>(
    e: &'a Expr,
    fa: &FileAnalysis,
) -> Option<(String, &'a Expr)> {
    match &e.kind {
        ExprKind::Paren(inner) => direct_variable_assignment(inner, fa),
        ExprKind::Assign { target, rhs } => match &target.kind {
            ExprKind::Variable(sym) => Some((fa.interner.resolve(*sym).to_string(), rhs)),
            _ => None,
        },
        _ => None,
    }
}

/// Whether an expression's type is evident from its syntax alone — no call, no
/// member access, nothing whose type depends on analysis that could be wrong.
pub(crate) fn rhs_is_obvious(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Paren(inner) => rhs_is_obvious(inner),
        ExprKind::Int(_) | ExprKind::Float(_) | ExprKind::Str(_) | ExprKind::Interpolated(_) => {
            true
        }
        ExprKind::Variable(_) => true,
        ExprKind::Name(n) => matches!(
            n.text.to_ascii_lowercase().as_str(),
            "true" | "false" | "null"
        ),
        ExprKind::Array { items, .. } => items.iter().all(|item| {
            !item.by_ref
                && !item.spread
                && item.key.as_ref().is_none_or(rhs_is_obvious)
                && item.value.as_ref().is_none_or(rhs_is_obvious)
        }),
        ExprKind::Unary { expr, .. } | ExprKind::Cast { expr, .. } => rhs_is_obvious(expr),
        ExprKind::Binary { lhs, rhs, .. } => rhs_is_obvious(lhs) && rhs_is_obvious(rhs),
        _ => false,
    }
}

/// Whether a type is too imprecise to compare a `@param-out` tag against.
///
/// Exhaustive over `Type` by construction: a new variant will not compile until
/// it is classified here, which is the point of listing the certain arms out
/// rather than ending in a wildcard.
pub(crate) fn type_is_uncertain(ty: &Type) -> bool {
    match ty {
        Type::Mixed
        | Type::ExplicitMixed
        | Type::Never
        | Type::Void
        | Type::SelfType
        | Type::StaticType
        | Type::Parent
        | Type::TemplateVar(_)
        | Type::Conditional { .. }
        | Type::Unknown(_) => true,
        Type::Nullable(inner)
        | Type::List(inner)
        | Type::ClassString(Some(inner))
        | Type::NonEmpty(inner) => type_is_uncertain(inner),
        Type::Union(parts) | Type::Intersection(parts) => parts.iter().any(type_is_uncertain),
        Type::Array(Some(pair)) | Type::Iterable(Some(pair)) => {
            type_is_uncertain(&pair.0) || type_is_uncertain(&pair.1)
        }
        Type::Shape { fields, .. } => fields.iter().any(|f| type_is_uncertain(&f.ty)),
        Type::Callable(Some(sig)) => {
            sig.params.iter().any(type_is_uncertain) || type_is_uncertain(&sig.ret)
        }
        Type::Named { args, .. } => args.iter().any(type_is_uncertain),
        Type::Array(None)
        | Type::Iterable(None)
        | Type::Callable(None)
        | Type::ClassString(None)
        | Type::Null
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Int
        | Type::IntRange { .. }
        | Type::Float
        | Type::String
        | Type::StringOf(_)
        | Type::Object
        | Type::Resource
        | Type::LiteralInt(_)
        | Type::LiteralString(_)
        | Type::EnumCase { .. } => false,
    }
}

/// Render a type the way phpstan writes it in a message: a nullable is spelled
/// as an explicit `|null` union rather than with a leading `?`.
pub(crate) fn phpstan_type(ty: &Type) -> String {
    match ty {
        Type::Nullable(inner) => format!("{}|null", phpstan_type(inner)),
        Type::Union(parts) => parts.iter().map(phpstan_type).collect::<Vec<_>>().join("|"),
        other => other.to_string(),
    }
}

/// The span of the named parameter's declaration, to anchor a diagnostic on.
pub(crate) fn param_decl_span(
    params: &[Param],
    name: &str,
    interner: &Interner,
) -> Option<php_span::Span> {
    params
        .iter()
        .find(|p| interner.resolve(p.name) == name)
        .map(|p| p.span)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `@phpstan-param-out` outranks the plain tag, and `@psalm-param-out` is
    /// ignored entirely — the precedence both rules must agree on.
    #[test]
    fn tag_precedence_matches_phpstan() {
        let scope = Scope::global();
        let doc = "/**\n * @param-out int $a\n * @phpstan-param-out string $a\n */";
        let outs = param_out_types(&scope, Some(doc), &[]);
        assert_eq!(outs.len(), 1);
        assert_eq!(outs[0].name, "a");
        assert_eq!(outs[0].ty.to_string(), "string");

        let psalm = "/**\n * @psalm-param-out string $a\n */";
        assert!(param_out_types(&scope, Some(psalm), &[]).is_empty());
    }

    #[test]
    fn uncertain_types_are_recognised_through_containers() {
        assert!(type_is_uncertain(&Type::Mixed));
        assert!(type_is_uncertain(&Type::Nullable(Box::new(Type::Mixed))));
        assert!(type_is_uncertain(&Type::List(Box::new(Type::Mixed))));
        assert!(!type_is_uncertain(&Type::Int));
        assert!(!type_is_uncertain(&Type::List(Box::new(Type::Int))));
    }

    #[test]
    fn nullable_renders_as_an_explicit_union() {
        assert_eq!(
            phpstan_type(&Type::Nullable(Box::new(Type::Int))),
            "int|null"
        );
        assert_eq!(phpstan_type(&Type::Int), "int");
    }
}
