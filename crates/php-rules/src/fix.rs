//! Fix computation for `--fix`: rendering inferred [`Type`]s as PHPDoc text and
//! anchoring [`DocTagFix`]es on declarations.
//!
//! The low-false-positive contract extends to fixes: a tag is attached only when
//! the type is non-trivial evidence ([`php_infer::useful_inference`]) *and*
//! renderable as valid PHPDoc ([`render_phpdoc`]); anything uncertain produces no
//! fix and the finding reports as before. Known accepted V1 gap: modifiers split
//! across lines (`public\nstatic\nfunction f`) anchor on the keyword line, placing
//! the docblock between the modifier and the rest — vanishingly rare style, still
//! parses.

use crate::FileAnalysis;
use php_ast::{Expr, Name, NameFq};
use php_diagnostics::{DocTagFix, DocTagKind, FixAnchor};
use php_resolve::{Resolution, Scope};
use php_span::Span;
use php_types::Type;

/// Render `ty` as PHPDoc text valid at `scope`, or `None` when any part of the
/// type is unrenderable or context-dependent. Class names are emitted as their
/// short name when that round-trips through the file's imports/namespace, else
/// as a fully-qualified `\`-prefixed name (bare qualified names in PHPDoc would
/// resolve relative to the namespace — wrong).
pub(crate) fn render_phpdoc(ty: &Type, scope: &Scope) -> Option<String> {
    render_phpdoc_mode(ty, scope, false)
}

fn render_phpdoc_mode(ty: &Type, scope: &Scope, container_mixed: bool) -> Option<String> {
    if matches!(ty, Type::Null) || !renderable_in(ty, container_mixed, false) {
        return None;
    }
    let display = ty.clone().map(&mut |t| match t {
        Type::Named { fqn, args } => Type::Named {
            fqn: display_name(&fqn, scope).into(),
            args,
        },
        other => other,
    });
    Some(display.to_string())
}

/// Whether every node of `ty` has a faithful, context-free PHPDoc rendering,
/// with a positional relaxation: when `container_mixed` is set,
/// `mixed` is accepted *inside* a container slot (`in_container`) — the
/// evidenced-structure-with-unknown-values shape (`array<string, mixed>`) that
/// the `missingType.iterableValue` fix writes — but never as the whole type.
fn renderable_in(ty: &Type, container_mixed: bool, in_container: bool) -> bool {
    let inner = |t: &Type| renderable_in(t, container_mixed, in_container);
    let slot = |t: &Type| renderable_in(t, container_mixed, true);
    match ty {
        Type::Mixed | Type::ExplicitMixed => container_mixed && in_container,
        // No information, bottom/return-position types, or context-dependent
        // names — never write these into a docblock we synthesize.
        Type::Never
        | Type::Void
        | Type::Unknown(_)
        | Type::TemplateVar(_)
        | Type::Conditional { .. }
        | Type::SelfType
        | Type::StaticType
        | Type::Parent
        // A case type renders as `Suit::Hearts`; our own doc grammar doesn't
        // round-trip const-fetch types yet, so don't write them.
        | Type::EnumCase { .. }
        | Type::IntRange { .. } => false,
        // `?A|B` renders ambiguously; the union smart constructor flattens these
        // away, so reject the stray shape rather than re-parenthesize.
        Type::Nullable(x) => {
            !matches!(**x, Type::Union(_) | Type::Intersection(_)) && inner(x)
        }
        // A literal string renders as `'…'`; reject contents that would break
        // the quoting or the surrounding comment.
        Type::LiteralString(s) => {
            !s.contains(['\'', '\\', '\n', '\r']) && !s.contains("*/")
        }
        // An *unsealed* empty shape (`array{...}`) is just bare `array` in
        // disguise — never write it. (A sealed `array{}` is exactly-empty and
        // fine.)
        Type::Shape { fields, sealed } => {
            (*sealed || !fields.is_empty())
                && fields.iter().all(|f| {
                    f.key.as_deref().is_none_or(plain_shape_key) && slot(&f.ty)
                })
        }
        Type::Array(kv) | Type::Iterable(kv) => kv
            .as_deref()
            .is_none_or(|(k, v)| slot(k) && slot(v)),
        Type::List(x) => slot(x),
        // `class-string<mixed>` is meaningless, and `NonEmpty` wraps the whole
        // container (its inner is not a value slot).
        Type::ClassString(Some(x)) | Type::NonEmpty(x) => inner(x),
        Type::Callable(sig) => sig
            .as_deref()
            .is_none_or(|s| s.params.iter().all(inner) && inner(&s.ret)),
        Type::Named { args, .. } => args.iter().all(slot),
        // `string|mixed` in a slot would be dishonest noise — a union arm of
        // `mixed` must have been absorbed by the caller, so reject it here.
        Type::Union(parts) | Type::Intersection(parts) => {
            !parts.is_empty()
                && !parts
                    .iter()
                    .any(|p| matches!(p, Type::Mixed | Type::ExplicitMixed))
                && parts.iter().all(inner)
        }
        _ => true,
    }
}

/// A shape key that renders back to parseable PHPDoc (identifier or number).
fn plain_shape_key(key: &str) -> bool {
    !key.is_empty()
        && (key.chars().all(|c| c.is_ascii_digit())
            || (key
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                && key.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')))
}

/// The docblock spelling of class `fqn` at `scope`: the short last segment when
/// resolving it round-trips to the same FQN (imported, or in this namespace),
/// else `\`-prefixed fully-qualified.
fn display_name(fqn: &str, scope: &Scope) -> String {
    let short = fqn.rsplit('\\').next().unwrap_or(fqn);
    let probe = Name {
        span: Span::new(0, 0),
        fq: NameFq::NotFq,
        text: short.to_string(),
    };
    if let Resolution::Fqn(resolved) = scope.resolve_class(&probe) {
        if resolved.eq_ignore_ascii_case(fqn) {
            return short.to_string();
        }
    }
    format!("\\{fqn}")
}

/// Locate where a fix's docblock goes for the declaration whose earliest token
/// is `first_span` (the first attribute's name span when attributes exist, else
/// the declaration's name/type span). Returns the anchor plus the declaration
/// line's verbatim indentation, or `None` when the declaration doesn't start its
/// own line (one-liners, embedded code) or an existing docblock can't be located
/// byte-exactly.
pub(crate) fn doc_anchor(
    source: &str,
    first_span: Span,
    doc: Option<&str>,
) -> Option<(FixAnchor, String)> {
    let start = first_span.start as usize;
    if start > source.len() {
        return None;
    }
    let line_start = source[..start].rfind('\n').map_or(0, |i| i + 1);
    let line_prefix = &source[line_start..start];
    let indent_len = line_prefix.len() - line_prefix.trim_start_matches([' ', '\t']).len();
    let indent = &line_prefix[..indent_len];
    // Between the indent and the anchor token only declaration-prefix material
    // may appear: modifiers/keywords and type hints (`public static function`,
    // `public ?array`, DNF parens), or the attribute opener when `first_span` is
    // an attribute *name* (`#[Attr]`). Anything else (`;`, `{`, `=`, `$`,
    // quotes, comment openers, …) means the declaration doesn't start this line
    // — skip rather than splice a docblock mid-statement.
    let rest = line_prefix[indent_len..].trim_end();
    let decl_prefix = rest.chars().all(|c| {
        c.is_ascii_alphanumeric()
            || matches!(c, '_' | '\\' | '|' | '&' | '?' | '(' | ')' | ' ' | '\t')
    });
    if !(decl_prefix || rest == "#[") {
        return None;
    }
    match doc {
        None => Some((FixAnchor::NewDocAt(line_start as u32), indent.to_string())),
        Some(text) => {
            let pos = source[..line_start].rfind(text)?;
            // The attached docblock sits directly above the declaration (or its
            // attributes): only whitespace or attribute lines in between.
            let between = &source[pos + text.len()..line_start];
            if !between
                .chars()
                .all(|c| c.is_whitespace() || matches!(c, '#' | '[' | ']'))
                || between.contains("/*")
            {
                return None;
            }
            Some((
                FixAnchor::ExistingDoc(Span::new(pos as u32, (pos + text.len()) as u32)),
                indent.to_string(),
            ))
        }
    }
}

/// The span of the declaration's earliest token when it carries attributes:
/// the first attribute's *name* (`AttributeGroup` has no span of its own; the
/// `#[` opener sits on the same line, which is all the anchor needs).
pub(crate) fn first_attr_span(attrs: &[php_ast::AttributeGroup]) -> Option<Span> {
    attrs.first()?.attrs.first().map(|a| a.name.span)
}

/// Gate + render + anchor in one call: `None` unless `ty` is useful evidence
/// ([`php_infer::useful_inference`]), renders as valid PHPDoc, and the
/// declaration anchors cleanly. `var` is the parameter name for `@param`.
pub(crate) fn typed_tag_fix(
    fa: &FileAnalysis,
    scope: &Scope,
    ty: &Type,
    first_span: Span,
    doc: Option<&str>,
    kind: DocTagKind,
    var: Option<&str>,
) -> Option<DocTagFix> {
    typed_tag_fix_mode(fa, scope, ty, first_span, doc, kind, var, false)
}

/// [`typed_tag_fix`] for the `missingType.iterableValue` sites: additionally
/// accepts `mixed` *inside* an evidenced container (`array<string, mixed>` —
/// the structure is known, the values honestly aren't), never as the whole
/// type. Union slots that retained `mixed` are absorbed to plain `mixed`
/// first (`int|mixed` claims less than it looks like it does).
#[allow(clippy::too_many_arguments)]
pub(crate) fn typed_tag_fix_ack(
    fa: &FileAnalysis,
    scope: &Scope,
    ty: &Type,
    first_span: Span,
    doc: Option<&str>,
    kind: DocTagKind,
    var: Option<&str>,
) -> Option<DocTagFix> {
    let absorbed = ty.clone().map(&mut |t| match &t {
        Type::Union(parts)
            if parts
                .iter()
                .any(|p| matches!(p, Type::Mixed | Type::ExplicitMixed)) =>
        {
            Type::Mixed
        }
        Type::Nullable(x) if matches!(**x, Type::Mixed | Type::ExplicitMixed) => Type::Mixed,
        _ => t,
    });
    // An all-mixed container as the whole type (`array<mixed, mixed>`,
    // `array<int|string, mixed>`) documents nothing the bare word didn't —
    // that's suppression, not a fix. (Inside a shape it stays: the shape keys
    // are the information, and a bare inner `array` couldn't be written.)
    if zero_info_container(&absorbed) {
        return None;
    }
    typed_tag_fix_mode(fa, scope, &absorbed, first_span, doc, kind, var, true)
}

/// A type that is nothing but empty-shape (and `null`) arms — the
/// "exactly-empty array" claim [`typed_tag_fix_mode`] refuses to write.
fn sole_empty_shape(ty: &Type) -> bool {
    match ty {
        Type::Shape { fields, .. } => fields.is_empty(),
        Type::Nullable(x) => sole_empty_shape(x),
        Type::Union(parts) => {
            !parts.is_empty()
                && parts
                    .iter()
                    .all(|p| matches!(p, Type::Null) || sole_empty_shape(p))
        }
        _ => false,
    }
}

/// A container type whose key carries no information (`mixed` or the full
/// `array-key` = `int|string`) and whose value is `mixed`, through nullability.
fn zero_info_container(ty: &Type) -> bool {
    fn mixedish_key(k: &Type) -> bool {
        match k {
            Type::Mixed | Type::ExplicitMixed => true,
            Type::Union(parts) => {
                parts.len() == 2
                    && parts.iter().any(|p| matches!(p, Type::Int))
                    && parts.iter().any(|p| matches!(p, Type::String))
            }
            _ => false,
        }
    }
    match ty {
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            mixedish_key(&kv.0) && matches!(kv.1, Type::Mixed | Type::ExplicitMixed)
        }
        Type::Nullable(inner) => zero_info_container(inner),
        _ => false,
    }
}

#[allow(clippy::too_many_arguments)]
fn typed_tag_fix_mode(
    fa: &FileAnalysis,
    scope: &Scope,
    ty: &Type,
    first_span: Span,
    doc: Option<&str>,
    kind: DocTagKind,
    var: Option<&str>,
    container_mixed: bool,
) -> Option<DocTagFix> {
    if !php_infer::useful_inference(ty) {
        return None;
    }
    // Don't write observed literals into signatures (`@return 1` from
    // `return 1;`): widen to the base scalar, as parameter inference does.
    // The widening rewrites union members in place, so rebuild every union
    // through the deduping smart constructor (`'a'|'b'` → `string|string` →
    // `string`).
    let widened = php_infer::widen_literals(ty.clone()).map(&mut |t| match t {
        Type::Union(parts) => Type::union(parts.to_vec()),
        other => other,
    });
    // Never write a type the missing-typehint rules would themselves report
    // (bare `array`, generic class without type args, bare `callable`): that
    // would only convert the finding into another one.
    if !crate::missing_type::check_type(fa.reflection, &widened).is_empty() {
        return None;
    }
    // Never write an exactly-empty array as the whole type: `array{}` evidence
    // almost always means the population path wasn't observed (e.g. a loop
    // assignment behind a `break`), and the written seal fences callers off
    // every key — minting offset findings instead of fixing one.
    if sole_empty_shape(&widened) {
        return None;
    }
    let rendered = render_phpdoc_mode(&widened, scope, container_mixed)?;
    let tag = match (kind, var) {
        (DocTagKind::Param, Some(v)) => format!("@param {rendered} ${v}"),
        (DocTagKind::Return, None) => format!("@return {rendered}"),
        (DocTagKind::Var, None) => format!("@var {rendered}"),
        _ => return None,
    };
    doc_tag_fix(fa, first_span, doc, kind, tag)
}

/// Anchor + render + assemble: the one-call path rules use. `tag_body` is the
/// full tag line (e.g. `@param string $name`).
pub(crate) fn doc_tag_fix(
    fa: &FileAnalysis,
    first_span: Span,
    doc: Option<&str>,
    kind: DocTagKind,
    tag_body: String,
) -> Option<DocTagFix> {
    let (anchor, indent) = doc_anchor(fa.source, first_span, doc)?;
    Some(DocTagFix {
        anchor,
        kind,
        tag: tag_body,
        indent,
    })
}

// ---------------------------------------------------------------------------
// Return-type evidence (for the return branch of `missingType.iterableValue`)
// ---------------------------------------------------------------------------

/// Evidence for a `@return` refining a declared bare `array`/`iterable` return:
/// the union of the body's own-scope `return <expr>` types. `None` for
/// generators, bodies with a bare `return;` or no value returns, or when the
/// union doesn't actually refine (still contains a bare iterable).
pub(crate) fn iterable_return_evidence(fa: &FileAnalysis, body: &[php_ast::Stmt]) -> Option<Type> {
    let mut has_yield = false;
    for s in body {
        crate::walk::for_each_expr_in_scope(s, &mut |e| {
            if matches!(
                e.kind,
                php_ast::ExprKind::Yield { .. } | php_ast::ExprKind::YieldFrom(_)
            ) {
                has_yield = true;
            }
        });
    }
    if has_yield {
        return None;
    }
    let mut types = Vec::new();
    let mut bare_return = false;
    crate::decls::collect_returns_in_body(body, &mut |e| match e {
        Some(expr) => types.push(fa.type_of(expr)),
        None => bare_return = true,
    });
    if bare_return || types.is_empty() {
        return None;
    }
    let union = Type::union(types);
    // Must refine: a member that is itself a bare iterable would re-report.
    if crate::missing_type::type_iterable_word(&union).is_some() {
        return None;
    }
    Some(union)
}

/// Whether a body provably returns no value: no `return <expr>` anywhere in
/// its own scope (bare `return;` is fine) and no `yield` (a generator's return
/// type is `Generator`, not `void`). Evidence for a `@return void` fix on the
/// `missingType.return` finding — `void` is unrenderable by [`render_phpdoc`]
/// on purpose (never *inferred* into value positions), so the fix site builds
/// the tag directly.
pub(crate) fn void_return_evidence(body: &[php_ast::Stmt]) -> bool {
    let mut has_yield = false;
    for s in body {
        crate::walk::for_each_expr_in_scope(s, &mut |e| {
            if matches!(
                e.kind,
                php_ast::ExprKind::Yield { .. } | php_ast::ExprKind::YieldFrom(_)
            ) {
                has_yield = true;
            }
        });
    }
    if has_yield {
        return false;
    }
    let mut has_value_return = false;
    crate::decls::collect_returns_in_body(body, &mut |e| {
        if e.is_some() {
            has_value_return = true;
        }
    });
    !has_value_return
}

// ---------------------------------------------------------------------------
// Wrong doc-narrowing rewrite (for `return.type` fixes)
// ---------------------------------------------------------------------------

/// A `Replace` fix correcting a PHPDoc `@return` whose type *narrows* the
/// native return hint in a way the body provably violates (the generated
/// `@return true` on `authorize(): bool` pattern). Only fires when the doc is
/// redundant-or-wrong relative to a real native contract — never when the doc
/// is the only contract (rewriting that could codify a body bug):
///
/// - a native return hint exists (not `mixed`/`void`/`never`),
/// - the doc-refined type differs from it and is assignable *to* it,
/// - the body's return-expression union is confidently typed, fits the
///   native type, but not the doc type,
/// - the docblock has exactly one `@return` and anchors byte-exactly.
///
/// When the body union equals the native type the tag adds nothing: its line
/// is deleted (multi-line docblocks only). Otherwise the written type text is
/// replaced with the rendered body union.
#[allow(clippy::too_many_arguments)]
pub(crate) fn return_narrowing_fix(
    index: &php_reflect::ReflectionIndex,
    types: &php_infer::TypeMap,
    source: &str,
    scope: &Scope,
    declared: &Type,
    native: &Type,
    doc: Option<&str>,
    first_span: Span,
    body: &[php_ast::Stmt],
) -> Option<php_diagnostics::ReplaceFix> {
    use php_diagnostics::ReplaceFix;
    if matches!(
        native,
        Type::Mixed | Type::ExplicitMixed | Type::Void | Type::Never
    ) || declared == native
        || !crate::is_assignable(index, declared, native)
    {
        return None;
    }
    // Confident body union: every `return <expr>` typed (no bare returns, no
    // yields, nothing mixed/unknown), read from the flow-narrowed type map.
    let mut has_yield = false;
    for s in body {
        crate::walk::for_each_expr_in_scope(s, &mut |e| {
            if matches!(
                e.kind,
                php_ast::ExprKind::Yield { .. } | php_ast::ExprKind::YieldFrom(_)
            ) {
                has_yield = true;
            }
        });
    }
    if has_yield {
        return None;
    }
    let mut parts = Vec::new();
    let mut bare = false;
    crate::decls::collect_returns_in_body(body, &mut |e| match e {
        Some(expr) => {
            parts.push(
                types
                    .get(&php_span::NodeKey::of(expr.span))
                    .map(|f| f.merged.clone())
                    .unwrap_or(Type::Mixed),
            );
        }
        None => bare = true,
    });
    if bare || parts.is_empty() {
        return None;
    }
    let union = php_infer::widen_literals(Type::union(parts)).map(&mut |t| match t {
        Type::Union(parts) => Type::union(parts.to_vec()),
        other => other,
    });
    if !php_infer::useful_inference(&union)
        || !crate::is_assignable(index, &union, native)
        || crate::is_assignable(index, &union, declared)
    {
        return None;
    }
    // Locate the docblock byte-exactly, then the single `@return` inside it.
    let doc_text = doc?;
    let (FixAnchor::ExistingDoc(doc_span), _) = doc_anchor(source, first_span, Some(doc_text))?
    else {
        return None;
    };
    if doc_text.matches("@return").count() != 1 {
        return None;
    }
    let tag_off = doc_text.find("@return")?;
    let after_tag = &doc_text[tag_off + "@return".len()..];
    let ws = after_tag.len() - after_tag.trim_start_matches([' ', '\t']).len();
    if ws == 0 {
        return None; // `@returns`/glued text — not the tag we think it is.
    }
    let operand = &after_tag[ws..];
    let (_, consumed) = php_phpdoc::parse_type_prefix(operand)?;
    if consumed == 0 {
        return None;
    }
    let type_start = doc_span.start as usize + tag_off + "@return".len() + ws;
    let rest_of_line = operand[consumed..].split(['\n', '\r']).next().unwrap_or("");
    let only_type_on_line = rest_of_line.trim_start_matches([' ', '\t']).is_empty()
        || rest_of_line
            .trim_start_matches([' ', '\t'])
            .starts_with("*/");
    let multi_line = doc_text.contains('\n');
    if union == *native && multi_line && only_type_on_line && !rest_of_line.contains("*/") {
        // The tag would just restate the native hint: delete its whole line,
        // provided the line holds nothing but framing and the tag.
        let mut line_start = doc_text[..tag_off].rfind('\n').map(|i| i + 1)?;
        if !doc_text[line_start..tag_off]
            .chars()
            .all(|c| matches!(c, ' ' | '\t' | '*'))
        {
            return None;
        }
        let line_end = doc_text[tag_off..]
            .find('\n')
            .map(|i| tag_off + i + 1)
            .unwrap_or(doc_text.len());
        // When the tag was the last content — next line closes the block —
        // absorb a now-dangling blank ` * ` separator line above it.
        if doc_text[line_end..]
            .trim_start_matches([' ', '\t'])
            .starts_with("*/")
        {
            if let Some(prev_nl) = doc_text[..line_start.saturating_sub(1)].rfind('\n') {
                let prev_line = &doc_text[prev_nl + 1..line_start - 1];
                // '\r' too: in a CRLF file the previous line carries it.
                let bare_star = prev_line.trim_matches([' ', '\t', '\r']) == "*";
                if bare_star {
                    line_start = prev_nl + 1;
                }
            }
        }
        return Some(ReplaceFix {
            span: Span::new(
                (doc_span.start as usize + line_start) as u32,
                (doc_span.start as usize + line_end) as u32,
            ),
            replacement: String::new(),
        });
    }
    // Rewrite the written type text to the body union.
    let rendered = render_phpdoc(&union, scope)?;
    if !crate::missing_type::check_type(index, &union).is_empty() || sole_empty_shape(&union) {
        return None;
    }
    Some(ReplaceFix {
        span: Span::new(type_start as u32, (type_start + consumed) as u32),
        replacement: rendered,
    })
}

// ---------------------------------------------------------------------------
// Inline `@var` generic completion (for `missingType.generics` fixes)
// ---------------------------------------------------------------------------

/// A `Replace` fix completing the type args of an inline `@var` naming a bare
/// generic class (`/** @var Builder $q */ $q = Screen::query();` →
/// `@var Builder<Screen> $q`), when the statement is a simple `$var = <expr>`
/// assignment whose RHS infers to a concrete instantiation of that same class.
/// The rewrite preserves the rest of the tag (`$var` name, prose).
pub(crate) fn var_generic_completion_fix(
    fa: &FileAnalysis,
    scope: &Scope,
    st: &php_ast::Stmt,
    doc_raw: &str,
) -> Option<php_diagnostics::ReplaceFix> {
    use php_ast::{ExprKind, StmtKind};
    let parsed = php_phpdoc::parse(doc_raw);
    let var = parsed.vars.first()?;
    if parsed.vars.len() != 1 {
        return None;
    }
    let php_phpdoc::DocType::Named(written) = var.ty.as_ref()? else {
        return None;
    };
    // Evidence: the annotated statement's own assignment RHS, else the flow
    // type of the named variable's first occurrence in it (`@var` frequently
    // floats above a *use* of the variable, not its assignment).
    let rhs_ty = match &st.kind {
        StmtKind::Expr(e)
            if matches!(&e.kind, ExprKind::Assign { target, .. }
                if matches!(&target.kind, ExprKind::Variable(sym)
                    if var.name.as_deref().is_none_or(|n| n == fa.interner.resolve(*sym)))) =>
        {
            let ExprKind::Assign { rhs, .. } = &e.kind else {
                return None;
            };
            fa.type_of(rhs)
        }
        _ => {
            let name = var.name.as_deref()?;
            let mut found: Option<Type> = None;
            crate::walk::for_each_expr_in_stmt(st, &mut |e| {
                if found.is_none()
                    && matches!(&e.kind, ExprKind::Variable(sym)
                        if fa.interner.resolve(*sym) == name)
                {
                    found = Some(fa.type_of(e));
                }
            });
            found?
        }
    };
    let Type::Named { fqn, args } = &rhs_ty else {
        return None;
    };
    if args.is_empty() || !crate::missing_type::check_type(fa.reflection, &rhs_ty).is_empty() {
        return None;
    }
    let written_fqn = match scope.resolve_class(&crate::missing_type::name_from_doc(written)) {
        php_resolve::Resolution::Fqn(f) => f,
        php_resolve::Resolution::Fallback { namespaced, .. } => namespaced,
        _ => return None,
    };
    if !written_fqn
        .trim_start_matches('\\')
        .eq_ignore_ascii_case(fqn.trim_start_matches('\\'))
    {
        return None;
    }
    let rendered = render_phpdoc(&rhs_ty, scope)?;
    // Locate the doc directly above the statement, then the single `@var`.
    let st_start = st.span.start as usize;
    let doc_start = fa.source.get(..st_start)?.rfind(doc_raw)?;
    if !fa.source[doc_start + doc_raw.len()..st_start]
        .chars()
        .all(char::is_whitespace)
    {
        return None;
    }
    if doc_raw.matches("@var").count() != 1 {
        return None;
    }
    let tag_off = doc_raw.find("@var")?;
    let after = &doc_raw[tag_off + "@var".len()..];
    let ws = after.len() - after.trim_start_matches([' ', '\t']).len();
    if ws == 0 {
        return None;
    }
    let (_, consumed) = php_phpdoc::parse_type_prefix(&after[ws..])?;
    if consumed == 0 {
        return None;
    }
    let type_start = doc_start + tag_off + "@var".len() + ws;
    Some(php_diagnostics::ReplaceFix {
        span: Span::new(type_start as u32, (type_start + consumed) as u32),
        replacement: rendered,
    })
}

// ---------------------------------------------------------------------------
// Unused closure capture removal (for `closure.unusedUse` fixes)
// ---------------------------------------------------------------------------

/// A `Replace` fix deleting an unused `use ($x)` capture. When *every* capture
/// is unused the whole clause goes (each finding carries the identical edit —
/// the applier dedups); otherwise just the item and its comma. The AST carries
/// no per-use spans, so the clause is located by scanning the closure's source
/// slice — and only trusted when exactly one candidate `use (…)` reproduces
/// the AST's capture list verbatim (names, by-ref flags, order).
pub(crate) fn closure_use_removal_fix(
    fa: &FileAnalysis,
    closure_span: Span,
    c: &php_ast::ClosureExpr,
    target: php_intern::Symbol,
    unused: &[php_intern::Symbol],
) -> Option<php_diagnostics::ReplaceFix> {
    use php_diagnostics::ReplaceFix;
    let text = fa.source.get(closure_span.range())?;
    let expected: Vec<(String, bool)> = c
        .uses
        .iter()
        .map(|u| (fa.interner.resolve(u.name).to_string(), u.by_ref))
        .collect();
    // Find the unique `use (…)` whose items match the AST captures:
    // `(keyword offset, `)` offset, trimmed item byte ranges)`.
    type UseClause = (usize, usize, Vec<(usize, usize)>);
    let mut found: Option<UseClause> = None;
    let mut search = 0;
    while let Some(rel) = text[search..].find("use") {
        let at = search + rel;
        search = at + 3;
        // Keyword boundary on both sides.
        if at > 0 && text.as_bytes()[at - 1].is_ascii_alphanumeric() {
            continue;
        }
        let after = &text[at + 3..];
        let ws = after.len() - after.trim_start().len();
        if !after[ws..].starts_with('(') {
            continue;
        }
        let open = at + 3 + ws;
        let Some(close_rel) = text[open + 1..].find(')') else {
            continue;
        };
        let close = open + 1 + close_rel;
        let inner = &text[open + 1..close];
        // Split on commas; a use list has no nested delimiters.
        let mut items: Vec<(usize, usize)> = Vec::new(); // trimmed byte ranges
        let mut ok = true;
        let mut pos = 0;
        for (i, raw) in inner.split(',').enumerate() {
            let lead = raw.len() - raw.trim_start().len();
            let item_start = open + 1 + pos + lead;
            let item_end = item_start + raw.trim().len();
            let trimmed = raw.trim();
            let (by_ref, rest) = match trimmed.strip_prefix('&') {
                Some(r) => (true, r.trim_start()),
                None => (false, trimmed),
            };
            match (rest.strip_prefix('$'), expected.get(i)) {
                (Some(name), Some((want, want_ref))) if name == want && by_ref == *want_ref => {}
                _ => {
                    ok = false;
                    break;
                }
            }
            items.push((item_start, item_end));
            pos += raw.len() + 1;
        }
        if ok && items.len() == expected.len() {
            if found.is_some() {
                return None; // ambiguous (e.g. a string constant lookalike).
            }
            found = Some((at, close, items));
        }
    }
    let (kw_at, close, items) = found?;
    let base = closure_span.start as usize;
    if unused.len() == c.uses.len() {
        // Whole clause: from the end of the previous token through `)`.
        let lead_ws = text[..kw_at].len() - text[..kw_at].trim_end().len();
        return Some(ReplaceFix {
            span: Span::new((base + kw_at - lead_ws) as u32, (base + close + 1) as u32),
            replacement: String::new(),
        });
    }
    let idx = c.uses.iter().position(|u| u.name == target)?;
    let (start, end) = items[idx];
    let span = if idx + 1 < items.len() {
        // Item plus its trailing comma and spacing.
        Span::new((base + start) as u32, (base + items[idx + 1].0) as u32)
    } else {
        // Last item: absorb the preceding comma.
        Span::new((base + items[idx - 1].1) as u32, (base + end) as u32)
    };
    Some(ReplaceFix {
        span,
        replacement: String::new(),
    })
}

// ---------------------------------------------------------------------------
// Property type evidence (for `missingType.property` fixes)
// ---------------------------------------------------------------------------

/// Infer a `@var` type for an untyped property from its default value and the
/// `$this->prop = …` assignments in the class's own method bodies.
///
/// Sound only when every write is visible, so this is deliberately restricted:
/// **private, non-static** properties (public/protected can be written from
/// other files), and any write shape we can't type — compound assigns,
/// index/list writes, by-ref aliasing, dynamic member names, possibly-by-ref
/// call arguments, foreach targets — bails the whole property. Incomplete
/// evidence must never become a wrong `@var`; the finding then simply reports
/// without a fix.
pub(crate) fn infer_property_type(
    fa: &FileAnalysis,
    scope: &Scope,
    class_fqn: &str,
    c: &php_ast::ClassDecl,
    pd: &php_ast::PropertyDecl,
    elem: &php_ast::PropElem,
) -> Option<Type> {
    use php_ast::{ClassKind, Visibility};
    if pd.modifiers.is_static || c.kind != ClassKind::Class {
        return None;
    }
    match pd.modifiers.visibility {
        Some(Visibility::Private) => {}
        // Protected is sound only when nothing can subclass-write it: no class
        // in the project (analyzed or scanned) extends this one.
        Some(Visibility::Protected) => {
            let extended = fa.project.classes().any(|e| {
                e.extends.iter().any(|p| {
                    p.trim_start_matches('\\')
                        .eq_ignore_ascii_case(class_fqn.trim_start_matches('\\'))
                })
            });
            if extended {
                return None;
            }
        }
        _ => return None,
    }
    // Ancestor classes and used traits can write `$this->prop` too (trait
    // methods are flattened into the class; parent methods share `$this`).
    // Their bodies aren't typed here, so any write-shaped use bails.
    if ancestors_write_property(fa, class_fqn, elem.name) {
        return None;
    }
    own_write_evidence(fa, scope, class_fqn, c, elem)?.into_type()
}

/// The class's own writes to `$this->{elem}` (default value + method-body
/// assignments) as typed [`Evidence`]; `None` when any write shape can't be
/// typed (the shared bail semantics of [`infer_property_type`]).
fn own_write_evidence(
    fa: &FileAnalysis,
    scope: &Scope,
    class_fqn: &str,
    c: &php_ast::ClassDecl,
    elem: &php_ast::PropElem,
) -> Option<Evidence> {
    let mut evidence = Evidence::default();
    if let Some(default) = &elem.default {
        let ctx = php_infer::TypeCtx::new(fa.reflection, scope, fa.interner);
        evidence.push(default, ctx.infer(default));
    }
    let mut bail = false;
    for m in &c.members {
        let php_ast::Member::Method(md) = m else {
            continue;
        };
        let Some(body) = &md.body else { continue };
        for st in body {
            crate::walk::for_each_stmt_in_stmt(st, &mut |s| {
                // A foreach key/value target is a write we don't type.
                if let php_ast::StmtKind::Foreach { key, value, .. } = &s.kind {
                    if contains_prop(value, elem.name, fa)
                        || key
                            .as_ref()
                            .is_some_and(|k| contains_prop(k, elem.name, fa))
                    {
                        bail = true;
                    }
                }
            });
            crate::walk::for_each_expr_in_stmt(st, &mut |e| {
                collect_prop_write(fa, class_fqn, elem.name, e, &mut evidence, &mut bail);
            });
        }
    }
    (!bail).then_some(evidence)
}

/// Fallback `@var` evidence for an untyped property that overrides an ancestor
/// declaration (the Eloquent `protected $fillable = […]` pattern): restate the
/// nearest ancestor's declared type. Sound because the non-private override
/// shares the ancestor's storage contract — but the annotation must not mint
/// new findings, so the child's own writes (and any subclass's write-shaped
/// uses) must be verifiably compatible with the ancestor type.
pub(crate) fn inherited_property_type(
    fa: &FileAnalysis,
    scope: &Scope,
    class_fqn: &str,
    c: &php_ast::ClassDecl,
    pd: &php_ast::PropertyDecl,
    elem: &php_ast::PropElem,
) -> Option<Type> {
    use php_ast::{ClassKind, Visibility};
    if c.kind != ClassKind::Class {
        return None;
    }
    let cr = fa.reflection.class(class_fqn)?;
    let prop = fa.interner.resolve(elem.name);
    // Nearest ancestor declaration: the class's own traits (flattened into it),
    // then parents; `find_property` continues each walk transitively.
    let found = cr.traits.iter().chain(&cr.parents).find_map(|t| match t {
        Type::Named { fqn, .. } => fa.reflection.find_property(fqn, prop),
        _ => None,
    })?;
    let member = &*found.member;
    // A private ancestor property is a separate per-class slot, and a magic
    // `@property` tag is not a declaration. Static properties are excluded
    // outright: their writes go through `self::$p`, which the write-evidence
    // collector below doesn't model, so conformance couldn't be verified.
    if member.magic
        || member.visibility == Visibility::Private
        || member.is_static
        || pd.modifiers.is_static
    {
        return None;
    }
    let ty = member.ty.clone();
    // The child's own writes must conform, else the `@var` trades this finding
    // for an assignment one. Unanalyzable write shapes bail as usual.
    if let Some(written) = own_write_evidence(fa, scope, class_fqn, c, elem)?.into_type() {
        if !crate::is_assignable(fa.reflection, &written, &ty) {
            return None;
        }
    }
    // Subclasses write through the same slot; any write-shaped use of the
    // property in a subclass body would now be checked against the new `@var`.
    let base = class_fqn.trim_start_matches('\\');
    for e in fa.project.classes() {
        if e.fqn.trim_start_matches('\\').eq_ignore_ascii_case(base)
            || !fa.reflection.is_subclass_of(&e.fqn, class_fqn)
        {
            continue;
        }
        let sub = fa.reflection.class(&e.fqn)?;
        for m in &sub.methods {
            if m.magic {
                continue;
            }
            if let Some((body, body_scope)) = fa.reflection.method_body(&sub.fqn, &m.name) {
                if body
                    .iter()
                    .any(|st| stmt_writes_prop(fa, body_scope, &sub.fqn, st, elem.name))
                {
                    return None;
                }
            }
        }
    }
    Some(ty)
}

/// Whether any ancestor class or used trait (transitively) has a method body
/// with a write-shaped use of `$this->{name}`. Unknown non-builtin ancestors
/// count as writes (can't verify). Bodies share the run-wide interner, so the
/// `Symbol` compares across files.
fn ancestors_write_property(fa: &FileAnalysis, class_fqn: &str, name: php_intern::Symbol) -> bool {
    let Some(start) = fa.reflection.class(class_fqn) else {
        return true;
    };
    let prop_str = fa.interner.resolve(name);
    let mut stack: Vec<String> = ancestor_fqns(start);
    let mut seen = std::collections::HashSet::new();
    while let Some(fqn) = stack.pop() {
        if !seen.insert(fqn.to_ascii_lowercase()) {
            continue;
        }
        let Some(cr) = fa.reflection.class(&fqn) else {
            return true; // unknown ancestor: writes can't be ruled out.
        };
        if cr.builtin {
            continue; // engine classes don't write userland declared props.
        }
        // An ancestor that declares its own *private* property of this name
        // has a separate per-class slot — its `$this->{name}` accesses can
        // never touch the child's property.
        let shadowed_private = cr
            .properties
            .iter()
            .any(|p| p.name == prop_str && p.visibility == php_ast::Visibility::Private);
        if !shadowed_private {
            for m in &cr.methods {
                if m.magic {
                    continue;
                }
                if let Some((body, body_scope)) = fa.reflection.method_body(&cr.fqn, &m.name) {
                    if body
                        .iter()
                        .any(|st| stmt_writes_prop(fa, body_scope, &cr.fqn, st, name))
                    {
                        return true;
                    }
                }
            }
        }
        stack.extend(ancestor_fqns(cr));
    }
    false
}

/// Parent + trait FQNs of a reflected class (interfaces carry no bodies).
fn ancestor_fqns(cr: &php_reflect::ClassReflection) -> Vec<String> {
    cr.parents
        .iter()
        .chain(&cr.traits)
        .filter_map(|t| match t {
            Type::Named { fqn, .. } => Some(fqn.to_string()),
            _ => None,
        })
        .collect()
}

/// Write detector for foreign (ancestor/trait) bodies: any assignment (plain,
/// compound, by-ref), index write, foreach target, dynamic `$this->{…}` write,
/// or possibly-by-ref call argument touching a property fetch of `name` counts
/// as a write. Calls resolve through the body's own `scope` so passing the
/// property *by value* (`Parser::parse($this->signature)`) doesn't bail.
fn stmt_writes_prop(
    fa: &FileAnalysis,
    scope: &Scope,
    class_fqn: &str,
    st: &php_ast::Stmt,
    name: php_intern::Symbol,
) -> bool {
    use php_ast::{ExprKind, MemberName};
    let mut found = false;
    crate::walk::for_each_stmt_in_stmt(st, &mut |s| {
        if let php_ast::StmtKind::Foreach { key, value, .. } = &s.kind {
            if contains_prop(value, name, fa)
                || key.as_ref().is_some_and(|k| contains_prop(k, name, fa))
            {
                found = true;
            }
        }
    });
    crate::walk::for_each_expr_in_stmt(st, &mut |e| match &e.kind {
        ExprKind::Assign { target, .. } | ExprKind::AssignOp { target, .. } => {
            if contains_prop(target, name, fa) {
                found = true;
            }
        }
        ExprKind::AssignRef { target, rhs } => {
            if contains_prop(target, name, fa) || contains_prop(rhs, name, fa) {
                found = true;
            }
        }
        ExprKind::Call { callee, args } => {
            for (idx, arg) in args.iter().enumerate() {
                if !arg.spread && is_this_prop(&arg.value, name, fa) {
                    let params = match &callee.kind {
                        ExprKind::Name(n) => resolve_function_params(fa, scope, n),
                        _ => None,
                    };
                    if resolved_param_by_ref_or_unknown(fa, params, idx) {
                        found = true;
                    }
                }
            }
        }
        ExprKind::StaticCall {
            class,
            method: MemberName::Ident(m),
            args,
        } => {
            for (idx, arg) in args.iter().enumerate() {
                if !arg.spread && is_this_prop(&arg.value, name, fa) {
                    let known_safe = static_class_fqn(scope, class, class_fqn).is_some_and(|fqn| {
                        method_param_not_by_ref(fa, &fqn, fa.interner.resolve(*m), idx)
                    });
                    if !known_safe {
                        found = true;
                    }
                }
            }
        }
        ExprKind::MethodCall {
            recv, method, args, ..
        } => {
            for (idx, arg) in args.iter().enumerate() {
                if !arg.spread && is_this_prop(&arg.value, name, fa) {
                    let known_safe = is_this(recv, fa)
                        && matches!(method, MemberName::Ident(m)
                            if method_param_not_by_ref(fa, class_fqn, fa.interner.resolve(*m), idx));
                    if !known_safe {
                        found = true;
                    }
                }
            }
        }
        // Dynamic-method static calls and constructors: unresolvable, so any
        // bare property argument may be by-ref.
        ExprKind::StaticCall { args, .. } | ExprKind::New { args, .. }
            if args
                .iter()
                .any(|a| !a.spread && is_this_prop(&a.value, name, fa)) =>
        {
            found = true;
        }
        _ => {}
    });
    found
}

/// Resolve a static-call class operand (`Parser::`, `self::`, `static::`) to an
/// FQN; `self`/`static` bind to the enclosing class (no subclasses exist when
/// this runs).
fn static_class_fqn(scope: &Scope, class: &Expr, self_fqn: &str) -> Option<String> {
    let php_ast::ExprKind::Name(n) = &class.kind else {
        return None;
    };
    match scope.resolve_class(n) {
        Resolution::Fqn(fqn) => Some(fqn),
        Resolution::LateStatic(_) => Some(self_fqn.to_string()),
        _ => None,
    }
}

/// The reflected params of a free function named at a call, resolved through
/// the given scope (with PHP's global fallback).
fn resolve_function_params<'a>(
    fa: &'a FileAnalysis,
    scope: &Scope,
    n: &php_ast::Name,
) -> Option<&'a [php_reflect::ParamReflection]> {
    let lookup = |fqn: &str| fa.reflection.function(fqn).map(|f| f.params.as_slice());
    match scope.resolve_function(n) {
        Resolution::Fqn(fqn) => lookup(&fqn),
        Resolution::Fallback { namespaced, global } => {
            lookup(&namespaced).or_else(|| lookup(&global))
        }
        _ => None,
    }
}

/// Property-type evidence with empty-array literals (`[]`) tracked separately:
/// `[]` is a subtype of every iterable, so when refined iterable evidence exists
/// the empty literal is subsumed instead of widening the union to bare `array`
/// (`private $rows = []; … $this->rows = ['a'];` → `array<int, string>`, not
/// `array|array<int, string>`).
#[derive(Default)]
struct Evidence {
    types: Vec<Type>,
    empty_array_literals: usize,
}

impl Evidence {
    fn push(&mut self, source: &Expr, ty: Type) {
        if matches!(&source.kind, php_ast::ExprKind::Array { items, .. } if items.is_empty()) {
            self.empty_array_literals += 1;
        } else {
            self.types.push(ty);
        }
    }

    fn into_type(self) -> Option<Type> {
        let mut types = self.types;
        if self.empty_array_literals > 0 {
            // Subsumed only when every other member already accepts `[]`.
            let all_iterable = !types.is_empty()
                && types.iter().all(|t| {
                    matches!(
                        t,
                        Type::Array(_) | Type::List(_) | Type::Iterable(_) | Type::Shape { .. }
                    )
                });
            if !all_iterable {
                types.push(Type::Array(None));
            }
        }
        (!types.is_empty()).then(|| Type::union(types))
    }
}

fn is_this(e: &Expr, fa: &FileAnalysis) -> bool {
    matches!(&e.kind, php_ast::ExprKind::Variable(s) if fa.interner.resolve(*s) == "this")
}

/// `$this->name` (non-nullsafe, literal member).
fn is_this_prop(e: &Expr, name: php_intern::Symbol, fa: &FileAnalysis) -> bool {
    matches!(
        &e.kind,
        php_ast::ExprKind::Prop { base, nullsafe: false, name: php_ast::MemberName::Ident(s) }
            if *s == name && is_this(base, fa)
    )
}

/// Whether `e` contains a fetch of property `name` (any receiver) or a dynamic
/// `$this->{$x}` member (which could name any property). Used on write-target
/// positions, where either means an untypeable write.
fn contains_prop(e: &Expr, name: php_intern::Symbol, fa: &FileAnalysis) -> bool {
    let mut found = false;
    crate::walk::for_each_subexpr(e, &mut |sub| match &sub.kind {
        php_ast::ExprKind::Prop {
            name: php_ast::MemberName::Ident(s),
            ..
        } if *s == name => found = true,
        php_ast::ExprKind::Prop {
            base,
            name: php_ast::MemberName::Var(_) | php_ast::MemberName::Expr(_),
            ..
        } if is_this(base, fa) => found = true,
        _ => {}
    });
    found
}

/// Inspect one expression for writes (or unanalyzable uses) of `$this->{name}`.
fn collect_prop_write(
    fa: &FileAnalysis,
    class_fqn: &str,
    name: php_intern::Symbol,
    e: &Expr,
    evidence: &mut Evidence,
    bail: &mut bool,
) {
    use php_ast::{ExprKind, MemberName};
    match &e.kind {
        ExprKind::Assign { target, rhs } => {
            if is_this_prop(target, name, fa) {
                evidence.push(rhs, fa.type_of(rhs.as_ref()));
            } else if let ExprKind::Prop {
                base,
                name: MemberName::Ident(s),
                ..
            } = &target.kind
            {
                if *s == name && !is_this(base, fa) {
                    // `$other->prop = …`: evidence when the receiver is provably
                    // this class, ignorable when provably another, bail otherwise.
                    match fa.type_of(base.as_ref()) {
                        Type::Named { fqn, .. } if fqn.eq_ignore_ascii_case(class_fqn) => {
                            evidence.push(rhs, fa.type_of(rhs.as_ref()));
                        }
                        Type::Named { .. } => {}
                        _ => *bail = true,
                    }
                }
            } else if dynamic_this_member_write(target, fa) || contains_prop(target, name, fa) {
                // `$this->{$x} = …`, `[$a, $this->p] = …`, `$this->p[…] = …`.
                *bail = true;
            }
        }
        ExprKind::AssignOp { op, target, rhs } => {
            if is_this_prop(target, name, fa) {
                if matches!(op, php_ast::BinOp::Coalesce) {
                    // `??=` assigns exactly the RHS (or leaves the value alone).
                    evidence.push(rhs, fa.type_of(rhs.as_ref()));
                } else {
                    *bail = true;
                }
            } else if dynamic_this_member_write(target, fa) || contains_prop(target, name, fa) {
                *bail = true;
            }
        }
        ExprKind::AssignRef { target, rhs } => {
            // Aliasing in either direction makes future writes invisible.
            if contains_prop(target, name, fa)
                || contains_prop(rhs, name, fa)
                || dynamic_this_member_write(target, fa)
            {
                *bail = true;
            }
        }
        // The property passed as a bare call argument may bind to a by-ref
        // parameter (an invisible write: `sort($this->rows)`).
        ExprKind::Call { callee, args } => {
            for (idx, arg) in args.iter().enumerate() {
                if !arg.spread && is_this_prop(&arg.value, name, fa) {
                    match &callee.kind {
                        ExprKind::Name(n) => {
                            if resolved_param_by_ref_or_unknown(fa, scope_free_function(fa, n), idx)
                            {
                                *bail = true;
                            }
                        }
                        _ => *bail = true,
                    }
                }
            }
        }
        ExprKind::MethodCall {
            recv, method, args, ..
        } => {
            for (idx, arg) in args.iter().enumerate() {
                if !arg.spread && is_this_prop(&arg.value, name, fa) {
                    let known_safe = is_this(recv, fa)
                        && matches!(method, MemberName::Ident(m)
                            if method_param_not_by_ref(fa, class_fqn, fa.interner.resolve(*m), idx));
                    if !known_safe {
                        *bail = true;
                    }
                }
            }
        }
        ExprKind::StaticCall { args, .. } | ExprKind::New { args, .. } => {
            for arg in args {
                if !arg.spread && is_this_prop(&arg.value, name, fa) {
                    *bail = true;
                }
            }
        }
        _ => {}
    }
}

/// `$this->{$x}` / `$this->$x` as a write target could name any property.
fn dynamic_this_member_write(target: &Expr, fa: &FileAnalysis) -> bool {
    matches!(
        &target.kind,
        php_ast::ExprKind::Prop {
            base,
            name: php_ast::MemberName::Var(_) | php_ast::MemberName::Expr(_),
            ..
        } if is_this(base, fa)
    )
}

/// The reflected params of a free function named at this call, if resolvable.
fn scope_free_function<'a>(
    fa: &'a FileAnalysis,
    n: &php_ast::Name,
) -> Option<&'a [php_reflect::ParamReflection]> {
    // The per-file scope isn't in hand here; function names in fix evidence are
    // resolved through the file's pre-resolved references (span-keyed).
    let r = fa
        .resolved_refs
        .iter()
        .find(|r| r.span == n.span)
        .map(|r| &r.resolution)?;
    let lookup = |fqn: &str| fa.reflection.function(fqn).map(|f| f.params.as_slice());
    match r {
        Resolution::Fqn(fqn) => lookup(fqn),
        Resolution::Fallback { namespaced, global } => {
            lookup(namespaced).or_else(|| lookup(global))
        }
        _ => None,
    }
}

/// True (= bail) when the callee is unknown or its parameter at `idx` is by-ref.
fn resolved_param_by_ref_or_unknown(
    fa: &FileAnalysis,
    params: Option<&[php_reflect::ParamReflection]>,
    idx: usize,
) -> bool {
    let _ = fa;
    let Some(params) = params else { return true };
    match params.get(idx) {
        Some(p) => p.by_ref,
        None => params.last().is_none_or(|p| p.variadic && p.by_ref),
    }
}

/// Whether `class_fqn::method`'s parameter at `idx` is known and not by-ref.
fn method_param_not_by_ref(fa: &FileAnalysis, class_fqn: &str, method: &str, idx: usize) -> bool {
    let Some(found) = fa.reflection.find_method(class_fqn, method) else {
        return false;
    };
    match found.member.params.get(idx) {
        Some(p) => !p.by_ref,
        None => found
            .member
            .params
            .last()
            .is_some_and(|p| p.variadic && !p.by_ref),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_types::{CallableSig, ShapeField};

    fn named(fqn: &str) -> Type {
        Type::Named {
            fqn: fqn.into(),
            args: Vec::new(),
        }
    }

    #[test]
    fn renders_scalars_unions_and_generics() {
        let scope = Scope::global();
        assert_eq!(render_phpdoc(&Type::Int, &scope).as_deref(), Some("int"));
        assert_eq!(
            render_phpdoc(
                &Type::union(vec![Type::Int, Type::String, Type::Null]),
                &scope
            )
            .as_deref(),
            Some("int|string|null")
        );
        assert_eq!(
            render_phpdoc(
                &Type::Array(Some(Box::new((Type::Int, Type::String)))),
                &scope
            )
            .as_deref(),
            Some("array<int, string>")
        );
        assert_eq!(
            render_phpdoc(&Type::List(Box::new(Type::Float)), &scope).as_deref(),
            Some("list<float>")
        );
    }

    #[test]
    fn fqn_uses_short_name_when_it_round_trips() {
        let mut scope = Scope::in_namespace("App");
        scope.add_class_use("User", "App\\Models\\User");
        assert_eq!(
            render_phpdoc(&named("App\\Models\\User"), &scope).as_deref(),
            Some("User")
        );
        // Same-namespace classes round-trip without an import.
        assert_eq!(
            render_phpdoc(&named("App\\Service"), &scope).as_deref(),
            Some("Service")
        );
        // Not importable as a short name from here: fully qualify.
        assert_eq!(
            render_phpdoc(&named("Vendor\\Pkg\\Thing"), &scope).as_deref(),
            Some("\\Vendor\\Pkg\\Thing")
        );
        // Global classes inside a namespace need the backslash too.
        assert_eq!(
            render_phpdoc(&named("DateTimeImmutable"), &scope).as_deref(),
            Some("\\DateTimeImmutable")
        );
        // …but in the global namespace the short name round-trips.
        assert_eq!(
            render_phpdoc(&named("DateTimeImmutable"), &Scope::global()).as_deref(),
            Some("DateTimeImmutable")
        );
    }

    #[test]
    fn rejects_unrenderable_types() {
        let scope = Scope::global();
        for ty in [
            Type::Mixed,
            Type::ExplicitMixed,
            Type::Never,
            Type::Void,
            Type::Null,
            Type::Unknown("?".into()),
            Type::TemplateVar("T".into()),
            Type::SelfType,
            Type::StaticType,
            Type::IntRange {
                min: Some(0),
                max: None,
            },
            Type::union(vec![Type::Int, Type::Mixed]),
            Type::Array(Some(Box::new((Type::Int, Type::Mixed)))),
            Type::Named {
                fqn: "Box".into(),
                args: vec![Type::TemplateVar("T".into())],
            },
            Type::LiteralString("a'b".into()),
            Type::LiteralString("x*/y".into()),
            Type::Shape {
                fields: vec![ShapeField {
                    key: Some("two words".into()),
                    optional: false,
                    ty: Type::Int,
                }],
                sealed: true,
            },
            Type::Callable(Some(Box::new(CallableSig {
                params: vec![Type::Mixed],
                ret: Type::Bool,
            }))),
        ] {
            assert_eq!(render_phpdoc(&ty, &scope), None, "{ty:?}");
        }
    }

    #[test]
    fn anchors_on_the_declaration_line() {
        let src = "<?php\nclass C {\n    public function f() {}\n}\n";
        let name_at = src.find("f()").unwrap() as u32;
        let (anchor, indent) = doc_anchor(src, Span::new(name_at, name_at + 1), None).unwrap();
        let line_start = src.find("    public").unwrap() as u32;
        assert_eq!(anchor, FixAnchor::NewDocAt(line_start));
        assert_eq!(indent, "    ");
    }

    #[test]
    fn anchors_existing_docblock() {
        let src = "<?php\nclass C {\n\t/** hi */\n\tpublic function f() {}\n}\n";
        let name_at = src.find("f()").unwrap() as u32;
        let (anchor, indent) =
            doc_anchor(src, Span::new(name_at, name_at + 1), Some("/** hi */")).unwrap();
        let doc_at = src.find("/** hi */").unwrap() as u32;
        assert_eq!(
            anchor,
            FixAnchor::ExistingDoc(Span::new(doc_at, doc_at + 9))
        );
        assert_eq!(indent, "\t");
    }

    #[test]
    fn anchors_attribute_line_and_doc_above_attributes() {
        let src = "<?php\nclass C {\n    /** d */\n    #[Attr]\n    public function f() {}\n}\n";
        // First span = the attribute *name* (`Attr`), as rules pass it.
        let attr_at = src.find("Attr").unwrap() as u32;
        let (anchor, indent) =
            doc_anchor(src, Span::new(attr_at, attr_at + 4), Some("/** d */")).unwrap();
        let doc_at = src.find("/** d */").unwrap() as u32;
        assert_eq!(
            anchor,
            FixAnchor::ExistingDoc(Span::new(doc_at, doc_at + 8))
        );
        assert_eq!(indent, "    ");
        // And with no doc, the new block goes above the attribute line.
        let (anchor, _) = doc_anchor(src, Span::new(attr_at, attr_at + 4), None).unwrap();
        assert_eq!(
            anchor,
            FixAnchor::NewDocAt(src.find("    #[Attr]").unwrap() as u32)
        );
    }

    #[test]
    fn skips_declarations_not_starting_their_line() {
        let src = "<?php class C { public function f() {} }\n";
        let name_at = src.find("f()").unwrap() as u32;
        assert_eq!(doc_anchor(src, Span::new(name_at, name_at + 1), None), None);
    }
}
