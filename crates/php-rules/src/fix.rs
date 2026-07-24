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
    if matches!(ty, Type::Null) || !renderable(ty) {
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

/// Whether every node of `ty` has a faithful, context-free PHPDoc rendering.
fn renderable(ty: &Type) -> bool {
    match ty {
        // No information, bottom/return-position types, or context-dependent
        // names — never write these into a docblock we synthesize.
        Type::Mixed
        | Type::ExplicitMixed
        | Type::Never
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
        Type::Nullable(inner) => {
            !matches!(**inner, Type::Union(_) | Type::Intersection(_)) && renderable(inner)
        }
        // A literal string renders as `'…'`; reject contents that would break
        // the quoting or the surrounding comment.
        Type::LiteralString(s) => {
            !s.contains(['\'', '\\', '\n', '\r']) && !s.contains("*/")
        }
        Type::Shape { fields, .. } => fields.iter().all(|f| {
            f.key.as_deref().is_none_or(plain_shape_key) && renderable(&f.ty)
        }),
        Type::Array(kv) | Type::Iterable(kv) => kv
            .as_deref()
            .is_none_or(|(k, v)| renderable(k) && renderable(v)),
        Type::List(inner) | Type::ClassString(Some(inner)) | Type::NonEmpty(inner) => {
            renderable(inner)
        }
        Type::Callable(sig) => sig
            .as_deref()
            .is_none_or(|s| s.params.iter().all(renderable) && renderable(&s.ret)),
        Type::Named { args, .. } => args.iter().all(renderable),
        Type::Union(parts) | Type::Intersection(parts) => {
            !parts.is_empty() && parts.iter().all(renderable)
        }
        _ => true,
    }
}

/// A shape key that renders back to parseable PHPDoc (identifier or number).
fn plain_shape_key(key: &str) -> bool {
    !key.is_empty()
        && (key.chars().all(|c| c.is_ascii_digit())
            || (key.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
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
        c.is_ascii_alphanumeric() || matches!(c, '_' | '\\' | '|' | '&' | '?' | '(' | ')' | ' ' | '\t')
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
    let rendered = render_phpdoc(&widened, scope)?;
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
    let mut evidence = Evidence::default();
    if let Some(default) = &elem.default {
        let ctx = php_infer::TypeCtx::new(fa.reflection, scope, fa.interner);
        evidence.push(default, ctx.infer(default));
    }
    let mut bail = false;
    for m in &c.members {
        let php_ast::Member::Method(md) = m else { continue };
        let Some(body) = &md.body else { continue };
        for st in body {
            crate::walk::for_each_stmt_in_stmt(st, &mut |s| {
                // A foreach key/value target is a write we don't type.
                if let php_ast::StmtKind::Foreach { key, value, .. } = &s.kind {
                    if contains_prop(value, elem.name, fa)
                        || key.as_ref().is_some_and(|k| contains_prop(k, elem.name, fa))
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
    if bail {
        return None;
    }
    evidence.into_type()
}

/// Whether any ancestor class or used trait (transitively) has a method body
/// with a write-shaped use of `$this->{name}`. Unknown non-builtin ancestors
/// count as writes (can't verify). Bodies share the run-wide interner, so the
/// `Symbol` compares across files.
fn ancestors_write_property(
    fa: &FileAnalysis,
    class_fqn: &str,
    name: php_intern::Symbol,
) -> bool {
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
        let shadowed_private = cr.properties.iter().any(|p| {
            p.name == prop_str && p.visibility == php_ast::Visibility::Private
        });
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
                    let known_safe = static_class_fqn(scope, class, class_fqn)
                        .is_some_and(|fqn| {
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
            let all_iterable = !types.is_empty() && types.iter().all(|t| {
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
        let (anchor, indent) =
            doc_anchor(src, Span::new(name_at, name_at + 1), None).unwrap();
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
        assert_eq!(anchor, FixAnchor::ExistingDoc(Span::new(doc_at, doc_at + 9)));
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
        assert_eq!(anchor, FixAnchor::ExistingDoc(Span::new(doc_at, doc_at + 8)));
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
