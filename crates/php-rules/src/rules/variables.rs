//! phpstan category **Variables** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Variables/` — 12 rule(s) at level(s) 0,1,3.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented here:
//! - **ThisInGlobalStatementRule** (`global.this`, level 0) — `global $this;`.
//! - **ThisInStaticStatementRule** (`static.this`, level 0) — `static $this;`.
//! - **InvalidVariableAssignRule** (`assign.this`, level 0) — re-assigning
//!   `$this` (`$this = …`, `$this op= …`, `$this =& …`); skipped when the
//!   enclosing class implements `ArrayAccess` (matching phpstan).
//! - **VariableCloningRule** (`clone.nonObject`, level 3) — `clone $x` where the
//!   inferred type is a concrete non-object (scalar/array/null). Lenient: only
//!   fires when the type is *known* non-cloneable.
//! - **ParameterOutAssignedTypeRule** (`parameterByRef.type`, level 3) — safe
//!   fallback branch: assignment to a named function/method by-reference
//!   parameter whose declared by-ref type definitely rejects the assigned value.
//!
//! - **DefinedVariableRule** (`variable.undefined`, level 0) — a variable read
//!   that is undefined (or, flow-sensitively, possibly undefined) on the path to
//!   its use. Backed by the Cap #5 definedness lattice (`php_infer`), which bails
//!   conservatively on scopes using `extract`/`$$x`/`eval`/… so it under-reports
//!   rather than false-positives.
//!
//! - **CompactVariablesRule** (`variable.undefined`, level 0) — a constant-string
//!   argument to `compact()` (directly, or nested in an array literal) that names
//!   a variable never bound anywhere in the enclosing scope. We answer at *scope*
//!   granularity (never-assigned ⇒ definitely undefined), not flow-position
//!   granularity: this under-reports (misses use-before-assign) but cannot false-
//!   positive. The scope is skipped entirely when it uses an escape hatch
//!   (`extract`/`$$x`/`eval`/…) that could define arbitrary variables.
//! - **IssetRule** / **EmptyRule** / **NullCoalesceRule** (`isset.*`,
//!   `empty.*`, `nullCoalesce.*`, level 1) — a conservative local clone of
//!   phpstan's `IssetCheck`: never-defined simple variables, sealed array-shape
//!   missing offsets, and always-existing non-null/falsy facts when the current
//!   expression type proves them.
//! - **UnsetRule** (`unset.variable`, `unset.offset`, level 0) — safe subset:
//!   never-defined simple variables and missing offsets on sealed array shapes.
//!
//! Deferred:
//! - `UnsetRule` readonly/hooked/possibly-hooked property branches — need
//!   property-initialization/hook reflection to match phpstan without FPs.
//! - `ParameterOutAssignedTypeRule` true `@param-out` branch — needs first-class
//!   parameter-out reflection to avoid duplicating execution-end reports.
//! - **AssignToByRefExprFromForeachRule** (`assign.byRefForeachExpr`, level 0) —
//!   assigning to a dangling by-ref `foreach` variable after the loop (Cap #6).

use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{Arg, Expr, ExprKind, FunctionDecl, Member, Param, Stmt, StmtKind};
use php_diagnostics::Diagnostic;
use php_infer::TypeCtx;
use php_intern::Interner;
use php_reflect::{resolve_doc_type, ParamReflection};
use php_resolve::{for_each_region, Scope};
use php_types::Type;
use std::collections::{HashMap, HashSet};

// ---------------------------------------------------------------------------
// ThisInGlobalStatementRule — `global $this;`
// ---------------------------------------------------------------------------

/// `global $this;` — `$this` cannot be a global variable.
///
/// Mirrors phpstan's `ThisInGlobalStatementRule`.
fn run_this_in_global(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        let StmtKind::Global(vars) = &s.kind else {
            return;
        };
        for v in vars {
            if is_this_variable(&v.kind, fa) {
                out.push(
                    Diagnostic::error(v.span, "Cannot use $this as global variable.")
                        .with_code("global.this"),
                );
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// ThisInStaticStatementRule — `static $this;`
// ---------------------------------------------------------------------------

/// `static $this;` — `$this` cannot be a static variable.
///
/// Mirrors phpstan's `ThisInStaticStatementRule`.
fn run_this_in_static(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        let StmtKind::StaticVars(vars) = &s.kind else {
            return;
        };
        for v in vars {
            if fa.interner.resolve(v.name) == "this" {
                out.push(
                    Diagnostic::error(s.span, "Cannot use $this as static variable.")
                        .with_code("static.this"),
                );
            }
        }
    });
    out
}

// ---------------------------------------------------------------------------
// InvalidVariableAssignRule — re-assigning `$this`
// ---------------------------------------------------------------------------

/// Re-assigning `$this` (`$this = …`, `$this op= …`, `$this =& …`).
///
/// Mirrors phpstan's `InvalidVariableAssignRule`. The one exception phpstan
/// makes is a class implementing `ArrayAccess` (where `$this[...] = …` desugars
/// differently) — we honour that by skipping when the enclosing class is known
/// to implement `ArrayAccess`.
fn run_invalid_this_assign(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    // Class regions: walk each class body and skip ArrayAccess implementers.
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            visit_for_this_assign(st, fa, scope, None, &mut out);
        }
    });
    out
}

/// `enclosing_class` = the FQN of the class whose body we're inside, if any.
fn visit_for_this_assign(
    st: &Stmt,
    fa: &FileAnalysis,
    scope: &php_resolve::Scope,
    enclosing_class: Option<&str>,
    out: &mut Vec<Diagnostic>,
) {
    // Enter class bodies to learn the enclosing-class FQN (for ArrayAccess).
    if let StmtKind::Class(c) = &st.kind {
        let fqn = c.name.map(|n| scope.qualify(fa.interner.resolve(n)));
        for m in &c.members {
            let Member::Method(md) = m else { continue };
            let Some(body) = &md.body else { continue };
            for s in body {
                scan_stmt_exprs_for_this_assign(s, fa, fqn.as_deref(), out);
            }
        }
        return;
    }
    // Outside a class, descend into control-flow / functions to reach assignments.
    scan_stmt_exprs_for_this_assign(st, fa, enclosing_class, out);
}

fn scan_stmt_exprs_for_this_assign(
    st: &Stmt,
    fa: &FileAnalysis,
    enclosing_class: Option<&str>,
    out: &mut Vec<Diagnostic>,
) {
    let implements_array_access =
        enclosing_class.is_some_and(|c| fa.reflection.is_subclass_of(c, "ArrayAccess"));
    if implements_array_access {
        return;
    }
    walk::for_each_expr(
        &php_ast::Program {
            stmts: vec![st.clone()],
        },
        &mut |e| {
            let target = match &e.kind {
                ExprKind::Assign { target, .. }
                | ExprKind::AssignOp { target, .. }
                | ExprKind::AssignRef { target, .. } => target,
                _ => return,
            };
            if is_this_variable(&target.kind, fa) {
                out.push(
                    Diagnostic::error(target.span, "Cannot re-assign $this.")
                        .with_code("assign.this"),
                );
            }
        },
    );
}

/// Whether an expression kind is the bare `$this` variable.
fn is_this_variable(kind: &ExprKind, fa: &FileAnalysis) -> bool {
    matches!(kind, ExprKind::Variable(s) if fa.interner.resolve(*s) == "this")
}

// ---------------------------------------------------------------------------
// VariableCloningRule — `clone <non-object>`
// ---------------------------------------------------------------------------

/// `clone $x` where `$x` has a concrete non-object type.
///
/// Mirrors phpstan's `VariableCloningRule` (`clone.nonObject`). Lenient: we only
/// fire when the inferred type is *definitely* non-cloneable (a scalar, array, or
/// null). `mixed`/`object`/class types / unknowns are left alone to avoid false
/// positives.
fn run_variable_cloning(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for clone in fa.facts.clones() {
        let inner = clone.inner;
        let ty = fa.type_of(inner);
        if !is_definitely_non_object(&ty) {
            continue;
        }
        // Match phpstan's two message shapes (variable vs. arbitrary expression).
        if let ExprKind::Variable(s) = &inner.kind {
            let name = fa.interner.resolve(*s);
            out.push(
                Diagnostic::error(
                    clone.expr.span,
                    format!("Cannot clone non-object variable ${name} of type {ty}."),
                )
                .with_code("clone.nonObject"),
            );
        } else {
            out.push(
                Diagnostic::error(clone.expr.span, format!("Cannot clone {ty}."))
                    .with_code("clone.nonObject"),
            );
        }
    }
    out
}

/// A type that is definitely not an object (and thus not cloneable). Conservative:
/// anything composite, generic, templated, or unknown returns `false`.
fn is_definitely_non_object(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Null
            | Type::Bool
            | Type::True
            | Type::False
            | Type::Int
            | Type::Float
            | Type::String
            | Type::Array(_)
            | Type::List(_)
            | Type::LiteralInt(_)
            | Type::LiteralString(_)
    )
}

// ---------------------------------------------------------------------------
// ParameterOutAssignedTypeRule — assignment to by-ref params
// ---------------------------------------------------------------------------

/// PHPStan's `ParameterOutAssignedTypeRule` has two branches:
/// `@param-out` and fallback by-ref parameter type. Until reflection carries an
/// explicit out type, implement only the fallback branch: inside a named
/// function/method, assigning a value that definitely does not fit the declared
/// type of a by-reference parameter.
fn run_parameter_out_assigned_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            walk::for_each_stmt_in_stmt(st, &mut |s| match &s.kind {
                StmtKind::Function(f) => {
                    check_byref_param_assignments_in_function(scope, f, fa, &mut out)
                }
                StmtKind::Class(c) => {
                    let Some(name) = c.name else {
                        return;
                    };
                    let fqn = scope.qualify(fa.interner.resolve(name));
                    let class_refl = fa.reflect_class(scope, &fqn, c);
                    for member in &c.members {
                        let Member::Method(m) = member else {
                            continue;
                        };
                        let Some(body) = &m.body else {
                            continue;
                        };
                        let method_name = fa.interner.resolve(m.name);
                        let Some(method_refl) = class_refl
                            .methods
                            .iter()
                            .find(|r| !r.magic && r.name.eq_ignore_ascii_case(method_name))
                        else {
                            continue;
                        };
                        let description =
                            format!("method {}::{}()", class_refl.fqn, method_refl.name);
                        check_byref_param_assignments(
                            body,
                            &method_refl.params,
                            &description,
                            fa,
                            &mut out,
                        );
                    }
                }
                _ => {}
            });
        }
    });
    out
}

fn check_byref_param_assignments_in_function(
    scope: &php_resolve::Scope,
    f: &FunctionDecl,
    fa: &FileAnalysis,
    out: &mut Vec<Diagnostic>,
) {
    let refl = fa.reflect_function(scope, f);
    let description = format!("function {}()", refl.fqn);
    check_byref_param_assignments(&f.body, &refl.params, &description, fa, out);
}

fn check_byref_param_assignments(
    body: &[Stmt],
    params: &[ParamReflection],
    function_description: &str,
    fa: &FileAnalysis,
    out: &mut Vec<Diagnostic>,
) {
    let byref: Vec<&ParamReflection> = params.iter().filter(|p| p.by_ref && !p.variadic).collect();
    if byref.is_empty() {
        return;
    }

    for st in body {
        walk::for_each_expr_in_scope(st, &mut |e| {
            let Some((target, assigned)) = variable_assignment(e) else {
                return;
            };
            let ExprKind::Variable(sym) = &target.kind else {
                return;
            };
            let name = fa.interner.resolve(*sym);
            let Some(param) = byref.iter().find(|p| p.name == name) else {
                return;
            };
            if fa.accepts(assigned, &param.ty, &param.native_ty) {
                return;
            }
            let given = fa.type_of(assigned);
            out.push(
                Diagnostic::error(
                    e.span,
                    format!(
                        "Parameter &${} by-ref type of {} expects {}, {} given.",
                        param.name, function_description, param.ty, given
                    ),
                )
                .with_code("parameterByRef.type"),
            );
        });
    }
}

fn variable_assignment(e: &Expr) -> Option<(&Expr, &Expr)> {
    match &e.kind {
        ExprKind::Assign { target, rhs } | ExprKind::AssignRef { target, rhs } => {
            Some((target, rhs))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// ParameterOutExecutionEndTypeRule — final by-ref param-out type
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct ParamOutType {
    name: String,
    ty: Type,
}

/// Conservative `ParameterOutExecutionEndTypeRule` (`paramOut.type`): explicit
/// `@param-out` tags on named functions and private methods, checked only when
/// the body is straight-line and the final parameter type is obvious.
fn run_parameter_out_execution_end_type(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for st in region {
            walk::for_each_stmt_in_stmt(st, &mut |s| match &s.kind {
                StmtKind::Function(f) => {
                    check_param_out_execution_function(scope, f, fa, &mut out);
                }
                StmtKind::Class(c) => {
                    let Some(class_name) = c.name else {
                        return;
                    };
                    let class_fqn = scope.qualify(fa.interner.resolve(class_name));
                    let class_refl = fa.reflect_class(scope, &class_fqn, c);
                    let class_templates = doc_templates(c.doc.as_deref());
                    for member in &c.members {
                        let Member::Method(m) = member else {
                            continue;
                        };
                        if m.modifiers.visibility != Some(php_ast::Visibility::Private) {
                            continue;
                        }
                        let Some(body) = &m.body else {
                            continue;
                        };
                        let method_name = fa.interner.resolve(m.name);
                        let Some(method_refl) = class_refl
                            .methods
                            .iter()
                            .find(|r| !r.magic && r.name.eq_ignore_ascii_case(method_name))
                        else {
                            continue;
                        };
                        let description =
                            format!("method {}::{}()", class_refl.fqn, method_refl.name);
                        let templates = combined_templates(&class_templates, m.doc.as_deref());
                        check_param_out_execution_body(
                            scope,
                            m.doc.as_deref(),
                            &templates,
                            body,
                            &m.params,
                            &method_refl.params,
                            Some(class_refl.fqn.as_str()),
                            &description,
                            fa,
                            &mut out,
                        );
                    }
                }
                _ => {}
            });
        }
    });
    out
}

fn check_param_out_execution_function(
    scope: &Scope,
    f: &FunctionDecl,
    fa: &FileAnalysis,
    out: &mut Vec<Diagnostic>,
) {
    let refl = fa.reflect_function(scope, f);
    let description = format!("function {}()", refl.fqn);
    let templates = doc_templates(f.doc.as_deref());
    check_param_out_execution_body(
        scope,
        f.doc.as_deref(),
        &templates,
        &f.body,
        &f.params,
        &refl.params,
        None,
        &description,
        fa,
        out,
    );
}

#[allow(clippy::too_many_arguments)]
fn check_param_out_execution_body(
    scope: &Scope,
    doc: Option<&str>,
    templates: &[String],
    body: &[Stmt],
    ast_params: &[Param],
    params: &[ParamReflection],
    class_fqn: Option<&str>,
    function_description: &str,
    fa: &FileAnalysis,
    out: &mut Vec<Diagnostic>,
) {
    let param_outs = param_out_types(scope, doc, templates);
    if param_outs.is_empty() {
        return;
    }
    let Some(final_vars) = straight_line_final_vars(body, params, scope, class_fqn, fa) else {
        return;
    };

    for po in param_outs {
        if param_out_type_is_uncertain(&po.ty) {
            continue;
        }
        let Some(param) = params
            .iter()
            .find(|p| p.name == po.name && p.by_ref && !p.variadic)
        else {
            continue;
        };
        let Some(final_ty) = final_vars.get(&po.name) else {
            continue;
        };
        if param_out_type_is_uncertain(final_ty)
            || crate::is_assignable(fa.reflection, final_ty, &po.ty)
        {
            continue;
        }
        out.push(
            Diagnostic::error(
                param_decl_span(ast_params, &param.name, fa.interner)
                    .unwrap_or_else(|| body.first().map_or(php_span::Span::at(0), |s| s.span)),
                format!(
                    "Parameter &${} @param-out type of {} expects {}, {} given.",
                    po.name,
                    function_description,
                    phpstan_type(&po.ty),
                    phpstan_type(final_ty),
                ),
            )
            .with_code("paramOut.type"),
        );
    }
}

fn param_out_types(scope: &Scope, doc: Option<&str>, templates: &[String]) -> Vec<ParamOutType> {
    let Some(raw) = doc else {
        return Vec::new();
    };
    let mut out: Vec<(i8, ParamOutType)> = Vec::new();
    for tag in php_phpdoc::parse_block(raw).tags {
        let (base, pri) = doc_tag_base_priority(&tag.name);
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

fn doc_templates(doc: Option<&str>) -> Vec<String> {
    doc.map(php_phpdoc::parse)
        .unwrap_or_default()
        .templates
        .into_iter()
        .map(|t| t.name)
        .collect()
}

fn combined_templates(class_templates: &[String], method_doc: Option<&str>) -> Vec<String> {
    let mut templates = class_templates.to_vec();
    templates.extend(doc_templates(method_doc));
    templates
}

fn doc_tag_base_priority(name: &str) -> (&str, i8) {
    php_phpdoc::query::base_priority(name)
}

fn straight_line_final_vars(
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

fn direct_variable_assignment<'a>(e: &'a Expr, fa: &FileAnalysis) -> Option<(String, &'a Expr)> {
    match &e.kind {
        ExprKind::Paren(inner) => direct_variable_assignment(inner, fa),
        ExprKind::Assign { target, rhs } => match &target.kind {
            ExprKind::Variable(sym) => Some((fa.interner.resolve(*sym).to_string(), rhs)),
            _ => None,
        },
        _ => None,
    }
}

fn rhs_is_obvious(e: &Expr) -> bool {
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

fn param_out_type_is_uncertain(ty: &Type) -> bool {
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
        | Type::NonEmpty(inner) => param_out_type_is_uncertain(inner),
        Type::Union(parts) | Type::Intersection(parts) => {
            parts.iter().any(param_out_type_is_uncertain)
        }
        Type::Array(Some(pair)) | Type::Iterable(Some(pair)) => {
            param_out_type_is_uncertain(&pair.0) || param_out_type_is_uncertain(&pair.1)
        }
        Type::Shape { fields, .. } => fields.iter().any(|f| param_out_type_is_uncertain(&f.ty)),
        Type::Callable(Some(sig)) => {
            sig.params.iter().any(param_out_type_is_uncertain)
                || param_out_type_is_uncertain(&sig.ret)
        }
        Type::Named { args, .. } => args.iter().any(param_out_type_is_uncertain),
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
        | Type::EnumCase { .. }
        | Type::LiteralInt(_)
        | Type::LiteralString(_) => false,
    }
}

fn phpstan_type(ty: &Type) -> String {
    match ty {
        Type::Nullable(inner) => format!("{}|null", phpstan_type(inner)),
        Type::Union(parts) => parts.iter().map(phpstan_type).collect::<Vec<_>>().join("|"),
        other => other.to_string(),
    }
}

fn param_decl_span(params: &[Param], name: &str, interner: &Interner) -> Option<php_span::Span> {
    params
        .iter()
        .find(|p| interner.resolve(p.name) == name)
        .map(|p| p.span)
}

// ---------------------------------------------------------------------------
// DefinedVariableRule — `variable.undefined`
// ---------------------------------------------------------------------------

/// `variable.undefined` (level 0): a variable read that is *definitely* undefined
/// on the path to its use (phpstan's `Undefined variable:` case). Backed by the
/// Cap #5 definedness lattice.
fn run_defined_variable(fa: &FileAnalysis) -> Vec<Diagnostic> {
    crate::undefined_variables_with(fa.program, fa.interner, &fa.terminators)
        .into_iter()
        .filter(|u| u.definite)
        .map(|u| {
            Diagnostic::error(u.span, format!("Undefined variable: ${}", u.name))
                .with_code("variable.undefined")
        })
        .collect()
}

/// `variable.undefined` (level 1): a variable read that is *possibly* undefined
/// (assigned on only some paths). phpstan gates this behind
/// `checkMaybeUndefinedVariables`, enabled from level 1.
fn run_maybe_undefined_variable(fa: &FileAnalysis) -> Vec<Diagnostic> {
    crate::undefined_variables_with(fa.program, fa.interner, &fa.terminators)
        .into_iter()
        .filter(|u| !u.definite)
        .map(|u| {
            Diagnostic::error(
                u.span,
                format!("Variable ${} might not be defined.", u.name),
            )
            .with_code("variable.undefined")
        })
        .collect()
}

// ---------------------------------------------------------------------------
// IssetCheck-family rules — `isset`, `empty`, `??`, `??=`
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
enum IssetLike {
    Isset,
    Empty,
    NullCoalesce,
    NullCoalesceAssign,
}

impl IssetLike {
    fn base_id(self) -> &'static str {
        match self {
            IssetLike::Isset => "isset",
            IssetLike::Empty => "empty",
            IssetLike::NullCoalesce | IssetLike::NullCoalesceAssign => "nullCoalesce",
        }
    }

    fn operator_description(self) -> &'static str {
        match self {
            IssetLike::Isset => "in isset()",
            IssetLike::Empty => "in empty()",
            IssetLike::NullCoalesce => "on left side of ??",
            IssetLike::NullCoalesceAssign => "on left side of ??=",
        }
    }
}

struct IssetFacts {
    bound: HashSet<String>,
    has_escape: bool,
}

/// `isset($x)` checks where `$x` is never defined, or is definitely present with
/// a non-nullable / always-null type. Mirrors phpstan's `IssetRule` where our
/// facts are certain.
fn run_isset(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let facts = isset_facts(fa);
    if facts.has_escape {
        return Vec::new();
    }
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Isset(vars) = &e.kind else {
            return;
        };
        for v in vars {
            if let Some(d) = check_isset_like(v, fa, &facts.bound, IssetLike::Isset) {
                out.push(d);
            }
        }
    });
    out
}

/// `empty($x)` checks where `$x` is never defined, or is definitely present with
/// an always-falsy / never-falsy type. Mirrors phpstan's `EmptyRule` where our
/// facts are certain.
fn run_empty(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let facts = isset_facts(fa);
    if facts.has_escape {
        return Vec::new();
    }
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| {
        let ExprKind::Empty(inner) = &e.kind else {
            return;
        };
        if let Some(d) = check_isset_like(inner, fa, &facts.bound, IssetLike::Empty) {
            out.push(d);
        }
    });
    out
}

/// `??` / `??=` checks on the left-hand side. Mirrors phpstan's
/// `NullCoalesceRule` where our facts are certain.
fn run_null_coalesce(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let facts = isset_facts(fa);
    if facts.has_escape {
        return Vec::new();
    }
    let mut out = Vec::new();
    walk::for_each_expr(fa.program, &mut |e| match &e.kind {
        ExprKind::Coalesce { lhs, .. } => {
            if let Some(d) = check_isset_like(lhs, fa, &facts.bound, IssetLike::NullCoalesce) {
                out.push(d);
            }
        }
        ExprKind::AssignOp {
            op: php_ast::BinOp::Coalesce,
            target,
            ..
        } => {
            if let Some(d) =
                check_isset_like(target, fa, &facts.bound, IssetLike::NullCoalesceAssign)
            {
                out.push(d);
            }
        }
        _ => {}
    });
    out
}

/// Safe subset of phpstan's `UnsetRule`: definitely undefined simple variables
/// and definitely missing offsets on sealed array shapes.
fn run_unset(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let facts = unset_facts(fa);
    if facts.has_escape {
        return Vec::new();
    }
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        let StmtKind::Unset(vars) = &s.kind else {
            return;
        };
        for v in vars {
            if let Some(d) = check_unset_arg(v, fa, &facts.bound) {
                out.push(d);
            }
        }
    });
    out
}

fn check_isset_like(
    expr: &Expr,
    fa: &FileAnalysis,
    bound: &HashSet<String>,
    kind: IssetLike,
) -> Option<Diagnostic> {
    match &expr.kind {
        ExprKind::Paren(inner) => check_isset_like(inner, fa, bound, kind),
        ExprKind::Variable(sym) => {
            let name = fa.interner.resolve(*sym);
            if !is_always_defined_name(name) && !bound.contains(name) {
                return Some(
                    Diagnostic::error(
                        expr.span,
                        format!(
                            "Variable ${name} {} is never defined.",
                            kind.operator_description()
                        ),
                    )
                    .with_code(kind_code(kind, "variable")),
                );
            }
            if name == "_SESSION" {
                return None; // phpstan special-case: sessions are often conditionally started.
            }
            let ty = isset_type(fa, expr);
            type_message(kind, &ty).map(|msg| {
                Diagnostic::error(
                    expr.span,
                    format!(
                        "Variable ${name} {} always exists and {msg}.",
                        kind.operator_description()
                    ),
                )
                .with_code(kind_code(kind, "variable"))
            })
        }
        ExprKind::Index {
            base,
            index: Some(dim),
        } => {
            let base_ty = isset_type(fa, base);
            let dim_ty = isset_type(fa, dim);
            if let Some(key) = const_shape_key(dim) {
                if let Some(status) = shape_offset_status(&base_ty, &key) {
                    match status {
                        ShapeOffsetStatus::Missing => {
                            return Some(
                                Diagnostic::error(
                                    expr.span,
                                    format!(
                                        "Offset {dim_ty} on {base_ty} {} does not exist.",
                                        kind.operator_description()
                                    ),
                                )
                                .with_code(kind_code(kind, "offset")),
                            );
                        }
                        ShapeOffsetStatus::Present(value_ty) => {
                            if let Some(msg) = type_message(kind, &value_ty) {
                                return Some(
                                    Diagnostic::error(
                                        expr.span,
                                        format!(
                                            "Offset {dim_ty} on {base_ty} {} always exists and {msg}.",
                                            kind.operator_description()
                                        ),
                                    )
                                    .with_code(kind_code(kind, "offset")),
                                );
                            }
                        }
                        ShapeOffsetStatus::Maybe => {}
                    }
                }
            }
            check_undefined_for_isset_like(base, fa, bound, kind)
        }
        ExprKind::Index { base, index: None } => {
            check_undefined_for_isset_like(base, fa, bound, kind)
        }
        // phpstan's advanced isset check also reports some arbitrary expressions
        // and properties, but those use dedicated identifiers/message shapes. Stay
        // silent until we can mirror those paths exactly.
        _ => None,
    }
}

fn check_undefined_for_isset_like(
    expr: &Expr,
    fa: &FileAnalysis,
    bound: &HashSet<String>,
    kind: IssetLike,
) -> Option<Diagnostic> {
    match &expr.kind {
        ExprKind::Paren(inner) => check_undefined_for_isset_like(inner, fa, bound, kind),
        ExprKind::Variable(sym) => {
            let name = fa.interner.resolve(*sym);
            if is_always_defined_name(name) || bound.contains(name) {
                return None;
            }
            Some(
                Diagnostic::error(
                    expr.span,
                    format!(
                        "Variable ${name} {} is never defined.",
                        kind.operator_description()
                    ),
                )
                .with_code(kind_code(kind, "variable")),
            )
        }
        ExprKind::Index { base, .. } => check_undefined_for_isset_like(base, fa, bound, kind),
        ExprKind::Prop { base, .. } => check_undefined_for_isset_like(base, fa, bound, kind),
        ExprKind::StaticProp { class, .. } => {
            check_undefined_for_isset_like(class, fa, bound, kind)
        }
        _ => None,
    }
}

fn check_unset_arg(expr: &Expr, fa: &FileAnalysis, bound: &HashSet<String>) -> Option<Diagnostic> {
    match &expr.kind {
        ExprKind::Paren(inner) => check_unset_arg(inner, fa, bound),
        ExprKind::Variable(sym) => {
            let name = fa.interner.resolve(*sym);
            if is_always_defined_name(name) || bound.contains(name) {
                return None;
            }
            Some(
                Diagnostic::error(
                    expr.span,
                    format!("Call to function unset() contains undefined variable ${name}."),
                )
                .with_code("unset.variable"),
            )
        }
        ExprKind::Index {
            base,
            index: Some(dim),
        } => {
            let base_ty = isset_type(fa, base);
            let dim_ty = isset_type(fa, dim);
            if let Some(key) = const_shape_key(dim) {
                if matches!(
                    shape_offset_status(&base_ty, &key),
                    Some(ShapeOffsetStatus::Missing)
                ) {
                    return Some(
                        Diagnostic::error(
                            expr.span,
                            format!("Cannot unset offset {dim_ty} on {base_ty}."),
                        )
                        .with_code("unset.offset"),
                    );
                }
            }
            check_unset_arg(base, fa, bound)
        }
        ExprKind::Index { base, index: None } => check_unset_arg(base, fa, bound),
        _ => None,
    }
}

fn kind_code(kind: IssetLike, suffix: &str) -> &'static str {
    match (kind.base_id(), suffix) {
        ("isset", "variable") => "isset.variable",
        ("isset", "offset") => "isset.offset",
        ("isset", "expr") => "isset.expr",
        ("empty", "variable") => "empty.variable",
        ("empty", "offset") => "empty.offset",
        ("empty", "expr") => "empty.expr",
        ("nullCoalesce", "variable") => "nullCoalesce.variable",
        ("nullCoalesce", "offset") => "nullCoalesce.offset",
        ("nullCoalesce", "expr") => "nullCoalesce.expr",
        _ => "isset.expr",
    }
}

fn isset_type(fa: &FileAnalysis, expr: &Expr) -> Type {
    if fa.treat_phpdoc_types_as_certain {
        fa.type_of(expr)
    } else {
        fa.native_type_of(expr)
    }
}

fn type_message(kind: IssetLike, ty: &Type) -> Option<&'static str> {
    if type_is_uncertain(ty) || matches!(ty, Type::Never | Type::Void) {
        return None;
    }
    match kind {
        IssetLike::Isset | IssetLike::NullCoalesce | IssetLike::NullCoalesceAssign => {
            match null_verdict(ty) {
                Truth::Yes => Some("is always null"),
                Truth::No => Some("is not nullable"),
                Truth::Maybe => None,
            }
        }
        IssetLike::Empty => {
            let null = null_verdict(ty);
            let falsy = falsy_verdict(ty);
            if matches!(null, Truth::Maybe) || matches!(falsy, Truth::Maybe) {
                return None;
            }
            match (null, falsy) {
                (Truth::Yes, Truth::Yes) => Some("is always falsy"),
                (Truth::Yes, Truth::No) => Some("is not falsy"),
                (Truth::Yes, Truth::Maybe) => Some("is always null"),
                (_, Truth::Yes) => Some("is always falsy"),
                (_, Truth::No) => Some("is not falsy"),
                _ => Some("is not nullable"),
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Truth {
    Yes,
    No,
    Maybe,
}

fn null_verdict(ty: &Type) -> Truth {
    match ty {
        Type::Null => Truth::Yes,
        Type::Nullable(_) => Truth::Maybe,
        Type::Union(parts) => combine_truth(parts.iter().map(null_verdict)),
        Type::Mixed | Type::Unknown(_) | Type::TemplateVar(_) | Type::Conditional { .. } => {
            Truth::Maybe
        }
        _ => Truth::No,
    }
}

fn falsy_verdict(ty: &Type) -> Truth {
    match ty {
        Type::Null | Type::False => Truth::Yes,
        Type::True | Type::Object | Type::Named { .. } | Type::EnumCase { .. } | Type::ClassString(_) => Truth::No,
        Type::LiteralInt(0) => Truth::Yes,
        Type::LiteralInt(_) => Truth::No,
        Type::IntRange { min, max } if min == &Some(0) && max == &Some(0) => Truth::Yes,
        Type::IntRange { min, .. } if min.is_some_and(|n| n > 0) => Truth::No,
        Type::IntRange { max, .. } if max.is_some_and(|n| n < 0) => Truth::No,
        Type::LiteralString(s) if s.is_empty() || &**s == "0" => Truth::Yes,
        Type::LiteralString(_) => Truth::No,
        // A non-falsy or callable string is definitely truthy; other refined
        // strings can still be "0" (numeric) or "" ("0" for non-empty).
        Type::StringOf(
            php_types::StringRefinement::NonFalsy | php_types::StringRefinement::Callable,
        ) => Truth::No,
        // A non-empty array is truthy by definition.
        Type::NonEmpty(_) => Truth::No,
        Type::StringOf(_) => Truth::Maybe,
        Type::Shape {
            fields,
            sealed: true,
        } => {
            if fields.is_empty() {
                Truth::Yes
            } else if fields.iter().any(|f| !f.optional) {
                Truth::No
            } else {
                Truth::Maybe
            }
        }
        Type::Nullable(_) => Truth::Maybe,
        Type::Union(parts) => combine_truth(parts.iter().map(falsy_verdict)),
        Type::Mixed
        | Type::ExplicitMixed
        | Type::Unknown(_)
        | Type::TemplateVar(_)
        | Type::Conditional { .. }
        | Type::Bool
        | Type::Int
        | Type::Float
        | Type::String
        | Type::Resource
        | Type::Array(_)
        | Type::Iterable(_)
        | Type::List(_)
        | Type::Callable(_)
        | Type::IntRange { .. }
        | Type::Shape { sealed: false, .. }
        | Type::SelfType
        | Type::StaticType
        | Type::Parent
        | Type::Intersection(_)
        | Type::Never
        | Type::Void => Truth::Maybe,
    }
}

fn combine_truth<I>(mut verdicts: I) -> Truth
where
    I: Iterator<Item = Truth>,
{
    let Some(first) = verdicts.next() else {
        return Truth::Maybe;
    };
    if verdicts.all(|v| v == first) {
        first
    } else {
        Truth::Maybe
    }
}

fn type_is_uncertain(ty: &Type) -> bool {
    match ty {
        Type::Mixed | Type::Unknown(_) | Type::TemplateVar(_) | Type::Conditional { .. } => true,
        Type::Nullable(inner) => type_is_uncertain(inner),
        Type::Union(parts) | Type::Intersection(parts) => parts.iter().any(type_is_uncertain),
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            type_is_uncertain(&kv.0) || type_is_uncertain(&kv.1)
        }
        Type::List(inner) | Type::ClassString(Some(inner)) => type_is_uncertain(inner),
        Type::Callable(Some(sig)) => {
            sig.params.iter().any(type_is_uncertain) || type_is_uncertain(&sig.ret)
        }
        Type::Named { args, .. } => args.iter().any(type_is_uncertain),
        Type::Shape { fields, .. } => fields.iter().any(|f| type_is_uncertain(&f.ty)),
        _ => false,
    }
}

type ShapeOffsetStatus = php_infer::arrays::ShapeOffsetStatus;

fn shape_offset_status(base_ty: &Type, key: &str) -> Option<ShapeOffsetStatus> {
    php_infer::arrays::shape_offset_status(base_ty, key)
}

fn const_shape_key(expr: &Expr) -> Option<String> {
    php_infer::arrays::const_shape_key(expr)
}

fn is_always_defined_name(name: &str) -> bool {
    ALWAYS_DEFINED.contains(&name)
}

fn isset_facts(fa: &FileAnalysis) -> IssetFacts {
    facts_with_unset_binding(fa, true)
}

fn unset_facts(fa: &FileAnalysis) -> IssetFacts {
    facts_with_unset_binding(fa, false)
}

fn facts_with_unset_binding(fa: &FileAnalysis, count_unset: bool) -> IssetFacts {
    let mut bound = HashSet::new();
    let mut has_escape = false;

    for s in &fa.program.stmts {
        collect_all_bound_stmt(s, fa.interner, &mut bound, count_unset);
    }
    walk::for_each_expr(fa.program, &mut |e| {
        if expr_is_escape(e) {
            has_escape = true;
        }
        collect_bound_expr(e, fa.interner, &mut bound);
        match &e.kind {
            ExprKind::Closure(cl) => {
                for p in &cl.params {
                    bound.insert(fa.interner.resolve(p.name).to_string());
                }
                for u in &cl.uses {
                    bound.insert(fa.interner.resolve(u.name).to_string());
                }
            }
            ExprKind::ArrowFn(a) => {
                for p in &a.params {
                    bound.insert(fa.interner.resolve(p.name).to_string());
                }
            }
            _ => {}
        }
    });

    IssetFacts { bound, has_escape }
}

fn collect_all_bound_stmt(s: &Stmt, i: &Interner, bound: &mut HashSet<String>, count_unset: bool) {
    match &s.kind {
        StmtKind::Function(f) => {
            for p in &f.params {
                bound.insert(i.resolve(p.name).to_string());
            }
            for st in &f.body {
                collect_all_bound_stmt(st, i, bound, count_unset);
            }
        }
        StmtKind::Class(c) => {
            for m in &c.members {
                if let Member::Method(md) = m {
                    for p in &md.params {
                        bound.insert(i.resolve(p.name).to_string());
                    }
                    if let Some(b) = &md.body {
                        for st in b {
                            collect_all_bound_stmt(st, i, bound, count_unset);
                        }
                    }
                }
            }
        }
        StmtKind::Unset(vars) => {
            if count_unset {
                for v in vars {
                    if let ExprKind::Variable(sym) = &v.kind {
                        bound.insert(i.resolve(*sym).to_string());
                    }
                }
            }
        }
        StmtKind::Block(b) => {
            for st in b {
                collect_all_bound_stmt(st, i, bound, count_unset);
            }
        }
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            collect_all_bound_stmt(then, i, bound, count_unset);
            for ei in elseifs {
                collect_all_bound_stmt(&ei.body, i, bound, count_unset);
            }
            if let Some(e) = els {
                collect_all_bound_stmt(e, i, bound, count_unset);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. } => {
            collect_all_bound_stmt(body, i, bound, count_unset);
        }
        StmtKind::Foreach {
            key, value, body, ..
        } => {
            if let Some(k) = key {
                bind_target(k, i, bound);
            }
            bind_target(value, i, bound);
            collect_all_bound_stmt(body, i, bound, count_unset);
        }
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                for st in &c.body {
                    collect_all_bound_stmt(st, i, bound, count_unset);
                }
            }
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for st in body {
                collect_all_bound_stmt(st, i, bound, count_unset);
            }
            for c in catches {
                if let Some(v) = c.var {
                    bound.insert(i.resolve(v).to_string());
                }
                for st in &c.body {
                    collect_all_bound_stmt(st, i, bound, count_unset);
                }
            }
            if let Some(f) = finally {
                for st in f {
                    collect_all_bound_stmt(st, i, bound, count_unset);
                }
            }
        }
        StmtKind::Namespace { body: Some(b), .. } => {
            for st in b {
                collect_all_bound_stmt(st, i, bound, count_unset);
            }
        }
        StmtKind::Declare { body: Some(b), .. } => collect_all_bound_stmt(b, i, bound, count_unset),
        _ => collect_bound(s, i, bound),
    }
}

fn expr_is_escape(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::VariableVariable(_)
        | ExprKind::DollarBrace(_)
        | ExprKind::Eval(_)
        | ExprKind::Include { .. } => true,
        ExprKind::Call { callee, .. } => {
            let ExprKind::Name(n) = &callee.kind else {
                return false;
            };
            let last = n
                .text
                .rsplit('\\')
                .next()
                .unwrap_or(&n.text)
                .to_ascii_lowercase();
            ESCAPE_FUNCTIONS.contains(&last.as_str())
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// AssignToByRefExprFromForeachRule — `assign.byRefForeachExpr`
// ---------------------------------------------------------------------------

/// After `foreach ($arr as &$v) { … }`, `$v` is a dangling reference to the last
/// element; assigning to `$v` afterwards (without `unset($v)`) silently
/// overwrites that element. We track, in execution order within each scope, the
/// set of "dangling" by-ref foreach variables and flag a later plain assignment
/// to one. `unset`/re-binding clears it. Conservative (direct `$v = …` only).
fn run_byref_foreach(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut dangling = HashSet::new();
    byref_seq(&fa.program.stmts, fa, &mut dangling, &mut out);
    out
}

fn byref_seq(
    stmts: &[Stmt],
    fa: &FileAnalysis,
    dangling: &mut HashSet<String>,
    out: &mut Vec<Diagnostic>,
) {
    for s in stmts {
        byref_stmt(s, fa, dangling, out);
    }
}

/// Process one branch of a conditional from a clone of the entry dangling set,
/// then shrink `keep` to the variables this branch left dangling (so a variable
/// survives past the conditional only if *no* branch cleared it).
fn byref_branch(
    body: &Stmt,
    fa: &FileAnalysis,
    entry: &HashSet<String>,
    keep: &mut HashSet<String>,
    out: &mut Vec<Diagnostic>,
) {
    let mut d = entry.clone();
    byref_stmt(body, fa, &mut d, out);
    keep.retain(|v| d.contains(v));
}

fn byref_stmt(
    s: &Stmt,
    fa: &FileAnalysis,
    dangling: &mut HashSet<String>,
    out: &mut Vec<Diagnostic>,
) {
    let var_name = |e: &Expr| match &e.kind {
        ExprKind::Variable(sym) => Some(fa.interner.resolve(*sym).to_string()),
        _ => None,
    };
    match &s.kind {
        StmtKind::Foreach {
            key,
            value,
            by_ref,
            body,
            ..
        } => {
            // The foreach *header* rebinds key/value to fresh references at the
            // start of the loop, so any prior dangling status for them is cleared
            // before the body runs — assigning to the by-ref variable *inside* its
            // own loop is the legitimate in-place-edit idiom, never a dangling write.
            if let Some(name) = var_name(value) {
                dangling.remove(&name);
            }
            if let Some(k) = key {
                if let Some(name) = var_name(k) {
                    dangling.remove(&name);
                }
            }
            byref_stmt(body, fa, dangling, out);
            // After the loop, a by-ref value variable dangles (it still references
            // the last element); a by-value foreach leaves it rebound (cleared).
            if let Some(name) = var_name(value) {
                if *by_ref {
                    dangling.insert(name);
                } else {
                    dangling.remove(&name);
                }
            }
        }
        StmtKind::Expr(e) => {
            if let ExprKind::Assign { target, .. } = &e.kind {
                if let Some(name) = var_name(target) {
                    if dangling.remove(&name) {
                        out.push(
                            Diagnostic::error(
                                e.span,
                                format!(
                                    "Assign to ${name} overwrites the last element from array."
                                ),
                            )
                            .with_code("assign.byRefForeachExpr"),
                        );
                    }
                }
            }
        }
        StmtKind::Unset(vars) => {
            for v in vars {
                if let Some(name) = var_name(v) {
                    dangling.remove(&name);
                }
            }
        }
        StmtKind::Block(b) => byref_seq(b, fa, dangling, out),
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            // Branches are mutually-exclusive paths: process each from a *clone* of
            // the entry set so a foreach arming a variable in one branch doesn't
            // leak into a sibling branch. A variable stays dangling after the `if`
            // only if no branch cleared it (FP-safe).
            let entry = dangling.clone();
            let mut keep = entry.clone();
            byref_branch(then, fa, &entry, &mut keep, out);
            for ei in elseifs {
                byref_branch(&ei.body, fa, &entry, &mut keep, out);
            }
            if let Some(e) = els {
                byref_branch(e, fa, &entry, &mut keep, out);
            }
            *dangling = keep;
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. } => {
            byref_stmt(body, fa, dangling, out);
        }
        StmtKind::Switch { cases, .. } => {
            let entry = dangling.clone();
            let mut keep = entry.clone();
            for c in cases {
                let mut d = entry.clone();
                byref_seq(&c.body, fa, &mut d, out);
                keep.retain(|v| d.contains(v));
            }
            *dangling = keep;
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            byref_seq(body, fa, dangling, out);
            for c in catches {
                byref_seq(&c.body, fa, dangling, out);
            }
            if let Some(f) = finally {
                byref_seq(f, fa, dangling, out);
            }
        }
        // New scopes get a fresh dangling set.
        StmtKind::Function(f) => byref_seq(&f.body, fa, &mut HashSet::new(), out),
        StmtKind::Class(c) => {
            for m in &c.members {
                if let Member::Method(md) = m {
                    if let Some(b) = &md.body {
                        byref_seq(b, fa, &mut HashSet::new(), out);
                    }
                }
            }
        }
        StmtKind::Namespace { body: Some(b), .. } => byref_seq(b, fa, dangling, out),
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// CompactVariablesRule — `compact('undefinedVar')`
// ---------------------------------------------------------------------------

/// PHP superglobals + always-available variables (never "undefined").
const ALWAYS_DEFINED: &[&str] = &[
    "GLOBALS",
    "_SERVER",
    "_GET",
    "_POST",
    "_FILES",
    "_COOKIE",
    "_SESSION",
    "_REQUEST",
    "_ENV",
    "this",
    "http_response_header",
    "argc",
    "argv",
    "php_errormsg",
];

/// Functions that can introduce arbitrary variables into a scope — their presence
/// makes scope-level "never assigned" reasoning unsafe, so we skip the scope.
const ESCAPE_FUNCTIONS: &[&str] = &[
    "extract",
    "parse_str",
    "mb_parse_str",
    "eval",
    "get_defined_vars",
];

/// `compact('x')` (or `compact(['x', 'y'])`) naming a variable that is never
/// bound anywhere in the enclosing scope. Mirrors phpstan's
/// `CompactVariablesRule` for the definite-undefined case (`$scopeHasVariable->no()`).
fn run_compact_variables(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    // Each scope: collect the names it ever binds, then check its compact() calls.
    // The global region is one scope; functions/methods/closures/arrows are their
    // own scopes (a captured/param/global var bound there is "defined").
    check_scope(&fa.program.stmts, &HashSet::new(), fa, &mut out);
    out
}

/// Analyse one scope. `seed` holds names defined by the signature/captures.
fn check_scope(
    body: &[Stmt],
    seed: &HashSet<String>,
    fa: &FileAnalysis,
    out: &mut Vec<Diagnostic>,
) {
    // Descend into nested scopes regardless (they're checked independently).
    descend_scopes(body, fa, out);

    if scope_has_escape(body, fa.interner) {
        return; // can't reason about definedness in this scope
    }

    // All variables ever bound anywhere in this scope (flow-insensitive: a name
    // bound on *any* path means it's not "never defined").
    let mut bound: HashSet<String> = seed.clone();
    for s in body {
        collect_bound(s, fa.interner, &mut bound);
    }

    // Check every compact() call in this scope (not crossing into nested scopes).
    for s in body {
        walk::for_each_expr_in_scope(s, &mut |e| {
            let Some(args) = compact_args(e, fa) else {
                return;
            };
            for arg in args {
                for (name, span) in constant_string_names(&arg.value) {
                    if ALWAYS_DEFINED.contains(&name.as_str()) || bound.contains(&name) {
                        continue;
                    }
                    out.push(
                        Diagnostic::error(
                            span,
                            format!(
                                "Call to function compact() contains undefined variable ${name}."
                            ),
                        )
                        .with_code("variable.undefined"),
                    );
                }
            }
        });
    }
}

/// Recurse into nested function/method/closure/arrow scopes, seeding each with
/// its parameter (and closure-`use`) names.
fn descend_scopes(body: &[Stmt], fa: &FileAnalysis, out: &mut Vec<Diagnostic>) {
    for s in body {
        match &s.kind {
            StmtKind::Function(f) => {
                check_scope(&f.body, &param_names(&f.params, fa.interner), fa, out)
            }
            StmtKind::Class(c) => {
                for m in &c.members {
                    if let Member::Method(md) = m {
                        if let Some(b) = &md.body {
                            check_scope(b, &param_names(&md.params, fa.interner), fa, out);
                        }
                    }
                }
            }
            StmtKind::Namespace { body: Some(b), .. } => descend_scopes(b, fa, out),
            _ => {}
        }
        // Closures / arrow-fns appear inside expressions; find them too.
        walk::for_each_expr_in_scope(s, &mut |e| match &e.kind {
            ExprKind::Closure(cl) => {
                let mut seed = param_names(&cl.params, fa.interner);
                for u in &cl.uses {
                    seed.insert(fa.interner.resolve(u.name).to_string());
                }
                check_scope(&cl.body, &seed, fa, out);
            }
            ExprKind::ArrowFn(_) => {} // single-expr body can't contain compact() bindings worth checking; arrow captures all outer vars by value anyway
            _ => {}
        });
    }
}

fn param_names(params: &[Param], i: &Interner) -> HashSet<String> {
    params
        .iter()
        .map(|p| i.resolve(p.name).to_string())
        .collect()
}

/// If `e` is a call to the global `compact(...)`, return its arguments.
fn compact_args<'a>(e: &'a Expr, _fa: &FileAnalysis) -> Option<&'a [Arg]> {
    let ExprKind::Call { callee, args } = &e.kind else {
        return None;
    };
    let ExprKind::Name(n) = &callee.kind else {
        return None;
    };
    let last = n.text.rsplit('\\').next().unwrap_or(&n.text);
    (last.eq_ignore_ascii_case("compact")).then_some(args.as_slice())
}

/// Collect the constant-string variable names an argument denotes: a bare string
/// literal, or string literals nested in an array literal. Each with the span to
/// report at. Non-constant arguments yield nothing (we can't know the name).
fn constant_string_names(e: &Expr) -> Vec<(String, php_span::Span)> {
    let mut out = Vec::new();
    collect_const_strings(e, &mut out);
    out
}

fn collect_const_strings(e: &Expr, out: &mut Vec<(String, php_span::Span)>) {
    match &e.kind {
        ExprKind::Str(bytes) => {
            if let Ok(s) = std::str::from_utf8(bytes) {
                out.push((s.to_string(), e.span));
            }
        }
        ExprKind::Array { items, .. } => {
            for it in items {
                if let Some(v) = &it.value {
                    collect_const_strings(v, out);
                }
            }
        }
        _ => {}
    }
}

/// Whether `body` contains an escape-hatch construct in *this* scope (not
/// crossing into nested function-likes).
fn scope_has_escape(body: &[Stmt], _i: &Interner) -> bool {
    let mut found = false;
    for s in body {
        walk::for_each_expr_in_scope(s, &mut |e| {
            if found {
                return;
            }
            match &e.kind {
                ExprKind::VariableVariable(_)
                | ExprKind::DollarBrace(_)
                | ExprKind::Eval(_)
                | ExprKind::Include { .. } => found = true,
                ExprKind::Call { callee, .. } => {
                    if let ExprKind::Name(n) = &callee.kind {
                        let last = n
                            .text
                            .rsplit('\\')
                            .next()
                            .unwrap_or(&n.text)
                            .to_ascii_lowercase();
                        if ESCAPE_FUNCTIONS.contains(&last.as_str()) {
                            found = true;
                        }
                    }
                }
                _ => {}
            }
        });
    }
    found
}

/// Collect every variable name bound by statement `s` in this scope (assignments,
/// foreach bindings, catch vars, global/static, by-ref call args, list-destructure,
/// `&$x` array elements). Flow-insensitive: any binding on any path counts.
fn collect_bound(s: &Stmt, i: &Interner, bound: &mut HashSet<String>) {
    match &s.kind {
        StmtKind::Global(vars) | StmtKind::Unset(vars) => {
            for v in vars {
                if let ExprKind::Variable(sym) = &v.kind {
                    bound.insert(i.resolve(*sym).to_string());
                }
            }
        }
        StmtKind::StaticVars(vars) => {
            for sv in vars {
                bound.insert(i.resolve(sv.name).to_string());
            }
        }
        StmtKind::Foreach {
            key, value, body, ..
        } => {
            if let Some(k) = key {
                bind_target(k, i, bound);
            }
            bind_target(value, i, bound);
            collect_bound(body, i, bound);
        }
        StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for st in body {
                collect_bound(st, i, bound);
            }
            for c in catches {
                if let Some(v) = c.var {
                    bound.insert(i.resolve(v).to_string());
                }
                for st in &c.body {
                    collect_bound(st, i, bound);
                }
            }
            if let Some(f) = finally {
                for st in f {
                    collect_bound(st, i, bound);
                }
            }
        }
        StmtKind::Block(b) => b.iter().for_each(|st| collect_bound(st, i, bound)),
        StmtKind::If {
            then, elseifs, els, ..
        } => {
            collect_bound(then, i, bound);
            for ei in elseifs {
                collect_bound(&ei.body, i, bound);
            }
            if let Some(e) = els {
                collect_bound(e, i, bound);
            }
        }
        StmtKind::While { body, .. }
        | StmtKind::DoWhile { body, .. }
        | StmtKind::For { body, .. } => collect_bound(body, i, bound),
        StmtKind::Switch { cases, .. } => {
            for c in cases {
                for st in &c.body {
                    collect_bound(st, i, bound);
                }
            }
        }
        StmtKind::Namespace { body: Some(b), .. } => {
            b.iter().for_each(|st| collect_bound(st, i, bound))
        }
        StmtKind::Declare { body: Some(b), .. } => collect_bound(b, i, bound),
        // Don't descend into nested function/class scopes for *this* scope's binds.
        StmtKind::Function(_) | StmtKind::Class(_) => {}
        _ => {
            // Any other statement: scan its expressions (in this scope) for the
            // variables they assign/bind.
            walk::for_each_expr_in_scope(s, &mut |e| collect_bound_expr(e, i, bound));
        }
    }
}

/// Collect variables that expression `e` binds (assignment targets, by-ref args).
fn collect_bound_expr(e: &Expr, i: &Interner, bound: &mut HashSet<String>) {
    match &e.kind {
        ExprKind::Assign { target, .. }
        | ExprKind::AssignOp { target, .. }
        | ExprKind::AssignRef { target, .. } => bind_target(target, i, bound),
        ExprKind::PreInc(t) | ExprKind::PreDec(t) | ExprKind::PostInc(t) | ExprKind::PostDec(t) => {
            bind_target(t, i, bound)
        }
        // A bare `$var` passed to a call may be a by-ref out-parameter ⇒ defines it.
        ExprKind::Call { args, .. }
        | ExprKind::MethodCall { args, .. }
        | ExprKind::StaticCall { args, .. } => {
            for a in args {
                if let ExprKind::Variable(sym) = &a.value.kind {
                    bound.insert(i.resolve(*sym).to_string());
                }
            }
        }
        _ => {}
    }
}

/// Record the variables an assignment *target* introduces (`$x`, `[$a,$b]`,
/// `$arr[…]` base, `&$x` array elements).
fn bind_target(target: &Expr, i: &Interner, bound: &mut HashSet<String>) {
    match &target.kind {
        ExprKind::Variable(sym) => {
            bound.insert(i.resolve(*sym).to_string());
        }
        ExprKind::Array { items, .. } => {
            for it in items {
                if let Some(v) = &it.value {
                    bind_target(v, i, bound);
                }
            }
        }
        ExprKind::Index { base, .. } => bind_target(base, i, bound),
        _ => {}
    }
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "global.this",
        level: 0,
        run: run_this_in_global,
    },
    RuleEntry {
        name: "variable.undefined/compact",
        level: 0,
        run: run_compact_variables,
    },
    RuleEntry {
        name: "assign.byRefForeachExpr",
        level: 0,
        run: run_byref_foreach,
    },
    RuleEntry {
        name: "unset.variable/offset",
        level: 0,
        run: run_unset,
    },
    RuleEntry {
        name: "static.this",
        level: 0,
        run: run_this_in_static,
    },
    RuleEntry {
        name: "assign.this",
        level: 0,
        run: run_invalid_this_assign,
    },
    RuleEntry {
        name: "variable.undefined",
        level: 0,
        run: run_defined_variable,
    },
    RuleEntry {
        name: "variable.maybeUndefined",
        level: 1,
        run: run_maybe_undefined_variable,
    },
    RuleEntry {
        name: "isset",
        level: 1,
        run: run_isset,
    },
    RuleEntry {
        name: "empty",
        level: 1,
        run: run_empty,
    },
    RuleEntry {
        name: "nullCoalesce",
        level: 1,
        run: run_null_coalesce,
    },
    RuleEntry {
        name: "clone.nonObject",
        level: 3,
        run: run_variable_cloning,
    },
    RuleEntry {
        name: "parameterByRef.type",
        level: 3,
        run: run_parameter_out_assigned_type,
    },
    RuleEntry {
        name: "paramOut.type/executionEnd",
        level: 3,
        run: run_parameter_out_execution_end_type,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{codes, run};

    // --- variable.undefined ----------------------------------------------

    #[test]
    fn undefined_variable_is_flagged() {
        assert_eq!(
            codes("<?php function f() { return $x; }", run_defined_variable),
            ["variable.undefined"]
        );
    }

    #[test]
    fn assigned_variable_is_clean() {
        assert!(codes(
            "<?php function f() { $x = 1; return $x; }",
            run_defined_variable
        )
        .is_empty());
    }

    #[test]
    fn parameter_is_defined() {
        assert!(codes("<?php function f($x) { return $x; }", run_defined_variable).is_empty());
    }

    #[test]
    fn use_before_assign_is_flagged() {
        assert_eq!(
            codes(
                "<?php function f() { echo $x; $x = 1; }",
                run_defined_variable
            ),
            ["variable.undefined"]
        );
    }

    #[test]
    fn maybe_undefined_after_if() {
        // $x assigned only in the then-branch -> possibly undefined after.
        let src = "<?php function f($c) { if ($c) { $x = 1; } return $x; }";
        // Not a *definite* undefined, so the level-0 rule stays quiet...
        assert!(codes(src, run_defined_variable).is_empty());
        // ...but the level-1 maybe rule reports it.
        assert_eq!(
            codes(src, run_maybe_undefined_variable),
            ["variable.undefined"]
        );
    }

    #[test]
    fn defined_in_both_branches_is_clean() {
        let src = "<?php function f($c) { if ($c) { $x = 1; } else { $x = 2; } return $x; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn foreach_binding_is_defined_in_body() {
        let src = "<?php function f(array $a) { foreach ($a as $v) { echo $v; } }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn list_destructuring_defines() {
        let src = "<?php function f(array $a) { [$x, $y] = $a; return $x + $y; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn isset_guard_is_not_a_read() {
        let src = "<?php function f() { if (isset($x)) { return 1; } return 0; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn coalesce_left_is_not_a_read() {
        let src = "<?php function f() { return $x ?? 'default'; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn extract_bails_the_scope() {
        // extract() can define arbitrary variables -> no reports for this scope.
        let src = "<?php function f(array $a) { extract($a); return $x; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn byref_call_argument_is_not_flagged() {
        // preg_match defines $m by reference; don't flag the bare-variable arg.
        let src = "<?php function f() { preg_match('/x/', 'x', $m); return $m; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn superglobal_is_defined() {
        assert!(codes(
            "<?php function f() { return $_GET['x']; }",
            run_defined_variable
        )
        .is_empty());
    }

    #[test]
    fn global_statement_defines() {
        let src = "<?php function f() { global $config; return $config; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn catch_variable_is_defined() {
        let src = "<?php function f() { try { g(); } catch (\\Exception $e) { return $e; } return null; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    #[test]
    fn closure_use_is_defined_inside() {
        let src = "<?php function f() { $x = 1; return function () use ($x) { return $x; }; }";
        assert!(codes(src, run_defined_variable).is_empty());
    }

    // --- isset / empty / nullCoalesce ------------------------------------

    #[test]
    fn isset_never_defined_variable_is_flagged() {
        let src = "<?php function f() { return isset($x); }";
        let diags = run(src, run_isset);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["isset.variable"]
        );
        assert_eq!(diags[0].message, "Variable $x in isset() is never defined.");
    }

    #[test]
    fn isset_non_nullable_variable_is_flagged() {
        let src = "<?php function f() { $x = 1; return isset($x); }";
        let diags = run(src, run_isset);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["isset.variable"]
        );
        assert_eq!(
            diags[0].message,
            "Variable $x in isset() always exists and is not nullable."
        );
    }

    #[test]
    fn isset_nullable_variable_is_clean() {
        let src = "<?php function f(?int $x) { return isset($x); }";
        assert!(codes(src, run_isset).is_empty());
    }

    #[test]
    fn isset_session_is_clean() {
        let src = "<?php function f() { return isset($_SESSION); }";
        assert!(codes(src, run_isset).is_empty());
    }

    #[test]
    fn isset_missing_shape_offset_is_flagged() {
        let src = "<?php function f() { $a = ['a' => 1]; return isset($a['b']); }";
        assert_eq!(codes(src, run_isset), ["isset.offset"]);
    }

    #[test]
    fn isset_existing_non_nullable_shape_offset_is_flagged() {
        let src = "<?php function f() { $a = ['a' => 1]; return isset($a['a']); }";
        assert_eq!(codes(src, run_isset), ["isset.offset"]);
    }

    #[test]
    fn isset_dynamic_offset_is_clean() {
        let src = "<?php function f(string $k) { $a = ['a' => 1]; return isset($a[$k]); }";
        assert!(codes(src, run_isset).is_empty());
    }

    #[test]
    fn empty_never_defined_variable_is_flagged() {
        let src = "<?php function f() { return empty($x); }";
        assert_eq!(codes(src, run_empty), ["empty.variable"]);
    }

    #[test]
    fn empty_always_falsy_variable_is_flagged() {
        let src = "<?php function f() { $x = false; return empty($x); }";
        let diags = run(src, run_empty);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["empty.variable"]
        );
        assert_eq!(
            diags[0].message,
            "Variable $x in empty() always exists and is always falsy."
        );
    }

    #[test]
    fn empty_never_falsy_variable_is_flagged() {
        let src = "<?php function f() { $x = 1; return empty($x); }";
        let diags = run(src, run_empty);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["empty.variable"]
        );
        assert_eq!(
            diags[0].message,
            "Variable $x in empty() always exists and is not falsy."
        );
    }

    #[test]
    fn empty_maybe_falsy_variable_is_clean() {
        let src = "<?php function f(bool $x) { return empty($x); }";
        assert!(codes(src, run_empty).is_empty());
    }

    #[test]
    fn empty_missing_shape_offset_is_flagged() {
        let src = "<?php function f() { $a = ['a' => 1]; return empty($a['b']); }";
        assert_eq!(codes(src, run_empty), ["empty.offset"]);
    }

    #[test]
    fn null_coalesce_never_defined_variable_is_flagged() {
        let src = "<?php function f() { return $x ?? 1; }";
        let diags = run(src, run_null_coalesce);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["nullCoalesce.variable"]
        );
        assert_eq!(
            diags[0].message,
            "Variable $x on left side of ?? is never defined."
        );
    }

    #[test]
    fn null_coalesce_non_nullable_variable_is_flagged() {
        let src = "<?php function f() { $x = 1; return $x ?? 2; }";
        assert_eq!(codes(src, run_null_coalesce), ["nullCoalesce.variable"]);
    }

    #[test]
    fn null_coalesce_nullable_variable_is_clean() {
        let src = "<?php function f(?int $x) { return $x ?? 2; }";
        assert!(codes(src, run_null_coalesce).is_empty());
    }

    #[test]
    fn null_coalesce_assign_non_nullable_target_is_flagged() {
        let src = "<?php function f() { $x = 1; $x ??= 2; }";
        assert_eq!(codes(src, run_null_coalesce), ["nullCoalesce.variable"]);
    }

    #[test]
    fn null_coalesce_missing_shape_offset_is_flagged() {
        let src = "<?php function f() { $a = ['a' => 1]; return $a['b'] ?? 2; }";
        assert_eq!(codes(src, run_null_coalesce), ["nullCoalesce.offset"]);
    }

    #[test]
    fn isset_family_skips_escape_hatch_scope() {
        let src = "<?php function f(array $data) { extract($data); return isset($x) || empty($y) || ($z ?? false); }";
        assert!(codes(src, run_isset).is_empty());
        assert!(codes(src, run_empty).is_empty());
        assert!(codes(src, run_null_coalesce).is_empty());
    }

    // --- unset.variable / unset.offset -----------------------------------

    #[test]
    fn unset_never_defined_variable_is_flagged() {
        let src = "<?php function f() { unset($x); }";
        let diags = run(src, run_unset);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["unset.variable"]
        );
        assert_eq!(
            diags[0].message,
            "Call to function unset() contains undefined variable $x."
        );
    }

    #[test]
    fn unset_defined_variable_is_clean() {
        let src = "<?php function f() { $x = 1; unset($x); }";
        assert!(codes(src, run_unset).is_empty());
    }

    #[test]
    fn unset_missing_shape_offset_is_flagged() {
        let src = "<?php function f() { $a = ['a' => 1]; unset($a['b']); }";
        let diags = run(src, run_unset);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["unset.offset"]
        );
        assert_eq!(diags[0].message, "Cannot unset offset 'b' on array{a: 1}.");
    }

    #[test]
    fn unset_existing_shape_offset_is_clean() {
        let src = "<?php function f() { $a = ['a' => 1]; unset($a['a']); }";
        assert!(codes(src, run_unset).is_empty());
    }

    // --- variable.undefined/compact --------------------------------------

    #[test]
    fn compact_undefined_variable_is_flagged() {
        let src = "<?php function f() { $a = 1; return compact('a', 'b'); }";
        assert_eq!(codes(src, run_compact_variables), ["variable.undefined"]);
    }

    #[test]
    fn compact_all_defined_is_clean() {
        let src = "<?php function f() { $a = 1; $b = 2; return compact('a', 'b'); }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_parameter_is_defined() {
        let src = "<?php function f($a) { return compact('a'); }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_array_argument_is_checked() {
        let src = "<?php function f() { $a = 1; return compact(['a', 'b']); }";
        assert_eq!(codes(src, run_compact_variables), ["variable.undefined"]);
    }

    #[test]
    fn compact_superglobal_is_defined() {
        let src = "<?php function f() { return compact('_GET'); }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_with_extract_is_skipped() {
        // extract() can define arbitrary variables ⇒ scope skipped (no FP).
        let src = "<?php function f(array $d) { extract($d); return compact('whatever'); }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_non_constant_argument_is_ignored() {
        let src = "<?php function f(string $name) { return compact($name); }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_variable_bound_later_is_clean() {
        // Scope-granular: bound anywhere in the scope ⇒ not "never defined".
        let src = "<?php function f() { $r = compact('a'); $a = 1; return $r; }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_foreach_binding_is_defined() {
        let src = "<?php function f(array $xs) { foreach ($xs as $a) {} return compact('a'); }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    #[test]
    fn compact_in_method_uses_method_scope() {
        let src = "<?php class C { function m() { $a = 1; return compact('a', 'b'); } }";
        assert_eq!(codes(src, run_compact_variables), ["variable.undefined"]);
    }

    #[test]
    fn compact_in_closure_use_is_defined() {
        let src =
            "<?php function f() { $a = 1; return function () use ($a) { return compact('a'); }; }";
        assert!(codes(src, run_compact_variables).is_empty());
    }

    // --- assign.byRefForeachExpr -----------------------------------------

    #[test]
    fn assign_to_dangling_byref_foreach_var_is_flagged() {
        let src = "<?php function f(array $a) { foreach ($a as &$v) {} $v = 1; }";
        assert_eq!(codes(src, run_byref_foreach), ["assign.byRefForeachExpr"]);
    }

    #[test]
    fn unset_after_foreach_clears_it() {
        let src = "<?php function f(array $a) { foreach ($a as &$v) {} unset($v); $v = 1; }";
        assert!(codes(src, run_byref_foreach).is_empty());
    }

    #[test]
    fn byvalue_foreach_is_clean() {
        let src = "<?php function f(array $a) { foreach ($a as $v) {} $v = 1; }";
        assert!(codes(src, run_byref_foreach).is_empty());
    }

    #[test]
    fn assign_inside_foreach_body_is_clean() {
        let src = "<?php function f(array $a) { foreach ($a as &$v) { $v = 1; } }";
        assert!(codes(src, run_byref_foreach).is_empty());
    }

    #[test]
    fn sibling_branch_foreaches_do_not_leak() {
        // The php-parser NameResolver pattern: separate `foreach (… as &$x) { $x = … }`
        // in mutually-exclusive branches must not flag (each header rebinds $x).
        let src = "<?php function f($n, array $a, array $b) { \
            if ($n === 1) { foreach ($a as &$x) { $x = 1; } } \
            elseif ($n === 2) { foreach ($b as &$x) { $x = 2; } } }";
        assert!(codes(src, run_byref_foreach).is_empty());
    }

    #[test]
    fn reuse_of_byref_var_in_second_foreach_is_clean() {
        // A second `foreach (… as &$v)` rebinds $v; its in-body assign isn't dangling.
        let src = "<?php function f(array $a, array $b) { \
            foreach ($a as &$v) {} foreach ($b as &$v) { $v = 1; } }";
        assert!(codes(src, run_byref_foreach).is_empty());
    }

    // --- global.this -----------------------------------------------------

    #[test]
    fn global_this_is_flagged() {
        assert_eq!(
            codes("<?php function f() { global $this; }", run_this_in_global),
            ["global.this"]
        );
    }

    #[test]
    fn global_other_variable_is_clean() {
        assert!(codes("<?php function f() { global $x, $y; }", run_this_in_global).is_empty());
    }

    // --- static.this -----------------------------------------------------

    #[test]
    fn static_this_is_flagged() {
        assert_eq!(
            codes("<?php function f() { static $this; }", run_this_in_static),
            ["static.this"]
        );
    }

    #[test]
    fn static_other_variable_is_clean() {
        assert!(codes(
            "<?php function f() { static $count = 0; }",
            run_this_in_static
        )
        .is_empty());
    }

    // --- assign.this -----------------------------------------------------

    #[test]
    fn reassign_this_is_flagged() {
        let src = "<?php class C { function m() { $this = 1; } }";
        assert_eq!(codes(src, run_invalid_this_assign), ["assign.this"]);
    }

    #[test]
    fn compound_assign_this_is_flagged() {
        let src = "<?php class C { function m() { $this += 1; } }";
        assert_eq!(codes(src, run_invalid_this_assign), ["assign.this"]);
    }

    #[test]
    fn assign_other_variable_is_clean() {
        let src = "<?php class C { function m() { $x = 1; $this->p = 2; } }";
        assert!(codes(src, run_invalid_this_assign).is_empty());
    }

    #[test]
    fn reassign_this_in_array_access_class_is_clean() {
        let src = "<?php class C implements ArrayAccess { function m() { $this = 1; } }";
        assert!(codes(src, run_invalid_this_assign).is_empty());
    }

    #[test]
    fn assign_this_outside_class_is_flagged() {
        // Even at top level / in a plain function PHP rejects re-assigning $this.
        let src = "<?php function f() { $this = 1; }";
        assert_eq!(codes(src, run_invalid_this_assign), ["assign.this"]);
    }

    // --- clone.nonObject -------------------------------------------------

    #[test]
    fn clone_int_literal_is_flagged() {
        assert_eq!(
            codes("<?php clone 1;", run_variable_cloning),
            ["clone.nonObject"]
        );
    }

    #[test]
    fn clone_string_variable_is_flagged() {
        let src = "<?php $x = 'hello'; clone $x;";
        assert_eq!(codes(src, run_variable_cloning), ["clone.nonObject"]);
    }

    #[test]
    fn clone_object_is_clean() {
        let src = "<?php class C {} $x = new C(); clone $x;";
        assert!(codes(src, run_variable_cloning).is_empty());
    }

    #[test]
    fn clone_unknown_type_is_clean() {
        // No inferred type ⇒ mixed ⇒ lenient (no diagnostic).
        let src = "<?php function f($x) { clone $x; }";
        assert!(codes(src, run_variable_cloning).is_empty());
    }

    // --- parameterByRef.type -----------------------------------------------

    #[test]
    fn byref_parameter_assignment_wrong_native_type_is_flagged() {
        let src = "<?php function f(int &$out) { $out = 'x'; }";
        let diags = run(src, run_parameter_out_assigned_type);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["parameterByRef.type"]
        );
        assert_eq!(
            diags[0].message,
            "Parameter &$out by-ref type of function f() expects int, 'x' given."
        );
    }

    #[test]
    fn byref_parameter_assignment_matching_type_is_clean() {
        let src = "<?php function f(int &$out) { $out = 1; }";
        assert!(codes(src, run_parameter_out_assigned_type).is_empty());
    }

    #[test]
    fn non_byref_parameter_assignment_is_clean() {
        let src = "<?php function f(int $out) { $out = 'x'; }";
        assert!(codes(src, run_parameter_out_assigned_type).is_empty());
    }

    #[test]
    fn byref_variadic_parameter_assignment_is_deferred() {
        let src = "<?php function f(int &...$out) { $out = 'x'; }";
        assert!(codes(src, run_parameter_out_assigned_type).is_empty());
    }

    #[test]
    fn byref_method_parameter_assignment_wrong_type_is_flagged() {
        let src = "<?php class C { function m(string &$name) { $name = 1; } }";
        let diags = run(src, run_parameter_out_assigned_type);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["parameterByRef.type"]
        );
        assert_eq!(
            diags[0].message,
            "Parameter &$name by-ref type of method C::m() expects string, 1 given."
        );
    }

    #[test]
    fn byref_assignment_inside_closure_is_not_outer_function_assignment() {
        let src = "<?php function f(int &$out) { $cb = function () use (&$out) { $out = 'x'; }; }";
        assert!(codes(src, run_parameter_out_assigned_type).is_empty());
    }

    // --- paramOut.type (execution end) -------------------------------------

    #[test]
    fn param_out_execution_end_wrong_final_native_type_is_flagged() {
        let src = "<?php /** @param-out int $out */ function f(string &$out) {}";
        let diags = run(src, run_parameter_out_execution_end_type);
        assert_eq!(
            diags
                .iter()
                .map(|d| d.code.unwrap_or(""))
                .collect::<Vec<_>>(),
            ["paramOut.type"]
        );
        assert_eq!(
            diags[0].message,
            "Parameter &$out @param-out type of function f() expects int, string given."
        );
    }

    #[test]
    fn param_out_execution_end_matching_assignment_is_clean() {
        let src = "<?php /** @param-out int $out */ function f(string &$out) { $out = 1; }";
        assert!(codes(src, run_parameter_out_execution_end_type).is_empty());
    }

    #[test]
    fn param_out_execution_end_wrong_assignment_final_type_is_flagged() {
        let src = "<?php /** @param-out int $out */ function f(&$out) { $out = 'x'; }";
        let diags = run(src, run_parameter_out_execution_end_type);
        assert_eq!(
            codes(src, run_parameter_out_execution_end_type),
            ["paramOut.type"]
        );
        assert_eq!(
            diags[0].message,
            "Parameter &$out @param-out type of function f() expects int, 'x' given."
        );
    }

    #[test]
    fn param_out_execution_end_branch_is_deferred() {
        let src = "<?php /** @param-out string $out */ function f(?string &$out, bool $c) { if ($c) { $out = 'x'; } }";
        assert!(codes(src, run_parameter_out_execution_end_type).is_empty());
    }

    #[test]
    fn param_out_execution_end_private_method_is_flagged() {
        let src =
            "<?php class C { /** @param-out int $out */ private function m(string &$out) {} }";
        let diags = run(src, run_parameter_out_execution_end_type);
        assert_eq!(
            codes(src, run_parameter_out_execution_end_type),
            ["paramOut.type"]
        );
        assert_eq!(
            diags[0].message,
            "Parameter &$out @param-out type of method C::m() expects int, string given."
        );
    }

    #[test]
    fn param_out_execution_end_public_method_is_deferred() {
        let src = "<?php class C { /** @param-out int $out */ public function m(string &$out) {} }";
        assert!(codes(src, run_parameter_out_execution_end_type).is_empty());
    }

    #[test]
    fn param_out_execution_end_variadic_is_deferred() {
        let src = "<?php /** @param-out int $out */ function f(int &...$out) { $out = 'x'; }";
        assert!(codes(src, run_parameter_out_execution_end_type).is_empty());
    }
}
