//! Shared return-checking primitives for function-like rules.

use crate::decls;
use php_ast::{Expr, Stmt};
use php_diagnostics::Diagnostic;
use php_reflect::ReflectionIndex;
use php_types::Type;

pub(crate) fn collect_returns<'a>(body: &'a [Stmt], mut f: impl FnMut(Option<&'a Expr>)) {
    decls::collect_returns_in_body(body, &mut f);
}

pub(crate) fn lenient_return_value(actual: &Type, check_nullables: bool) -> Type {
    if check_nullables {
        actual.clone()
    } else {
        php_infer::strip_null_lenient(actual)
    }
}

pub(crate) fn type_mismatch_reportable(
    index: &ReflectionIndex,
    actual: &Type,
    declared: &Type,
    check_nullables: bool,
    report_maybes: bool,
) -> bool {
    let checked = lenient_return_value(actual, check_nullables);
    match php_infer::assignable_trinary(index, &checked, declared) {
        php_infer::Trinary::Yes => false,
        php_infer::Trinary::No => true,
        php_infer::Trinary::Maybe => {
            report_maybes && maybe_is_reportable(&checked) && maybe_is_reportable(declared)
        }
    }
}

fn maybe_is_reportable(t: &Type) -> bool {
    use Type::*;
    match t {
        Mixed | ExplicitMixed | Unknown(_) | TemplateVar(_) | Conditional { .. } => false,
        Nullable(inner) => maybe_is_reportable(inner),
        Union(parts) | Intersection(parts) => parts.iter().all(maybe_is_reportable),
        Array(Some(kv)) | Iterable(Some(kv)) => {
            maybe_is_reportable(&kv.0) && maybe_is_reportable(&kv.1)
        }
        List(inner) | ClassString(Some(inner)) => maybe_is_reportable(inner),
        Callable(Some(sig)) => {
            sig.params.iter().all(maybe_is_reportable) && maybe_is_reportable(&sig.ret)
        }
        Named { args, .. } => args.iter().all(maybe_is_reportable),
        Shape { fields, .. } => fields.iter().all(|f| maybe_is_reportable(&f.ty)),
        _ => true,
    }
}

pub(crate) fn push_return_type_error(
    out: &mut Vec<Diagnostic>,
    expr: &Expr,
    label: &str,
    declared: &Type,
    actual: &Type,
) {
    out.push(
        Diagnostic::error(
            expr.span,
            format!("{label} should return {declared} but returns {actual}"),
        )
        .with_code("return.type"),
    );
}

// ---------------------------------------------------------------------------
// Call-arity vocabulary (phpstan's `FunctionCallParametersCheck`)
// ---------------------------------------------------------------------------

/// phpstan's shared "invoked with" phrase, identical for functions, methods,
/// static methods, constructors and callables (see
/// `CallToFunctionParametersRule` / `CallMethodsRule`, which pass the same six
/// message templates into `FunctionCallParametersCheck`).
///
/// Only "parameter" is pluralized — "required" never is. The arity half is
/// `N required` (fixed arity), `at least N required` (variadic), or
/// `R-M required` (some parameters optional).
pub(crate) fn invoked_with(supplied: usize, required: usize, max: usize, variadic: bool) -> String {
    let unit = if supplied == 1 {
        "parameter"
    } else {
        "parameters"
    };
    let arity = if variadic {
        format!("at least {required}")
    } else if required == max {
        format!("{max}")
    } else {
        format!("{required}-{max}")
    };
    format!("invoked with {supplied} {unit}, {arity} required")
}

/// Whether a function-like body reads its arguments dynamically via
/// `func_get_args`, `func_num_args`, or `func_get_arg`. Such a callee
/// legitimately accepts more positional arguments than its declared arity (the
/// Laravel `Rule::in()` idiom: `in($values)` collects extras with
/// `func_get_args()`), so "too many arguments" must not be reported.
///
/// Only consulted when a call already exceeds the declared maximum, so the body
/// scan stays off the hot path.
pub(crate) fn body_reads_variadic_args(body: &[Stmt]) -> bool {
    let prog = php_ast::Program {
        stmts: body.to_vec(),
    };
    let mut found = false;
    php_ast::walk::for_each_expr(&prog, &mut |e| {
        let php_ast::ExprKind::Call { callee, .. } = &e.kind else {
            return;
        };
        let php_ast::ExprKind::Name(n) = &callee.kind else {
            return;
        };
        let name = n.text.trim_start_matches('\\');
        found |= name.eq_ignore_ascii_case("func_get_args")
            || name.eq_ignore_ascii_case("func_num_args")
            || name.eq_ignore_ascii_case("func_get_arg");
    });
    found
}
