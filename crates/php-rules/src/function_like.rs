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

// ---------------------------------------------------------------------------
// Argument-type checking (phpstan's `FunctionCallParametersCheck`, type half)
// ---------------------------------------------------------------------------

/// A resolved callee, reduced to what argument checking actually needs.
///
/// The four call sites (function calls, method calls, and the callback-context
/// overlay's versions of each) differ only in how they *resolve* a callee and
/// where they read types from. The check itself is this one loop — it used to be
/// four copies that had already drifted apart in three ways: the built-in
/// overload guard existed on only two of them, method resolution was
/// generic-aware on one path and not the other, and the display name came from a
/// different source in each.
pub(crate) struct ResolvedCallable<'a> {
    /// How the callee is named in the message: `function strlen` or
    /// `method Foo::bar()`.
    pub(crate) label: String,
    pub(crate) params: &'a [php_reflect::ParamReflection],
    /// Whether the callee came from a curated built-in stub.
    pub(crate) builtin: bool,
}

impl<'a> ResolvedCallable<'a> {
    pub(crate) fn function(
        display: &str,
        params: &'a [php_reflect::ParamReflection],
        builtin: bool,
    ) -> Self {
        ResolvedCallable {
            label: format!("function {display}"),
            params,
            builtin,
        }
    }

    pub(crate) fn method(
        class: &str,
        method: &str,
        params: &'a [php_reflect::ParamReflection],
        builtin: bool,
    ) -> Self {
        ResolvedCallable {
            label: format!("method {}::{method}()", class.trim_start_matches('\\')),
            params,
            builtin,
        }
    }
}

/// Check each positional argument against its parameter.
///
/// `type_of` and `accepts` are supplied by the caller because the
/// callback-context pass reads through a contextual type-map overlay rather than
/// the file's own map.
pub(crate) fn check_call_args(
    args: &[php_ast::Arg],
    callee: &ResolvedCallable<'_>,
    type_of: &dyn Fn(&Expr) -> Type,
    accepts: &dyn Fn(&Expr, &Type, &Type) -> bool,
    out: &mut Vec<Diagnostic>,
) {
    // Built-in stubs carry only one signature, so a call with more positional
    // arguments than the stub declares (and no variadic) is an *overload* the
    // stub does not capture — `strtr($s, $from, $to)` vs `strtr(string, array)`.
    // The stub's parameter types cannot be trusted for such a call.
    if callee.builtin
        && !callee.params.iter().any(|p| p.variadic)
        && args.len() > callee.params.len()
    {
        return;
    }
    for (i, arg) in args.iter().enumerate() {
        let Some(param) = callee.params.get(i) else {
            break;
        };
        if param.variadic {
            break; // a variadic absorbs the rest; element types are checked elsewhere
        }
        if !accepts(&arg.value, &param.ty, &param.native_ty) {
            let given = type_of(&arg.value);
            out.push(
                Diagnostic::error(
                    arg.value.span,
                    format!(
                        "Parameter #{} ${} of {} expects {}, {given} given.",
                        i + 1,
                        param.name,
                        callee.label,
                        param.ty
                    ),
                )
                .with_code("argument.type"),
            );
        }
    }
}
