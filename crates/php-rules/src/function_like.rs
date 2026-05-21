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

pub(crate) fn return_value_assignable(
    index: &ReflectionIndex,
    actual: &Type,
    declared: &Type,
    check_nullables: bool,
) -> bool {
    let checked = lenient_return_value(actual, check_nullables);
    php_infer::is_assignable(index, &checked, declared)
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
