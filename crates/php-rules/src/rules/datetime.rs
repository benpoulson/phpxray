//! Root-level phpstan rule: `DateTimeInstantiationRule`.
//!
//! PHPStan asks PHP's own `DateTime` parser about every constant-string first
//! constructor argument. We do not have PHP's date parser in-process, so this is
//! deliberately conservative: it only reports ISO-like date/time strings whose
//! PHP `DateTime::getLastErrors()['errors']` messages are stable and obvious.
//! Dynamic strings, plain `string`, non-UTF-8 strings, and unfamiliar formats are
//! left alone to keep the rule false-positive-safe.

use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{Arg, Expr, ExprKind, Stmt};
use php_diagnostics::Diagnostic;
use php_infer::{eval_const, ConstVal};
use php_resolve::{for_each_region, Resolution, Scope};
use php_types::Type;

pub(crate) static RULES: &[RuleEntry] = &[RuleEntry {
    name: "datetime.instantiation",
    level: 5,
    run: run_datetime_instantiation,
}];

fn run_datetime_instantiation(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        for stmt in region {
            collect_exprs_in_stmt(stmt, &mut |expr| {
                let ExprKind::New { class, args } = &expr.kind else {
                    return;
                };
                let Some((display, code)) = datetime_class(class, scope) else {
                    return;
                };
                let Some(arg) = first_datetime_arg(args, fa) else {
                    return;
                };

                for value in constant_strings(fa, &arg.value) {
                    for error in datetime_errors(&value) {
                        out.push(
                            Diagnostic::error(
                                arg.value.span,
                                format!(
                                    "Instantiating {display} with {value} produces an error: {error}"
                                ),
                            )
                            .with_code(code),
                        );
                    }
                }
            });
        }
    });
    out
}

fn collect_exprs_in_stmt(stmt: &Stmt, f: &mut impl FnMut(&Expr)) {
    walk::for_each_expr(
        &php_ast::Program {
            stmts: vec![stmt.clone()],
        },
        f,
    );
}

fn datetime_class(class: &Expr, scope: &Scope) -> Option<(&'static str, &'static str)> {
    let ExprKind::Name(name) = &class.kind else {
        return None;
    };
    let Resolution::Fqn(fqn) = scope.resolve_class(name) else {
        return None;
    };
    match fqn.trim_start_matches('\\').to_ascii_lowercase().as_str() {
        "datetime" => Some(("DateTime", "new.dateTime")),
        "datetimeimmutable" => Some(("DateTimeImmutable", "new.dateTimeImmutable")),
        _ => None,
    }
}

fn first_datetime_arg<'a>(args: &'a [Arg], fa: &FileAnalysis) -> Option<&'a Arg> {
    let arg = args.first()?;
    if arg.spread || arg.is_placeholder() {
        return None;
    }
    if let Some(name) = arg.name {
        if !fa.interner.resolve(name).eq_ignore_ascii_case("datetime") {
            return None;
        }
    }
    Some(arg)
}

fn constant_strings(fa: &FileAnalysis, expr: &Expr) -> Vec<String> {
    let mut out = Vec::new();
    collect_type_strings(&fa.type_of(expr), &mut out);
    if let Some(ConstVal::Str(bytes)) = eval_const(expr) {
        if let Ok(s) = String::from_utf8(bytes) {
            push_unique(&mut out, s);
        }
    }
    out
}

fn collect_type_strings(ty: &Type, out: &mut Vec<String>) {
    match ty {
        Type::LiteralString(s) => push_unique(out, s.to_string()),
        Type::Nullable(inner) => collect_type_strings(inner, out),
        Type::Union(parts) | Type::Intersection(parts) => {
            for part in parts.iter() {
                collect_type_strings(part, out);
            }
        }
        _ => {}
    }
}

fn push_unique(out: &mut Vec<String>, s: String) {
    if !out.iter().any(|seen| seen == &s) {
        out.push(s);
    }
}

fn datetime_errors(value: &str) -> Vec<&'static str> {
    let bytes = value.as_bytes();
    let Some((_, mut i)) = read_digits(bytes, 0, 4, 4) else {
        return Vec::new();
    };
    if byte(bytes, i) != Some(b'-') {
        return Vec::new();
    }
    i += 1;

    let Some((month, next)) = read_digits(bytes, i, 1, 2) else {
        return Vec::new();
    };
    i = next;
    if byte(bytes, i) != Some(b'-') {
        return Vec::new();
    }
    i += 1;

    let Some((day, next)) = read_digits(bytes, i, 1, 2) else {
        return Vec::new();
    };
    i = next;

    let mut out = Vec::new();
    if month > 12 || day > 31 {
        out.push("Unexpected character");
    }

    if let Some(sep @ (b'T' | b' ')) = byte(bytes, i) {
        read_time_errors(bytes, i + 1, sep, &mut out);
    }

    out
}

fn read_time_errors(bytes: &[u8], mut i: usize, sep: u8, out: &mut Vec<&'static str>) {
    let Some((hour, next)) = read_digits(bytes, i, 1, 2) else {
        return;
    };
    i = next;
    if byte(bytes, i) != Some(b':') {
        return;
    }
    i += 1;

    if hour > 24 {
        out.push(if sep == b'T' {
            "Double time specification"
        } else {
            "Unexpected character"
        });
    }

    let Some((minute, next)) = read_digits(bytes, i, 1, 2) else {
        return;
    };
    i = next;
    if minute > 59 {
        out.push("Double time specification");
    }
    if byte(bytes, i) != Some(b':') {
        return;
    }
    i += 1;

    let Some((second, _)) = read_digits(bytes, i, 1, 2) else {
        return;
    };
    if second > 60 {
        out.push("Unexpected character");
    }
}

fn read_digits(bytes: &[u8], start: usize, min: usize, max: usize) -> Option<(u32, usize)> {
    let mut value = 0u32;
    let mut i = start;
    let end = bytes.len().min(start + max);
    while i < end {
        let b = bytes[i];
        if !b.is_ascii_digit() {
            break;
        }
        value = value * 10 + u32::from(b - b'0');
        i += 1;
    }
    (i - start >= min).then_some((value, i))
}

fn byte(bytes: &[u8], i: usize) -> Option<u8> {
    bytes.get(i).copied()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{codes, run};

    #[test]
    fn invalid_datetime_month_reports_phpstan_message() {
        let diags = run(
            r#"<?php new \DateTime('2024-13-01');"#,
            run_datetime_instantiation,
        );
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, Some("new.dateTime"));
        assert_eq!(
            diags[0].message,
            "Instantiating DateTime with 2024-13-01 produces an error: Unexpected character"
        );
    }

    #[test]
    fn invalid_datetimeimmutable_time_reports_identifier() {
        let diags = run(
            r#"<?php new \DateTimeImmutable('2024-01-01T25:00:00');"#,
            run_datetime_instantiation,
        );
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, Some("new.dateTimeImmutable"));
        assert_eq!(
            diags[0].message,
            "Instantiating DateTimeImmutable with 2024-01-01T25:00:00 produces an error: Double time specification"
        );
    }

    #[test]
    fn warning_only_invalid_date_is_not_reported() {
        assert!(codes(
            r#"<?php new \DateTime('2024-02-30');"#,
            run_datetime_instantiation
        )
        .is_empty());
    }

    #[test]
    fn dynamic_string_is_not_reported() {
        assert!(codes(r#"<?php new \DateTime($s);"#, run_datetime_instantiation).is_empty());
    }

    #[test]
    fn constant_string_union_reports_each_bad_value() {
        let src = r#"<?php $s = rand(0, 1) ? '2024-13-01' : '2024-12-32'; new \DateTime($s);"#;
        assert_eq!(
            codes(src, run_datetime_instantiation),
            vec!["new.dateTime", "new.dateTime"]
        );
    }

    #[test]
    fn constant_concat_is_reported() {
        assert_eq!(
            codes(
                r#"<?php new \DateTime('2024-' . '13-01');"#,
                run_datetime_instantiation
            ),
            vec!["new.dateTime"]
        );
    }

    #[test]
    fn named_datetime_argument_is_reported() {
        assert_eq!(
            codes(
                r#"<?php new \DateTime(datetime: '2024-13-01');"#,
                run_datetime_instantiation
            ),
            vec!["new.dateTime"]
        );
    }

    #[test]
    fn other_named_first_argument_is_not_reported() {
        assert!(codes(
            r#"<?php new \DateTime(timezone: '2024-13-01');"#,
            run_datetime_instantiation
        )
        .is_empty());
    }

    #[test]
    fn imported_datetime_is_reported_inside_namespace() {
        let src = r#"<?php namespace App; use DateTime; new DateTime('2024-13-01');"#;
        assert_eq!(codes(src, run_datetime_instantiation), vec!["new.dateTime"]);
    }

    #[test]
    fn user_datetime_class_is_not_reported_inside_namespace() {
        let src = r#"<?php namespace App; class DateTime {} new DateTime('2024-13-01');"#;
        assert!(codes(src, run_datetime_instantiation).is_empty());
    }
}
