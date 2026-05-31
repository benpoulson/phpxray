//! phpstan category **Cast** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Cast/` — 7 rule(s) at level(s) 0,2.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to `RULES`
//! (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented (level 0, purely syntactic):
//! - `cast.unset` — the `(unset)` cast (removed in PHP 8.0).
//! - `cast.void` — a `(void)` cast used inside an expression (only valid as a
//!   statement-level discard).
//! - `cast.deprecated` — non-standard `(integer)`/`(boolean)`/`(double)`/
//!   `(binary)` spellings deprecated in PHP 8.5.
//!
//! Implemented (level 2, type-based — `fa.type_of` + conservative classifiers;
//! flag only when the operand type can DEFINITELY not be coerced):
//! - `cast.int` / `cast.double` / `cast.string` (`InvalidCastRule`) — casting a
//!   value that can never become that scalar (e.g. `(int) []`, `(string) [1]`).
//!   `(bool)` is omitted: every PHP value is boolean-coercible, so it never errs.
//! - `echo.nonString` (`EchoRule`) — an `echo` argument that can never be a
//!   string (`echo []`).
//! - `print.nonString` (`PrintRule`) — likewise for `print`.
//! - `encapsedStringPart.nonString` (`InvalidPartOfEncapsedStringRule`) — an
//!   interpolated expression that can never be cast to string (`"{$arr}"`).
//!
use crate::{FileAnalysis, RuleEntry};
use php_ast::{CastKind, ExprKind, StmtKind};
use php_diagnostics::Diagnostic;
use php_types::Type;
use std::collections::HashSet;

/// `DeprecatedCastRule` (level 0): PHP 8.5 deprecates the long/non-standard
/// cast spellings. The AST normalizes the cast kind, so we recover the spelling
/// from the expression span's source prefix.
fn run_deprecated_cast(fa: &FileAnalysis) -> Vec<Diagnostic> {
    if !fa.php_version.at_least(80500) {
        return Vec::new();
    }

    let mut out = Vec::new();
    for cast in fa.facts.casts() {
        if !matches!(
            cast.kind,
            CastKind::Int | CastKind::Bool | CastKind::Float | CastKind::String
        ) {
            continue;
        }
        let Some((spelling, replacement)) =
            deprecated_cast_spelling(cast.expr.span.text(fa.source))
        else {
            continue;
        };
        out.push(
            Diagnostic::error(
                cast.expr.span,
                format!(
                    "Non-standard ({spelling}) cast is deprecated in PHP 8.5. Use ({replacement}) instead."
                ),
            )
            .with_code("cast.deprecated"),
        );
    }
    out
}

fn deprecated_cast_spelling(expr_src: &str) -> Option<(&'static str, &'static str)> {
    let close = expr_src.find(')')?;
    let token = &expr_src[..=close];
    let inner = token.strip_prefix('(')?.strip_suffix(')')?.trim();
    if inner.eq_ignore_ascii_case("integer") {
        Some(("integer", "int"))
    } else if inner.eq_ignore_ascii_case("boolean") {
        Some(("boolean", "bool"))
    } else if inner.eq_ignore_ascii_case("double") {
        Some(("double", "float"))
    } else if inner.eq_ignore_ascii_case("binary") {
        Some(("binary", "string"))
    } else {
        None
    }
}

/// `(unset)` cast — no longer supported since PHP 8.0.
fn run_unset_cast(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for cast in fa.facts.casts() {
        if matches!(cast.kind, CastKind::Unset) {
            out.push(
                Diagnostic::error(
                    cast.expr.span,
                    "The (unset) cast is no longer supported in PHP 8.0 and later.",
                )
                .with_code("cast.unset"),
            );
        }
    }
    out
}

/// `(void)` cast used within an expression. A `(void)` cast is only valid as a
/// statement-level discard (`(void) foo();`); anywhere else it's an error.
fn run_void_cast(fa: &FileAnalysis) -> Vec<Diagnostic> {
    // Collect void casts that ARE a statement expression (the allowed position).
    let mut allowed: HashSet<(u32, u32)> = HashSet::new();
    for s in fa.facts.statements() {
        if let StmtKind::Expr(e) = &s.kind {
            if let ExprKind::Cast {
                kind: CastKind::Void,
                ..
            } = &e.kind
            {
                let r = e.span.range();
                allowed.insert((r.start as u32, r.end as u32));
            }
        }
    }

    let mut out = Vec::new();
    for cast in fa.facts.casts() {
        if matches!(cast.kind, CastKind::Void) {
            let r = cast.expr.span.range();
            if !allowed.contains(&(r.start as u32, r.end as u32)) {
                out.push(
                    Diagnostic::error(
                        cast.expr.span,
                        "The (void) cast cannot be used within an expression.",
                    )
                    .with_code("cast.void"),
                );
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Conservative coercibility classifiers (zero false positives: only return
// `true` — "definitely cannot be coerced" — when every member of the type is
// certainly incompatible; `mixed`/objects/unknown/templates → `false`).
// ---------------------------------------------------------------------------

/// Array-like value kinds, which can never become an int/float/string scalar.
fn is_array_like(t: &Type) -> bool {
    matches!(
        t,
        Type::Array(_) | Type::Iterable(_) | Type::List(_) | Type::Shape { .. }
    )
}

/// `true` only if `t` can NEVER be cast to a string (arrays can't; objects
/// might via `__toString`, so they are not flagged).
fn never_string(t: &Type) -> bool {
    match t {
        _ if is_array_like(t) => true,
        Type::Int
        | Type::Float
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Null
        | Type::String
        | Type::LiteralInt(_)
        | Type::LiteralString(_) => false,
        Type::Union(parts) => !parts.is_empty() && parts.iter().all(never_string),
        Type::Nullable(inner) => never_string(inner),
        _ => false,
    }
}

/// `true` only if `t` can NEVER be cast to int/float (arrays can't; scalars,
/// strings, bool, null all coerce).
fn never_number(t: &Type) -> bool {
    match t {
        _ if is_array_like(t) => true,
        Type::Int
        | Type::Float
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Null
        | Type::String
        | Type::LiteralInt(_)
        | Type::LiteralString(_) => false,
        Type::Union(parts) => !parts.is_empty() && parts.iter().all(never_number),
        Type::Nullable(inner) => never_number(inner),
        _ => false,
    }
}

/// `InvalidCastRule` (level 2): casting a value to a scalar it can never become.
/// Only `(int)`/`(float)`/`(string)` are checked — `(bool)` always succeeds in
/// PHP, and `(array)`/`(object)` wrap any value.
fn run_invalid_cast(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for cast in fa.facts.casts() {
        // (name shown in phpstan's message, identifier suffix, coercibility test)
        let (name, ident, bad): (&str, &'static str, fn(&Type) -> bool) = match cast.kind {
            CastKind::Int => ("int", "cast.int", never_number),
            CastKind::Float => ("float", "cast.double", never_number),
            CastKind::String => ("string", "cast.string", never_string),
            _ => continue,
        };
        let t = fa.type_of(cast.inner);
        if bad(&t) {
            out.push(
                Diagnostic::error(cast.expr.span, format!("Cannot cast {t} to {name}."))
                    .with_code(ident),
            );
        }
    }
    out
}

/// `EchoRule` (level 2): an `echo` argument that can never be converted to a
/// string.
fn run_echo(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for echo in fa.facts.echoes() {
        for (i, ex) in echo.exprs.iter().enumerate() {
            let t = fa.type_of(ex);
            if never_string(&t) {
                out.push(
                    Diagnostic::error(
                        ex.span,
                        format!(
                            "Parameter #{} ({t}) of echo cannot be converted to string.",
                            i + 1
                        ),
                    )
                    .with_code("echo.nonString"),
                );
            }
        }
    }
    out
}

/// `PrintRule` (level 2): a `print` operand that can never be converted to a
/// string.
fn run_print(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for print in fa.facts.prints() {
        let t = fa.type_of(print.inner);
        if never_string(&t) {
            out.push(
                Diagnostic::error(
                    print.inner.span,
                    format!("Parameter {t} of print cannot be converted to string."),
                )
                .with_code("print.nonString"),
            );
        }
    }
    out
}

/// `InvalidPartOfEncapsedStringRule` (level 2): an interpolated expression that
/// can never be cast to string. The literal text runs (also `ExprKind::Str`
/// parts) are skipped — only the embedded *expressions* are checked.
fn run_invalid_encapsed_part(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for e in fa.facts.expressions() {
        let parts = match &e.kind {
            ExprKind::Interpolated(parts) | ExprKind::ShellExec(parts) => parts,
            _ => continue,
        };
        for part in parts {
            // Literal text runs are `Str`; they are always valid string parts.
            if matches!(part.kind, ExprKind::Str(_)) {
                continue;
            }
            let t = fa.type_of(part);
            if never_string(&t) {
                out.push(
                    Diagnostic::error(
                        part.span,
                        // phpstan prints the pretty-printed part expression; we
                        // approximate with a placeholder (our AST has no printer).
                        format!(
                            "Part expression ({t}) of encapsed string cannot be cast to string."
                        ),
                    )
                    .with_code("encapsedStringPart.nonString"),
                );
            }
        }
    }
    out
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "cast.deprecated",
        level: 0,
        run: run_deprecated_cast,
    },
    RuleEntry {
        name: "cast.unset",
        level: 0,
        run: run_unset_cast,
    },
    RuleEntry {
        name: "cast.void",
        level: 0,
        run: run_void_cast,
    },
    RuleEntry {
        name: "cast.invalid",
        level: 2,
        run: run_invalid_cast,
    },
    RuleEntry {
        name: "cast.echo",
        level: 2,
        run: run_echo,
    },
    RuleEntry {
        name: "cast.print",
        level: 2,
        run: run_print,
    },
    RuleEntry {
        name: "cast.encapsedPart",
        level: 2,
        run: run_invalid_encapsed_part,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::{codes, codes_version, run_version};

    #[test]
    fn deprecated_casts_are_flagged_on_php_85() {
        let php85 = crate::PhpVersion::parse("8.5").unwrap();
        let src = "<?php $a = (integer) $x; $b = (boolean) $x; $c = (double) $x; $d = (binary) $x;";
        assert_eq!(
            codes_version(src, run_deprecated_cast, php85),
            [
                "cast.deprecated",
                "cast.deprecated",
                "cast.deprecated",
                "cast.deprecated"
            ]
        );
    }

    #[test]
    fn deprecated_cast_message_matches_phpstan() {
        let php85 = crate::PhpVersion::parse("8.5").unwrap();
        let diagnostics = run_version("<?php $a = (integer) $x;", run_deprecated_cast, php85);
        assert_eq!(
            diagnostics[0].message,
            "Non-standard (integer) cast is deprecated in PHP 8.5. Use (int) instead."
        );
    }

    #[test]
    fn deprecated_casts_are_silent_before_php_85() {
        assert!(codes("<?php $a = (integer) $x;", run_deprecated_cast).is_empty());
    }

    #[test]
    fn canonical_casts_are_not_deprecated() {
        let php85 = crate::PhpVersion::parse("8.5").unwrap();
        let src = "<?php $a = (int) $x; $b = (bool) $x; $c = (float) $x; $d = (string) $x;";
        assert!(codes_version(src, run_deprecated_cast, php85).is_empty());
    }

    #[test]
    fn deprecated_cast_spelling_is_case_and_space_insensitive() {
        let php85 = crate::PhpVersion::parse("8.5").unwrap();
        let src = "<?php $a = ( INTEGER ) $x; $b = (\tBOOLEAN\t) $x;";
        assert_eq!(
            codes_version(src, run_deprecated_cast, php85),
            ["cast.deprecated", "cast.deprecated"]
        );
    }

    #[test]
    fn unset_cast_is_flagged() {
        assert_eq!(
            codes("<?php $x = (unset) $y;", run_unset_cast),
            ["cast.unset"]
        );
    }

    #[test]
    fn unset_cast_found_anywhere_in_the_tree() {
        // Nested inside a function body + an argument — the walker reaches it.
        let src = "<?php function f($a) { g((unset) $a); }";
        assert_eq!(codes(src, run_unset_cast), ["cast.unset"]);
    }

    #[test]
    fn other_casts_are_not_unset() {
        assert!(codes("<?php $x = (int) $y; $z = (string) $y;", run_unset_cast).is_empty());
    }

    #[test]
    fn void_cast_as_statement_is_allowed() {
        // A bare `(void) expr;` statement is the one valid position.
        assert!(codes("<?php (void) foo();", run_void_cast).is_empty());
    }

    #[test]
    fn void_cast_within_expression_is_flagged() {
        assert_eq!(
            codes("<?php $x = (void) foo();", run_void_cast),
            ["cast.void"]
        );
        assert_eq!(
            codes("<?php bar((void) foo());", run_void_cast),
            ["cast.void"]
        );
        assert_eq!(
            codes("<?php echo (void) foo();", run_void_cast),
            ["cast.void"]
        );
    }

    #[test]
    fn void_cast_statement_inside_a_function_is_allowed() {
        assert!(codes("<?php function f() { (void) foo(); }", run_void_cast).is_empty());
    }

    #[test]
    fn no_cast_no_diagnostics() {
        assert!(codes("<?php $x = 1 + 2; echo $x;", run_unset_cast).is_empty());
        assert!(codes("<?php $x = 1 + 2; echo $x;", run_void_cast).is_empty());
    }

    // --- InvalidCastRule ------------------------------------------------------

    #[test]
    fn cast_array_to_scalar_is_flagged() {
        assert_eq!(
            codes("<?php $x = (int) [];", run_invalid_cast),
            ["cast.int"]
        );
        assert_eq!(
            codes("<?php $x = (float) [1];", run_invalid_cast),
            ["cast.double"]
        );
        assert_eq!(
            codes("<?php $x = (string) [1, 2];", run_invalid_cast),
            ["cast.string"]
        );
    }

    #[test]
    fn cast_scalar_is_ok() {
        assert!(codes("<?php $x = (int) '5';", run_invalid_cast).is_empty());
        assert!(codes("<?php $x = (string) 42;", run_invalid_cast).is_empty());
        assert!(codes("<?php $x = (float) true;", run_invalid_cast).is_empty());
        // (array)/(bool)/(object) casts are never invalid.
        assert!(codes("<?php $x = (array) [];", run_invalid_cast).is_empty());
        assert!(codes("<?php $x = (bool) [];", run_invalid_cast).is_empty());
    }

    #[test]
    fn cast_of_unknown_is_not_flagged() {
        assert!(codes(
            "<?php function f($a) { return (int) $a; }",
            run_invalid_cast
        )
        .is_empty());
    }

    // --- EchoRule -------------------------------------------------------------

    #[test]
    fn echo_array_is_flagged() {
        assert_eq!(codes("<?php echo [];", run_echo), ["echo.nonString"]);
        // Position is reported per-argument.
        assert_eq!(codes("<?php echo 'a', [1];", run_echo), ["echo.nonString"]);
    }

    #[test]
    fn echo_string_or_number_is_ok() {
        assert!(codes("<?php echo 'a', 1, 2.0;", run_echo).is_empty());
    }

    #[test]
    fn echo_unknown_is_not_flagged() {
        assert!(codes("<?php function f($a) { echo $a; }", run_echo).is_empty());
    }

    // --- PrintRule ------------------------------------------------------------

    #[test]
    fn print_array_is_flagged() {
        assert_eq!(codes("<?php print [];", run_print), ["print.nonString"]);
    }

    #[test]
    fn print_string_is_ok() {
        assert!(codes("<?php print 'hi';", run_print).is_empty());
        assert!(codes("<?php function f($a) { print $a; }", run_print).is_empty());
    }

    // --- InvalidPartOfEncapsedStringRule --------------------------------------

    #[test]
    fn array_in_interpolation_is_flagged() {
        // `$a` is a known array, interpolated via `{$a}`.
        let src = "<?php $a = [1, 2]; $s = \"x {$a} y\";";
        assert_eq!(
            codes(src, run_invalid_encapsed_part),
            ["encapsedStringPart.nonString"]
        );
    }

    #[test]
    fn scalar_in_interpolation_is_ok() {
        let src = "<?php $a = 5; $s = \"x {$a} y\";";
        assert!(codes(src, run_invalid_encapsed_part).is_empty());
    }

    #[test]
    fn interpolation_of_unknown_is_not_flagged() {
        let src = "<?php function f($a) { return \"v {$a}\"; }";
        assert!(codes(src, run_invalid_encapsed_part).is_empty());
    }
}
