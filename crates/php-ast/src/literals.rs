//! Shared PHP literal normalization helpers.

use crate::{BinOp, Expr, ExprKind};

pub enum ScalarStringValue<'a> {
    Str(&'a [u8]),
    Int(i64),
    Float(f64),
    Bool(bool),
    Null,
}

/// Whether `s` is a canonical integer string (it round-trips through i64): `0`
/// or `-?[1-9][0-9]*` within range. Used for array/interpolation integer keys.
pub fn canonical_int_key(s: &str) -> Option<i64> {
    let n: i64 = s.parse().ok()?;
    (n.to_string() == s).then_some(n)
}

/// Decode a `T_CONSTANT_ENCAPSED_STRING` lexeme (with quotes and optional `b`
/// prefix) to its byte-string value, applying single- or double-quote rules.
pub fn decode_string_literal(text: &str) -> Vec<u8> {
    let b = text.as_bytes();
    let body = if b.len() > 1 && (b[0] == b'b' || b[0] == b'B') && (b[1] == b'"' || b[1] == b'\'') {
        &text[1..]
    } else {
        text
    };
    let bb = body.as_bytes();
    if bb.len() < 2 {
        return Vec::new();
    }
    let inner = &body[1..body.len() - 1];
    if bb[0] == b'\'' {
        decode_single(inner)
    } else {
        decode_double(inner, Some(b'"'))
    }
}

/// Double-quoted / heredoc / backtick escape rules. PHP strings are byte
/// sequences, so escapes like `\xff`/`\377` yield raw bytes. `quote` is the
/// delimiter-specific escapable quote (`\"` in double-quotes, `` \` `` in
/// backticks, `None` in heredoc).
pub fn decode_double(s: &str, quote: Option<u8>) -> Vec<u8> {
    let b = s.as_bytes();
    let mut out = Vec::with_capacity(b.len());
    let mut i = 0;
    while i < b.len() {
        if b[i] != b'\\' {
            out.push(b[i]);
            i += 1;
            continue;
        }
        i += 1;
        if i >= b.len() {
            out.push(b'\\');
            break;
        }
        if Some(b[i]) == quote {
            out.push(b[i]);
            i += 1;
            continue;
        }
        match b[i] {
            b'n' => {
                out.push(b'\n');
                i += 1;
            }
            b't' => {
                out.push(b'\t');
                i += 1;
            }
            b'r' => {
                out.push(b'\r');
                i += 1;
            }
            b'v' => {
                out.push(0x0b);
                i += 1;
            }
            b'f' => {
                out.push(0x0c);
                i += 1;
            }
            b'e' => {
                out.push(0x1b);
                i += 1;
            }
            b'\\' => {
                out.push(b'\\');
                i += 1;
            }
            b'$' => {
                out.push(b'$');
                i += 1;
            }
            b'0'..=b'7' => {
                let mut val = 0u32;
                let mut n = 0;
                while n < 3 && i < b.len() && (b'0'..=b'7').contains(&b[i]) {
                    val = val * 8 + (b[i] - b'0') as u32;
                    i += 1;
                    n += 1;
                }
                out.push((val & 0xff) as u8);
            }
            b'x' if i + 1 < b.len() && b[i + 1].is_ascii_hexdigit() => {
                i += 1;
                let mut val = 0u32;
                let mut n = 0;
                while n < 2 && i < b.len() && b[i].is_ascii_hexdigit() {
                    val = val * 16 + (b[i] as char).to_digit(16).unwrap();
                    i += 1;
                    n += 1;
                }
                out.push((val & 0xff) as u8);
            }
            b'u' if i + 1 < b.len() && b[i + 1] == b'{' => {
                i += 2;
                let mut val = 0u32;
                while i < b.len() && b[i] != b'}' {
                    if let Some(d) = (b[i] as char).to_digit(16) {
                        val = val * 16 + d;
                    }
                    i += 1;
                }
                if i < b.len() {
                    i += 1;
                }
                if let Some(ch) = char::from_u32(val) {
                    let mut buf = [0u8; 4];
                    out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                }
            }
            _ => out.push(b'\\'),
        }
    }
    out
}

/// Post-process a heredoc/nowdoc body: remove the single trailing newline that
/// precedes the closing marker, then strip up to `indent` leading whitespace
/// characters from the start of every body line (PHP 7.3+ flexible syntax).
pub fn normalize_heredoc_parts(parts: &mut [Expr], indent: usize) {
    if let Some(last) = parts.last_mut() {
        if let ExprKind::Str(s) = &mut last.kind {
            if s.last() == Some(&b'\n') {
                s.pop();
                if s.last() == Some(&b'\r') {
                    s.pop();
                }
            }
        }
    }
    if indent == 0 {
        return;
    }
    let mut at_line_start = true;
    for p in parts.iter_mut() {
        match &mut p.kind {
            ExprKind::Str(s) => {
                if !s.is_empty() {
                    *s = dedent_line_starts(s, indent, at_line_start);
                    at_line_start = s.last() == Some(&b'\n');
                }
            }
            _ => at_line_start = false,
        }
    }
}

/// String form for PHP `.` concatenation.
pub fn scalar_to_string_bytes(value: ScalarStringValue<'_>) -> Vec<u8> {
    match value {
        ScalarStringValue::Str(bytes) => bytes.to_vec(),
        ScalarStringValue::Int(n) => n.to_string().into_bytes(),
        ScalarStringValue::Float(f) => runtime_float_to_string(f).into_bytes(),
        ScalarStringValue::Bool(true) => b"1".to_vec(),
        ScalarStringValue::Bool(false) | ScalarStringValue::Null => Vec::new(),
    }
}

/// Fold a constant-expression operand of `.` to its PHP byte-string value,
/// recursing through nested constant concatenations. This deliberately accepts
/// only literal strings, ints, floats, parenthesized values, and nested concat;
/// booleans/null/names are not folded by the Zend AST dumper path.
pub fn fold_scalar_concat_expr(e: &Expr) -> Option<Vec<u8>> {
    match &e.kind {
        ExprKind::Str(s) => Some(s.clone()),
        ExprKind::Int(i) => Some(scalar_to_string_bytes(ScalarStringValue::Int(*i))),
        ExprKind::Float(f) => Some(scalar_to_string_bytes(ScalarStringValue::Float(*f))),
        ExprKind::Binary {
            op: BinOp::Concat,
            lhs,
            rhs,
        } => {
            let mut a = fold_scalar_concat_expr(lhs)?;
            a.extend_from_slice(&fold_scalar_concat_expr(rhs)?);
            Some(a)
        }
        ExprKind::Paren(inner) => fold_scalar_concat_expr(inner),
        _ => None,
    }
}

/// PHP's runtime float→string conversion (precision 14, `%G`-style), used when a
/// float operand is converted for string concatenation.
pub fn runtime_float_to_string(f: f64) -> String {
    if f.is_nan() {
        return "NAN".into();
    }
    if f.is_infinite() {
        return if f > 0.0 { "INF".into() } else { "-INF".into() };
    }
    if f == 0.0 {
        return if f.is_sign_negative() {
            "-0".into()
        } else {
            "0".into()
        };
    }
    const P: i32 = 14;
    let sci = format!("{:.*E}", (P - 1) as usize, f);
    let epos = sci.find('E').unwrap();
    let exp: i32 = sci[epos + 1..].parse().unwrap();
    if (-4..P).contains(&exp) {
        let prec = (P - 1 - exp).max(0) as usize;
        let mut s = format!("{f:.prec$}");
        if s.contains('.') {
            while s.ends_with('0') {
                s.pop();
            }
            if s.ends_with('.') {
                s.pop();
            }
        }
        s
    } else {
        let mut mant = sci[..epos].to_string();
        if mant.contains('.') {
            while mant.ends_with('0') {
                mant.pop();
            }
            if mant.ends_with('.') {
                mant.pop();
            }
        }
        if !mant.contains('.') {
            mant.push_str(".0");
        }
        let sign = if exp < 0 { "-" } else { "+" };
        format!("{mant}E{sign}{}", exp.abs())
    }
}

fn decode_single(s: &str) -> Vec<u8> {
    let b = s.as_bytes();
    let mut out = Vec::with_capacity(b.len());
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'\\' && i + 1 < b.len() && (b[i + 1] == b'\\' || b[i + 1] == b'\'') {
            out.push(b[i + 1]);
            i += 2;
        } else {
            out.push(b[i]);
            i += 1;
        }
    }
    out
}

fn dedent_line_starts(s: &[u8], indent: usize, at_line_start: bool) -> Vec<u8> {
    let mut out = Vec::with_capacity(s.len());
    let mut skip = if at_line_start { indent } else { 0 };
    for &ch in s {
        if skip > 0 && (ch == b' ' || ch == b'\t') {
            skip -= 1;
            continue;
        }
        skip = 0;
        out.push(ch);
        if ch == b'\n' {
            skip = indent;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Expr, ExprKind};
    use php_span::Span;

    fn str_expr(bytes: &[u8]) -> Expr {
        Expr::new(Span::at(0), ExprKind::Str(bytes.to_vec()))
    }

    #[test]
    fn decodes_quoted_strings() {
        assert_eq!(decode_string_literal("'a\\\\b\\'c'"), b"a\\b'c");
        assert_eq!(decode_string_literal("\"a\\n\\x41\""), b"a\nA");
    }

    #[test]
    fn normalizes_heredoc_parts() {
        let mut parts = vec![str_expr(b"  a\n  b\n")];
        normalize_heredoc_parts(&mut parts, 2);
        assert_eq!(parts[0].kind, ExprKind::Str(b"a\nb".to_vec()));
    }

    #[test]
    fn folds_scalar_concat_expr() {
        let e = Expr::new(
            Span::at(0),
            ExprKind::Binary {
                op: BinOp::Concat,
                lhs: Box::new(str_expr(b"a")),
                rhs: Box::new(Expr::new(Span::at(0), ExprKind::Int(12))),
            },
        );
        assert_eq!(fold_scalar_concat_expr(&e), Some(b"a12".to_vec()));
    }
}
