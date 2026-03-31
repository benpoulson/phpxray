//! Cap #2: **constant-expression evaluation** (compile-time folding).
//!
//! A purely *syntactic* evaluator: it folds an expression built entirely from
//! literals and operators to a concrete [`ConstVal`], or returns `None` when the
//! value isn't a compile-time constant (a variable, a call, …). It deliberately
//! does **not** consult the type map or reflection — it only knows what the
//! source literally says — which keeps it sound and side-effect-free.
//!
//! Used by the constant-condition / constant-comparison rules
//! (`if (1 === 1)`, `5 > 3`, `'a' == 'b'`, …). To stay false-positive-safe the
//! folding is conservative: anything whose PHP semantics are subtle (mixed-type
//! loose `==`, string ordering, integer overflow) yields `None` rather than a
//! guess.

use php_ast::{BinOp, Expr, ExprKind, UnOp};

/// A folded compile-time value.
#[derive(Clone, Debug, PartialEq)]
pub enum ConstVal {
    Int(i64),
    Float(f64),
    Bool(bool),
    /// A byte string (PHP strings are byte arrays).
    Str(Vec<u8>),
    Null,
}

impl ConstVal {
    /// PHP truthiness of the value.
    pub fn truthy(&self) -> bool {
        match self {
            ConstVal::Int(n) => *n != 0,
            ConstVal::Float(f) => *f != 0.0,
            ConstVal::Bool(b) => *b,
            ConstVal::Null => false,
            ConstVal::Str(b) => !(b.is_empty() || b == b"0"),
        }
    }

    /// A phpstan `VerbosityLevel::value()`-style description for diagnostics.
    pub fn describe(&self) -> String {
        match self {
            ConstVal::Int(n) => n.to_string(),
            ConstVal::Float(f) => {
                // Render whole floats as `1.0` (php prints a trailing point).
                if f.fract() == 0.0 && f.is_finite() {
                    format!("{f:.1}")
                } else {
                    format!("{f}")
                }
            }
            ConstVal::Bool(b) => b.to_string(),
            ConstVal::Null => "null".to_string(),
            ConstVal::Str(b) => format!("'{}'", String::from_utf8_lossy(b)),
        }
    }
}

/// Evaluate `e` to a constant, or `None` if it isn't a compile-time constant.
pub fn eval_const(e: &Expr) -> Option<ConstVal> {
    use ConstVal::*;
    match &e.kind {
        ExprKind::Paren(inner) => eval_const(inner),
        ExprKind::Int(n) => Some(Int(*n)),
        ExprKind::Float(f) => Some(Float(*f)),
        ExprKind::Str(b) => Some(Str(b.clone())),
        ExprKind::Name(n) => match n.text.trim_start_matches('\\').to_ascii_lowercase().as_str() {
            "true" => Some(Bool(true)),
            "false" => Some(Bool(false)),
            "null" => Some(Null),
            _ => None,
        },
        ExprKind::Unary { op, expr } => eval_unary(*op, &eval_const(expr)?),
        ExprKind::Binary { op, lhs, rhs } => eval_binary(*op, lhs, rhs),
        _ => None,
    }
}

fn eval_unary(op: UnOp, v: &ConstVal) -> Option<ConstVal> {
    use ConstVal::*;
    Some(match (op, v) {
        (UnOp::Not, _) => Bool(!v.truthy()),
        (UnOp::Minus, Int(n)) => Int(n.checked_neg()?),
        (UnOp::Minus, Float(f)) => Float(-f),
        (UnOp::Plus, Int(n)) => Int(*n),
        (UnOp::Plus, Float(f)) => Float(*f),
        (UnOp::BitNot, Int(n)) => Int(!n),
        _ => return None,
    })
}

fn eval_binary(op: BinOp, lhs: &Expr, rhs: &Expr) -> Option<ConstVal> {
    use ConstVal::*;

    // Logical operators: both sides are constant here, but evaluate lazily so a
    // short-circuit doesn't require the other side to fold.
    match op {
        BinOp::BoolAnd | BinOp::LogicalAnd => {
            return Some(Bool(eval_const(lhs)?.truthy() && eval_const(rhs)?.truthy()));
        }
        BinOp::BoolOr | BinOp::LogicalOr => {
            return Some(Bool(eval_const(lhs)?.truthy() || eval_const(rhs)?.truthy()));
        }
        _ => {}
    }

    let l = eval_const(lhs)?;
    let r = eval_const(rhs)?;
    Some(match op {
        BinOp::Concat => Str([concat_bytes(&l), concat_bytes(&r)].concat()),
        BinOp::Identical => Bool(identical(&l, &r)),
        BinOp::NotIdentical => Bool(!identical(&l, &r)),
        BinOp::Eq => Bool(loose_eq(&l, &r)?),
        BinOp::NotEq => Bool(!loose_eq(&l, &r)?),
        BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => Bool(numeric_cmp(op, &l, &r)?),
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => arith(op, &l, &r)?,
        _ => return None, // Pow, bitwise, spaceship, pipe: not folded (yet).
    })
}

/// Strict (`===`) equality: same type *and* value. Int and Float are distinct
/// types, so `1 === 1.0` is `false`.
fn identical(l: &ConstVal, r: &ConstVal) -> bool {
    use ConstVal::*;
    match (l, r) {
        (Int(a), Int(b)) => a == b,
        (Float(a), Float(b)) => a == b,
        (Bool(a), Bool(b)) => a == b,
        (Str(a), Str(b)) => a == b,
        (Null, Null) => true,
        _ => false,
    }
}

/// Loose (`==`) equality — only the unambiguous same-category cases are folded
/// (mixed-type PHP 8 loose comparison is subtle, so we return `None` and don't
/// report). Numbers compare numerically (int↔float), strings byte-wise.
fn loose_eq(l: &ConstVal, r: &ConstVal) -> Option<bool> {
    use ConstVal::*;
    match (l, r) {
        (Int(_) | Float(_), Int(_) | Float(_)) => Some(as_f64(l)? == as_f64(r)?),
        (Str(a), Str(b)) => Some(a == b),
        (Bool(a), Bool(b)) => Some(a == b),
        (Null, Null) => Some(true),
        _ => None,
    }
}

/// `<`/`>`/`<=`/`>=` — only numeric operands are folded (string/array ordering
/// has PHP-specific rules we don't replicate here).
fn numeric_cmp(op: BinOp, l: &ConstVal, r: &ConstVal) -> Option<bool> {
    let a = as_f64(l)?;
    let b = as_f64(r)?;
    Some(match op {
        BinOp::Lt => a < b,
        BinOp::Gt => a > b,
        BinOp::LtEq => a <= b,
        BinOp::GtEq => a >= b,
        _ => return None,
    })
}

fn arith(op: BinOp, l: &ConstVal, r: &ConstVal) -> Option<ConstVal> {
    use ConstVal::*;
    if let (Int(a), Int(b)) = (l, r) {
        return Some(match op {
            BinOp::Add => Int(a.checked_add(*b)?),
            BinOp::Sub => Int(a.checked_sub(*b)?),
            BinOp::Mul => Int(a.checked_mul(*b)?),
            BinOp::Div => {
                if *b == 0 {
                    return None;
                } else if a % b == 0 {
                    Int(a / b)
                } else {
                    Float(*a as f64 / *b as f64)
                }
            }
            BinOp::Mod => {
                if *b == 0 {
                    return None;
                }
                Int(a % b)
            }
            _ => return None,
        });
    }
    // Mixed int/float -> float arithmetic.
    let a = as_f64(l)?;
    let b = as_f64(r)?;
    Some(match op {
        BinOp::Add => Float(a + b),
        BinOp::Sub => Float(a - b),
        BinOp::Mul => Float(a * b),
        BinOp::Div if b != 0.0 => Float(a / b),
        _ => return None,
    })
}

/// Numeric value of a constant, for numeric comparison/arithmetic.
fn as_f64(v: &ConstVal) -> Option<f64> {
    match v {
        ConstVal::Int(n) => Some(*n as f64),
        ConstVal::Float(f) => Some(*f),
        ConstVal::Bool(b) => Some(if *b { 1.0 } else { 0.0 }),
        _ => None,
    }
}

/// String form for `.` concatenation.
fn concat_bytes(v: &ConstVal) -> Vec<u8> {
    match v {
        ConstVal::Str(b) => b.clone(),
        ConstVal::Int(n) => n.to_string().into_bytes(),
        ConstVal::Float(f) => f.to_string().into_bytes(),
        ConstVal::Bool(true) => b"1".to_vec(),
        ConstVal::Bool(false) | ConstVal::Null => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn val(src: &str) -> Option<ConstVal> {
        let full = format!("<?php $x = ({src});");
        let r = php_parser::parse(&full);
        assert!(!r.has_errors(), "parse error: {src}");
        // The first expression statement's RHS.
        let stmt = r.program.stmts.first()?;
        let php_ast::StmtKind::Expr(e) = &stmt.kind else { return None };
        let ExprKind::Assign { rhs, .. } = &e.kind else { return None };
        eval_const(rhs)
    }

    #[test]
    fn folds_literals() {
        assert_eq!(val("1"), Some(ConstVal::Int(1)));
        assert_eq!(val("true"), Some(ConstVal::Bool(true)));
        assert_eq!(val("null"), Some(ConstVal::Null));
        assert_eq!(val("'a'"), Some(ConstVal::Str(b"a".to_vec())));
    }

    #[test]
    fn folds_arithmetic() {
        assert_eq!(val("1 + 2"), Some(ConstVal::Int(3)));
        assert_eq!(val("10 - 4 * 2"), Some(ConstVal::Int(2)));
        assert_eq!(val("7 % 3"), Some(ConstVal::Int(1)));
        assert_eq!(val("'a' . 'b'"), Some(ConstVal::Str(b"ab".to_vec())));
    }

    #[test]
    fn folds_strict_comparison() {
        assert_eq!(val("1 === 1"), Some(ConstVal::Bool(true)));
        assert_eq!(val("1 === 2"), Some(ConstVal::Bool(false)));
        assert_eq!(val("1 === 1.0"), Some(ConstVal::Bool(false))); // distinct types
        assert_eq!(val("'a' !== 'b'"), Some(ConstVal::Bool(true)));
    }

    #[test]
    fn folds_numeric_comparison() {
        assert_eq!(val("5 > 3"), Some(ConstVal::Bool(true)));
        assert_eq!(val("3 >= 3"), Some(ConstVal::Bool(true)));
        assert_eq!(val("2 < 1"), Some(ConstVal::Bool(false)));
    }

    #[test]
    fn folds_loose_same_category() {
        assert_eq!(val("1 == 1"), Some(ConstVal::Bool(true)));
        assert_eq!(val("'a' == 'b'"), Some(ConstVal::Bool(false)));
        // Mixed-type loose comparison is not folded (PHP 8 subtlety).
        assert_eq!(val("1 == '1'"), None);
    }

    #[test]
    fn folds_logical_and_not() {
        assert_eq!(val("true && false"), Some(ConstVal::Bool(false)));
        assert_eq!(val("!0"), Some(ConstVal::Bool(true)));
        assert_eq!(val("1 < 2 || 0"), Some(ConstVal::Bool(true)));
    }

    #[test]
    fn non_constant_is_none() {
        assert_eq!(val("$y"), None);
        assert_eq!(val("foo()"), None);
        assert_eq!(val("9223372036854775807 + 1"), None); // overflow -> not folded
    }
}
