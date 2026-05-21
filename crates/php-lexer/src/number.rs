//! PHP numeric literal decoding/classification.

/// Whether a non-negative integer literal overflows `i64::MAX`, accounting for
/// radix prefixes, legacy octal, and `_` digit separators.
pub fn int_literal_overflows_i64(text: &str) -> bool {
    let digits = integer_digits(text);
    match u128::from_str_radix(&digits.digits, digits.radix) {
        Ok(v) => v > i64::MAX as u128,
        Err(_) => true,
    }
}

pub fn parse_int_literal(text: &str) -> i64 {
    let digits = integer_digits(text);
    i128::from_str_radix(&digits.digits, digits.radix)
        .map(|v| v as i64)
        .unwrap_or(0)
}

pub fn parse_float_literal(text: &str) -> f64 {
    let cleaned = strip_separators(text);
    let lower = cleaned.to_ascii_lowercase();
    if let Some(h) = lower.strip_prefix("0x") {
        let mut v = 0f64;
        for c in h.bytes() {
            if let Some(d) = (c as char).to_digit(16) {
                v = v * 16.0 + d as f64;
            }
        }
        return v;
    }
    if let Some(b) = lower.strip_prefix("0b") {
        return radix_strtod_sub(b, 2.0);
    }
    if let Some(o) = lower.strip_prefix("0o") {
        return radix_strtod_sub(o, 8.0);
    }
    if lower.len() > 1
        && lower.starts_with('0')
        && lower.bytes().all(|b| (b'0'..=b'7').contains(&b))
    {
        return radix_strtod_sub(&lower[1..], 8.0);
    }
    cleaned.parse::<f64>().unwrap_or(0.0)
}

struct IntegerDigits {
    radix: u32,
    digits: String,
}

fn integer_digits(text: &str) -> IntegerDigits {
    let cleaned = strip_separators(text);
    let lower = cleaned.to_ascii_lowercase();
    if let Some(d) = lower.strip_prefix("0x") {
        IntegerDigits {
            radix: 16,
            digits: d.to_string(),
        }
    } else if let Some(d) = lower.strip_prefix("0b") {
        IntegerDigits {
            radix: 2,
            digits: d.to_string(),
        }
    } else if let Some(d) = lower.strip_prefix("0o") {
        IntegerDigits {
            radix: 8,
            digits: d.to_string(),
        }
    } else if cleaned.len() > 1
        && cleaned.starts_with('0')
        && cleaned.bytes().all(|b| (b'0'..=b'7').contains(&b))
    {
        IntegerDigits {
            radix: 8,
            digits: cleaned[1..].to_string(),
        }
    } else {
        IntegerDigits {
            radix: 10,
            digits: cleaned,
        }
    }
}

fn strip_separators(text: &str) -> String {
    text.chars().filter(|&c| c != '_').collect()
}

/// Accumulate base-2/base-8 digits exactly as PHP's `zend_{bin,oct}_strtod`:
/// `value = value*base + c - '0'`. The floating-point operation order matters.
fn radix_strtod_sub(digits: &str, base: f64) -> f64 {
    let mut v = 0f64;
    for c in digits.bytes() {
        v = v * base + c as f64 - 48.0;
    }
    v
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_radix_and_separator_ints() {
        assert_eq!(parse_int_literal("1_000"), 1000);
        assert_eq!(parse_int_literal("0xff"), 255);
        assert_eq!(parse_int_literal("0b1010"), 10);
        assert_eq!(parse_int_literal("0o10"), 8);
        assert_eq!(parse_int_literal("010"), 8);
    }

    #[test]
    fn classifies_i64_overflow_as_float_token() {
        assert!(!int_literal_overflows_i64("9223372036854775807"));
        assert!(int_literal_overflows_i64("9223372036854775808"));
        assert!(int_literal_overflows_i64("0xffffffffffffffff"));
    }

    #[test]
    fn decodes_overflowed_legacy_octal_as_octal_float() {
        assert_eq!(parse_float_literal("010"), 8.0);
        assert_eq!(parse_float_literal("0_1_0"), 8.0);
    }
}
