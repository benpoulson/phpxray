//! The PHP lexer.
//!
//! Hand-written and stateful: PHP's tokenizer is a state machine with 11 start
//! conditions and a state stack (HTML vs scripting, string-interpolation
//! contexts, heredoc/nowdoc, the post-`->` property context, etc.), plus
//! lexer→parser feedback (the `&` token split, context-sensitive keywords).
//!
//! The implementation covers the scripting core, interpolation/heredoc states,
//! contextual tokens, and the PHP-compatible numeric classification path.
//!
//! [`golden`] is the golden-token test harness used to assert byte-for-byte
//! parity against PHP's own `token_get_all()` output.

mod lexer;
pub mod number;
mod token;

pub mod golden;

pub use lexer::tokenize;
pub use token::{Kw, Token, TokenKind};

#[cfg(test)]
mod tests {
    use super::*;

    /// Names map to the canonical PHP token names the golden harness compares to.
    #[test]
    fn token_names_match_php() {
        assert_eq!(TokenKind::Variable.php_name(), Some("T_VARIABLE"));
        assert_eq!(TokenKind::DoubleColon.php_name(), Some("T_DOUBLE_COLON"));
        assert_eq!(TokenKind::Eq.php_name(), Some("="));
        assert_eq!(
            TokenKind::Keyword(Kw::Function).php_name(),
            Some("T_FUNCTION")
        );
        assert_eq!(TokenKind::Eof.php_name(), None);
    }

    fn names(src: &str) -> Vec<&'static str> {
        let (toks, _) = tokenize(src);
        toks.iter().filter_map(|t| t.kind.php_name()).collect()
    }

    #[test]
    fn keywords_are_case_insensitive() {
        assert_eq!(
            names("<?php FUNCTION Foo"),
            ["T_OPEN_TAG", "T_FUNCTION", "T_STRING"]
        );
    }

    #[test]
    fn int_type_is_identifier_not_keyword() {
        // `int` is not a reserved keyword in PHP — it is a plain T_STRING.
        assert_eq!(names("<?php int"), ["T_OPEN_TAG", "T_STRING"]);
    }

    #[test]
    fn lexer_diagnostics_have_stable_codes() {
        let (_, diags) = tokenize("<?php /*");
        assert_eq!(
            diags.first().and_then(|d| d.code),
            Some("lexer.unterminatedComment")
        );

        let (_, diags) = tokenize("<?php \"");
        assert_eq!(
            diags.first().and_then(|d| d.code),
            Some("lexer.unterminatedString")
        );

        let (_, diags) = tokenize("<?php \x01");
        assert_eq!(
            diags.first().and_then(|d| d.code),
            Some("lexer.unexpectedCharacter")
        );
    }
}
