//! The shared diagnostic vocabulary.
//!
//! Every phase — lexer, parser, and later name-resolution, the type checker, and
//! the rules engine — emits the same [`Diagnostic`]. Keeping the type here, with
//! only a dependency on `php-span`, means no phase is coupled to a particular
//! rendering library. Rich terminal rendering (e.g. `miette`/`ariadne`) is done
//! at the CLI/test boundary by converting *from* this type.

use php_span::Span;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Severity {
    Error,
    Warning,
}

/// A secondary span with an explanatory note, e.g. "expected `;` here".
#[derive(Clone, Debug)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

impl Label {
    pub fn new(span: Span, message: impl Into<String>) -> Label {
        Label { span, message: message.into() }
    }
}

/// A single problem found in the source. The parser is error-recovering: it
/// pushes diagnostics and synthesizes error nodes rather than aborting.
#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub severity: Severity,
    /// Stable machine code (e.g. `"PHP0001"`), assigned as rules mature.
    pub code: Option<&'static str>,
    pub message: String,
    /// The primary location the diagnostic points at.
    pub primary: Span,
    pub labels: Vec<Label>,
}

impl Diagnostic {
    pub fn error(primary: Span, message: impl Into<String>) -> Diagnostic {
        Diagnostic {
            severity: Severity::Error,
            code: None,
            message: message.into(),
            primary,
            labels: Vec::new(),
        }
    }

    pub fn warning(primary: Span, message: impl Into<String>) -> Diagnostic {
        Diagnostic {
            severity: Severity::Warning,
            code: None,
            message: message.into(),
            primary,
            labels: Vec::new(),
        }
    }

    pub fn with_code(mut self, code: &'static str) -> Diagnostic {
        self.code = Some(code);
        self
    }

    pub fn with_label(mut self, label: Label) -> Diagnostic {
        self.labels.push(label);
        self
    }

    #[inline]
    pub fn is_error(&self) -> bool {
        self.severity == Severity::Error
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builder() {
        let d = Diagnostic::error(Span::new(3, 4), "unexpected token")
            .with_code("PHP0001")
            .with_label(Label::new(Span::new(0, 1), "started here"));
        assert!(d.is_error());
        assert_eq!(d.code, Some("PHP0001"));
        assert_eq!(d.labels.len(), 1);
        assert_eq!(d.primary, Span::new(3, 4));
    }
}
