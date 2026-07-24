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
        Label {
            span,
            message: message.into(),
        }
    }
}

/// Where a [`DocTagFix`]'s tag is written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FixAnchor {
    /// The declaration has no docblock: insert a new block at this byte offset
    /// (always the start of the declaration's first line).
    NewDocAt(u32),
    /// A docblock exists at exactly this byte range in the analyzed source:
    /// add the tag before its closing `*/`.
    ExistingDoc(Span),
}

/// Tag ordering inside a merged docblock: `@param` lines first, then
/// `@return`, then `@var` (the derived `Ord` encodes this).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum DocTagKind {
    Param,
    Return,
    Var,
}

/// A machine-applicable repair: one PHPDoc tag to add to a declaration's
/// docblock. Several fixes sharing an anchor merge into a single docblock.
#[derive(Clone, Debug)]
pub struct DocTagFix {
    pub anchor: FixAnchor,
    pub kind: DocTagKind,
    /// The tag line without framing, e.g. `@param string $name`,
    /// `@return int`, `@var array<int, string>`.
    pub tag: String,
    /// Verbatim leading whitespace of the declaration's first line.
    pub indent: String,
}

/// A machine-applicable repair: replace a byte range of the analyzed source
/// verbatim (an empty replacement deletes it). Used to rewrite or remove
/// *existing* text — a provably-wrong doc type, an unused closure capture.
/// Identical replacements from several findings dedup at application.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReplaceFix {
    pub span: Span,
    pub replacement: String,
}

/// A machine-applicable repair carried by a [`Diagnostic`].
#[derive(Clone, Debug)]
pub enum Fix {
    /// Add one PHPDoc tag (fixes sharing an anchor merge into one docblock).
    DocTag(DocTagFix),
    /// Replace/delete a byte range of the source.
    Replace(ReplaceFix),
}

impl From<DocTagFix> for Fix {
    fn from(f: DocTagFix) -> Fix {
        Fix::DocTag(f)
    }
}

impl From<ReplaceFix> for Fix {
    fn from(f: ReplaceFix) -> Fix {
        Fix::Replace(f)
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
    /// A machine-applicable repair, when the producing rule knows one.
    pub fix: Option<Fix>,
}

impl Diagnostic {
    pub fn error(primary: Span, message: impl Into<String>) -> Diagnostic {
        Diagnostic {
            severity: Severity::Error,
            code: None,
            message: message.into(),
            primary,
            labels: Vec::new(),
            fix: None,
        }
    }

    pub fn warning(primary: Span, message: impl Into<String>) -> Diagnostic {
        Diagnostic {
            severity: Severity::Warning,
            code: None,
            message: message.into(),
            primary,
            labels: Vec::new(),
            fix: None,
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

    pub fn with_fix(mut self, fix: impl Into<Fix>) -> Diagnostic {
        self.fix = Some(fix.into());
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
