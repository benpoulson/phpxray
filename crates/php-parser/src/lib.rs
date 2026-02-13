//! The PHP parser: hand-written recursive descent with a Pratt expression
//! parser (the precedence table is transcribed from `zend_language_parser.y`).
//!
//! `parse` is **total**: it never panics and always returns a tree (with explicit
//! error nodes) plus diagnostics, so error recovery composes without changing
//! callers. M4 implements the statement skeleton and the full expression core;
//! declarations, control flow, closures, `match`, etc. arrive in M5–M8.

mod parser;

use php_ast::Program;
use php_diagnostics::Diagnostic;
use php_intern::Interner;

/// The outcome of parsing one source unit.
pub struct ParseResult {
    pub program: Program,
    pub diagnostics: Vec<Diagnostic>,
    /// Resolves the [`php_intern::Symbol`]s embedded in the AST.
    pub interner: Interner,
}

impl ParseResult {
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(Diagnostic::is_error)
    }
}

/// Parse PHP source into a [`Program`]. Total by contract: never panics.
pub fn parse(source: &str) -> ParseResult {
    parser::Parser::new(source).parse()
}
