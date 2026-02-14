//! The hand-written PHP scanner.
//!
//! Start conditions implemented (mirroring `zend_language_scanner.l`):
//!   * `Initial`            — outside PHP: inline HTML + `<?php` / `<?=` / `<?`.
//!   * `Scripting`          — normal PHP code.
//!   * `LookingForProperty` — after `->` / `?->`: the next label is a property
//!     name (so keywords like `class` lex as `T_STRING`).
//!   * `DoubleQuotes` / `Backquote` — interpolated `"..."` and `` `...` ``.
//!   * `LookingForVarname`  — after `${` inside a string.
//!   * `VarOffset`          — inside `$a[...]` inside a string.
//!   * `Heredoc`            — heredoc/nowdoc bodies.
//!
//! Brace tracking matches PHP exactly: every `{` in scripting pushes a scripting
//! state and every `}` pops one, which is how `"{$expr}"` returns to the string
//! state at its closing brace.
//!
//! Whitespace and ordinary comments are skipped; `/** */` doc-comments, open/close
//! tags, inline HTML and the interpolation tokens are emitted for `token_get_all`
//! parity.

use php_diagnostics::Diagnostic;
use php_span::Span;

use crate::token::{Kw, Token, TokenKind};

#[derive(Clone)]
struct HeredocCtx {
    label: String,
    nowdoc: bool,
}

#[derive(Clone)]
enum State {
    Initial,
    Scripting,
    LookingForProperty,
    DoubleQuotes,
    Backquote,
    LookingForVarname,
    VarOffset,
    Heredoc(HeredocCtx),
}

/// Tokenize PHP source. Total: never panics; returns the token stream (always
/// ending in [`TokenKind::Eof`]) plus any diagnostics.
pub fn tokenize(source: &str) -> (Vec<Token>, Vec<Diagnostic>) {
    Lexer::new(source).run()
}

struct Lexer<'a> {
    text: &'a str,
    bytes: &'a [u8],
    pos: usize,
    tokens: Vec<Token>,
    diags: Vec<Diagnostic>,
    states: Vec<State>,
    /// Set when `__halt_compiler` was seen; the next `;` ends lexing and dumps
    /// the remainder of the file as a single `T_INLINE_HTML`.
    halt_seen: bool,
}

#[inline]
fn is_label_start(b: u8) -> bool {
    b == b'_' || b.is_ascii_alphabetic() || b >= 0x80
}

#[inline]
fn is_label_cont(b: u8) -> bool {
    is_label_start(b) || b.is_ascii_digit()
}

#[inline]
fn is_ws(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\r' | b'\n')
}

impl<'a> Lexer<'a> {
    fn new(source: &'a str) -> Lexer<'a> {
        Lexer {
            text: source,
            bytes: source.as_bytes(),
            pos: 0,
            tokens: Vec::new(),
            diags: Vec::new(),
            states: vec![State::Initial],
            halt_seen: false,
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.bytes.len()
    }

    /// The byte `offset` positions ahead of the cursor, or 0 past the end.
    #[inline]
    fn at(&self, offset: usize) -> u8 {
        self.bytes.get(self.pos + offset).copied().unwrap_or(0)
    }

    #[inline]
    fn set_state(&mut self, s: State) {
        *self.states.last_mut().expect("non-empty state stack") = s;
    }

    #[inline]
    fn push(&mut self, kind: TokenKind, start: usize) {
        self.tokens.push(Token::new(kind, Span::from_range(start..self.pos)));
    }

    fn run(mut self) -> (Vec<Token>, Vec<Diagnostic>) {
        while self.pos < self.len() {
            let state = self.states.last().expect("non-empty state stack").clone();
            match state {
                State::Initial => self.initial_step(),
                State::Scripting => self.scripting_step(),
                State::LookingForProperty => self.looking_for_property_step(),
                State::DoubleQuotes => self.string_body_step(b'"', TokenKind::DoubleQuote),
                State::Backquote => self.string_body_step(b'`', TokenKind::Backtick),
                State::LookingForVarname => self.looking_for_varname_step(),
                State::VarOffset => self.var_offset_step(),
                State::Heredoc(ctx) => self.heredoc_step(&ctx),
            }
        }
        self.tokens.push(Token::new(TokenKind::Eof, Span::at(self.pos as u32)));
        (self.tokens, self.diags)
    }

    // --- INITIAL: inline HTML + open tags ---------------------------------

    fn initial_step(&mut self) {
        let start = self.pos;
        while self.pos < self.len() && !(self.at(0) == b'<' && self.at(1) == b'?') {
            self.pos += 1;
        }
        if self.pos > start {
            self.push(TokenKind::InlineHtml, start);
        }
        if self.pos >= self.len() {
            return;
        }

        let tag_start = self.pos;
        if self.at(2) == b'=' {
            self.pos += 3; // <?=
            self.push(TokenKind::OpenTagEcho, tag_start);
        } else if self.starts_with_ci(b"<?php") {
            self.pos += 5;
            self.consume_one_trailing_ws();
            self.push(TokenKind::OpenTag, tag_start);
        } else {
            self.pos += 2; // short <?
            self.push(TokenKind::OpenTag, tag_start);
        }
        self.set_state(State::Scripting);
    }

    fn starts_with_ci(&self, needle: &[u8]) -> bool {
        let end = self.pos + needle.len();
        end <= self.len() && self.bytes[self.pos..end].eq_ignore_ascii_case(needle)
    }

    fn consume_one_trailing_ws(&mut self) {
        if self.at(0) == b'\r' && self.at(1) == b'\n' {
            self.pos += 2;
        } else if is_ws(self.at(0)) {
            self.pos += 1;
        }
    }

    // --- ST_IN_SCRIPTING --------------------------------------------------

    fn scripting_step(&mut self) {
        let c = self.at(0);

        if is_ws(c) {
            self.pos += 1;
            return;
        }

        // Close tag `?>` (+ one optional trailing newline) returns to INITIAL.
        if c == b'?' && self.at(1) == b'>' {
            let start = self.pos;
            self.pos += 2;
            if self.at(0) == b'\r' && self.at(1) == b'\n' {
                self.pos += 2;
            } else if matches!(self.at(0), b'\r' | b'\n') {
                self.pos += 1;
            }
            self.push(TokenKind::CloseTag, start);
            self.set_state(State::Initial);
            return;
        }

        // Comments.
        if c == b'/' && self.at(1) == b'/' {
            self.skip_line_comment();
            return;
        }
        if c == b'#' {
            if self.at(1) == b'[' {
                let start = self.pos;
                self.pos += 2;
                self.push(TokenKind::Attribute, start);
            } else {
                self.skip_line_comment();
            }
            return;
        }
        if c == b'/' && self.at(1) == b'*' {
            self.lex_block_comment();
            return;
        }

        // Heredoc / nowdoc start (`<<<`, or `b<<<`) — before the `<<` shift
        // operator, and only when a valid label + newline actually follows
        // (otherwise `<<<` is just `<<` then `<`).
        let lt = if c == b'<' && self.at(1) == b'<' && self.at(2) == b'<' {
            Some(self.pos)
        } else if matches!(c, b'b' | b'B')
            && self.at(1) == b'<'
            && self.at(2) == b'<'
            && self.at(3) == b'<'
        {
            Some(self.pos + 1)
        } else {
            None
        };
        if let Some(lt) = lt {
            if self.heredoc_valid_at(lt) {
                self.lex_heredoc_start();
                return;
            }
        }

        // Numbers (incl. a leading-dot float like `.5`).
        if c.is_ascii_digit() || (c == b'.' && self.at(1).is_ascii_digit()) {
            let start = self.pos;
            let kind = self.lex_number();
            self.push(kind, start);
            return;
        }

        // Variable `$name` (a lone `$` is its own token).
        if c == b'$' {
            let start = self.pos;
            if is_label_start(self.at(1)) {
                self.pos += 1;
                self.consume_label();
                self.push(TokenKind::Variable, start);
            } else {
                self.pos += 1;
                self.push(TokenKind::Dollar, start);
            }
            return;
        }

        // Binary-string prefix on a non-interpolated literal: `b"..."` / `b'...'`.
        if (c == b'b' || c == b'B') && matches!(self.at(1), b'"' | b'\'') {
            let q = self.at(1);
            if q == b'\'' || !self.double_quoted_interpolated(self.pos + 1) {
                let start = self.pos;
                self.pos += 1; // prefix; cursor now on the quote
                self.lex_string(start);
                return;
            }
            // Interpolated `b"..."` is rare; fall through and let `b` lex as a name.
        }

        // String literals.
        if c == b'\'' {
            let start = self.pos;
            self.lex_string(start);
            return;
        }
        if c == b'"' {
            if self.double_quoted_interpolated(self.pos) {
                let start = self.pos;
                self.pos += 1;
                self.push(TokenKind::DoubleQuote, start);
                self.states.push(State::DoubleQuotes);
            } else {
                let start = self.pos;
                self.lex_string(start);
            }
            return;
        }
        if c == b'`' {
            let start = self.pos;
            self.pos += 1;
            self.push(TokenKind::Backtick, start);
            self.states.push(State::Backquote);
            return;
        }

        // `&` is split so the parser can tell by-ref from intersection types.
        if c == b'&' {
            let start = self.pos;
            let kind = if self.at(1) == b'&' {
                self.pos += 2;
                TokenKind::BoolAnd
            } else if self.at(1) == b'=' {
                self.pos += 2;
                TokenKind::AndEq
            } else {
                self.pos += 1;
                if self.amp_followed_by_var_or_vararg() {
                    TokenKind::AmpFollowedByVar
                } else {
                    TokenKind::AmpNotFollowedByVar
                }
            };
            self.push(kind, start);
            return;
        }

        // `(int)` and friends — a cast is `(` ws* TYPE ws* `)` (tabs/spaces only).
        if c == b'(' {
            let start = self.pos;
            if let Some((kind, end)) = self.try_cast() {
                self.pos = end;
                self.push(kind, start);
            } else {
                self.pos += 1;
                self.push(TokenKind::LParen, start);
            }
            return;
        }

        // Names beginning with a namespace separator.
        if c == b'\\' {
            let start = self.pos;
            let kind = self.lex_backslash_name();
            self.push(kind, start);
            return;
        }

        // Braces maintain the state stack so `{$expr}` returns to its string.
        if c == b'{' {
            let start = self.pos;
            self.pos += 1;
            self.push(TokenKind::LBrace, start);
            self.states.push(State::Scripting);
            return;
        }
        if c == b'}' {
            let start = self.pos;
            self.pos += 1;
            self.push(TokenKind::RBrace, start);
            if self.states.len() > 1 {
                self.states.pop();
            }
            return;
        }

        // Identifiers / keywords / namespaced names.
        if is_label_start(c) {
            let start = self.pos;
            let kind = self.lex_name();
            self.push(kind, start);
            if matches!(kind, TokenKind::Keyword(Kw::HaltCompiler)) {
                self.halt_seen = true;
            }
            return;
        }

        // Operators and punctuation.
        let start = self.pos;
        let kind = self.lex_operator();
        self.push(kind, start);
        if matches!(kind, TokenKind::Arrow | TokenKind::NullsafeArrow) {
            self.states.push(State::LookingForProperty);
        }
        // `__halt_compiler();` ends compilation; the rest is raw data.
        if self.halt_seen && kind == TokenKind::Semicolon && self.pos < self.len() {
            let start = self.pos;
            self.pos = self.len();
            self.push(TokenKind::InlineHtml, start);
        }
    }

    // --- ST_LOOKING_FOR_PROPERTY ------------------------------------------

    fn looking_for_property_step(&mut self) {
        let c = self.at(0);
        if is_ws(c) {
            self.pos += 1;
            return;
        }
        // Comments may sit between `->` and the property name.
        if c == b'/' && self.at(1) == b'/' {
            self.skip_line_comment();
            return;
        }
        if c == b'#' && self.at(1) != b'[' {
            self.skip_line_comment();
            return;
        }
        if c == b'/' && self.at(1) == b'*' {
            self.lex_block_comment();
            return;
        }
        if is_label_start(c) {
            // A property name: emitted as T_STRING even if it spells a keyword.
            let start = self.pos;
            self.consume_label();
            self.push(TokenKind::Identifier, start);
            self.states.pop();
            return;
        }
        // Not a bare property name (`{`, `$`, ...): hand back to scripting.
        self.states.pop();
    }

    // --- string / backquote bodies ----------------------------------------

    /// One step inside an interpolated string. `term` is the closing delimiter
    /// (`"` or `` ` ``) and `close_kind` the token emitted for it.
    fn string_body_step(&mut self, term: u8, close_kind: TokenKind) {
        let c = self.at(0);
        if c == term {
            let start = self.pos;
            self.pos += 1;
            self.push(close_kind, start);
            self.states.pop();
            return;
        }
        if c == b'$' && is_label_start(self.at(1)) {
            self.lex_simple_interp_var();
            return;
        }
        if c == b'$' && self.at(1) == b'{' {
            let start = self.pos;
            self.pos += 2;
            self.push(TokenKind::DollarOpenCurly, start);
            self.states.push(State::LookingForVarname);
            return;
        }
        if c == b'{' && self.at(1) == b'$' {
            let start = self.pos;
            self.pos += 1; // only the `{`
            self.push(TokenKind::CurlyOpen, start);
            self.states.push(State::Scripting);
            return;
        }
        self.scan_encapsed_run(term);
    }

    /// A literal run inside an interpolated string, up to the delimiter or the
    /// next interpolation.
    fn scan_encapsed_run(&mut self, term: u8) {
        let start = self.pos;
        while self.pos < self.len() {
            let c = self.at(0);
            if c == term {
                break;
            }
            if c == b'\\' {
                self.pos = (self.pos + 2).min(self.len());
                continue;
            }
            if c == b'$' && (is_label_start(self.at(1)) || self.at(1) == b'{') {
                break;
            }
            if c == b'{' && self.at(1) == b'$' {
                break;
            }
            self.pos += 1;
        }
        if self.pos > start {
            self.push(TokenKind::EncapsedAndWhitespace, start);
        } else {
            // Defensive: never stall (e.g. lone `{` not starting `{$`).
            self.pos += 1;
            self.push(TokenKind::EncapsedAndWhitespace, start);
        }
    }

    /// The "simple syntax" `$var`, `$var->prop`, or `$var[offset]` inside a
    /// string. Only a single level of `->`/`[]` is part of this syntax.
    fn lex_simple_interp_var(&mut self) {
        let start = self.pos;
        self.pos += 1;
        self.consume_label();
        self.push(TokenKind::Variable, start);

        if self.at(0) == b'-' && self.at(1) == b'>' && is_label_start(self.at(2)) {
            let s = self.pos;
            self.pos += 2;
            self.push(TokenKind::Arrow, s);
            let s2 = self.pos;
            self.consume_label();
            self.push(TokenKind::Identifier, s2);
        } else if self.at(0) == b'?'
            && self.at(1) == b'-'
            && self.at(2) == b'>'
            && is_label_start(self.at(3))
        {
            let s = self.pos;
            self.pos += 3;
            self.push(TokenKind::NullsafeArrow, s);
            let s2 = self.pos;
            self.consume_label();
            self.push(TokenKind::Identifier, s2);
        } else if self.at(0) == b'[' {
            let s = self.pos;
            self.pos += 1;
            self.push(TokenKind::LBracket, s);
            self.states.push(State::VarOffset);
        }
    }

    // --- ST_VAR_OFFSET (inside "$a[...]") ---------------------------------

    fn var_offset_step(&mut self) {
        let c = self.at(0);
        if c == b']' {
            let start = self.pos;
            self.pos += 1;
            self.push(TokenKind::RBracket, start);
            self.states.pop();
            return;
        }
        if c == b'$' && is_label_start(self.at(1)) {
            let start = self.pos;
            self.pos += 1;
            self.consume_label();
            self.push(TokenKind::Variable, start);
            return;
        }
        if c == b'-' {
            let start = self.pos;
            self.pos += 1;
            self.push(TokenKind::Minus, start);
            return;
        }
        if c.is_ascii_digit() {
            let start = self.pos;
            self.scan_offset_number();
            self.push(TokenKind::NumString, start);
            return;
        }
        if is_label_start(c) {
            let start = self.pos;
            self.consume_label();
            self.push(TokenKind::Identifier, start);
            return;
        }
        // Anything else terminates the offset defensively.
        self.states.pop();
    }

    fn scan_offset_number(&mut self) {
        if self.at(0) == b'0' && matches!(self.at(1), b'x' | b'X' | b'b' | b'B' | b'o' | b'O') {
            self.pos += 2;
        }
        while self.pos < self.len()
            && (self.at(0).is_ascii_hexdigit() || self.at(0) == b'_')
        {
            self.pos += 1;
        }
    }

    // --- ST_LOOKING_FOR_VARNAME (after `${`) ------------------------------

    fn looking_for_varname_step(&mut self) {
        let c = self.at(0);
        if is_label_start(c) {
            // Simple `${name}` / `${name[...]}` only when the name is immediately
            // followed by `[` or `}`; otherwise it is a general `${ expr }`.
            let mut i = self.pos + 1;
            while i < self.len() && is_label_cont(self.bytes[i]) {
                i += 1;
            }
            let after = self.bytes.get(i).copied().unwrap_or(0);
            if after == b'[' || after == b'}' {
                let start = self.pos;
                self.pos = i;
                self.push(TokenKind::StringVarname, start);
                self.set_state(State::Scripting);
                return;
            }
        }
        // General expression form: continue in scripting (re-lex from here).
        self.set_state(State::Scripting);
    }

    // --- heredoc / nowdoc -------------------------------------------------

    /// Whether a valid heredoc/nowdoc header (label + newline) begins at `lt`
    /// (the first `<` of `<<<`).
    fn heredoc_valid_at(&self, lt: usize) -> bool {
        let b = self.bytes;
        let mut i = lt + 3;
        while i < b.len() && matches!(b[i], b' ' | b'\t') {
            i += 1;
        }
        let quote = b.get(i).copied().unwrap_or(0);
        if quote == b'\'' || quote == b'"' {
            i += 1;
        }
        let ls = i;
        if i >= b.len() || !is_label_start(b[i]) {
            return false;
        }
        while i < b.len() && is_label_cont(b[i]) {
            i += 1;
        }
        if i == ls {
            return false;
        }
        if quote == b'\'' || quote == b'"' {
            if b.get(i).copied().unwrap_or(0) != quote {
                return false;
            }
            i += 1;
        }
        matches!(b.get(i).copied().unwrap_or(0), b'\n' | b'\r')
    }

    fn lex_heredoc_start(&mut self) {
        let start = self.pos;
        if matches!(self.at(0), b'b' | b'B') {
            self.pos += 1; // binary heredoc prefix
        }
        self.pos += 3; // <<<
        while matches!(self.at(0), b' ' | b'\t') {
            self.pos += 1;
        }
        let nowdoc;
        let label_start;
        match self.at(0) {
            b'\'' => {
                nowdoc = true;
                self.pos += 1;
                label_start = self.pos;
                self.consume_label();
                let label = self.text[label_start..self.pos].to_string();
                if self.at(0) == b'\'' {
                    self.pos += 1;
                }
                self.finish_heredoc_start(start, label, nowdoc);
            }
            b'"' => {
                self.pos += 1;
                label_start = self.pos;
                self.consume_label();
                let label = self.text[label_start..self.pos].to_string();
                if self.at(0) == b'"' {
                    self.pos += 1;
                }
                self.finish_heredoc_start(start, label, false);
            }
            _ => {
                label_start = self.pos;
                self.consume_label();
                let label = self.text[label_start..self.pos].to_string();
                self.finish_heredoc_start(start, label, false);
            }
        }
    }

    fn finish_heredoc_start(&mut self, start: usize, label: String, nowdoc: bool) {
        // The required newline is part of the T_START_HEREDOC token.
        if self.at(0) == b'\r' && self.at(1) == b'\n' {
            self.pos += 2;
        } else if matches!(self.at(0), b'\r' | b'\n') {
            self.pos += 1;
        }
        self.push(TokenKind::StartHeredoc, start);
        self.states.push(State::Heredoc(HeredocCtx { label, nowdoc }));
    }

    /// Is position `at` the start of this heredoc's closing marker? Returns the
    /// offset just past the label (the end of the `T_END_HEREDOC` token).
    fn heredoc_close_at(&self, at: usize, label: &str) -> Option<usize> {
        let b = self.bytes;
        let mut i = at;
        while i < b.len() && matches!(b[i], b' ' | b'\t') {
            i += 1;
        }
        let end = i + label.len();
        if end <= b.len()
            && &self.text[i..end] == label
            && (end == b.len() || !is_label_cont(b[end]))
        {
            return Some(end);
        }
        None
    }

    fn heredoc_step(&mut self, ctx: &HeredocCtx) {
        // The closing marker can only begin at the start of a line.
        let at_line_start = self.pos == 0 || self.bytes[self.pos - 1] == b'\n';
        if at_line_start {
            if let Some(end) = self.heredoc_close_at(self.pos, &ctx.label) {
                let start = self.pos;
                self.pos = end;
                self.push(TokenKind::EndHeredoc, start);
                self.states.pop();
                return;
            }
        }

        if ctx.nowdoc {
            self.scan_heredoc_body(&ctx.label, true);
            return;
        }

        let c = self.at(0);
        if c == b'$' && is_label_start(self.at(1)) {
            self.lex_simple_interp_var();
            return;
        }
        if c == b'$' && self.at(1) == b'{' {
            let start = self.pos;
            self.pos += 2;
            self.push(TokenKind::DollarOpenCurly, start);
            self.states.push(State::LookingForVarname);
            return;
        }
        if c == b'{' && self.at(1) == b'$' {
            let start = self.pos;
            self.pos += 1;
            self.push(TokenKind::CurlyOpen, start);
            self.states.push(State::Scripting);
            return;
        }
        self.scan_heredoc_body(&ctx.label, false);
    }

    /// Scan a run of heredoc/nowdoc body text. Stops at an interpolation trigger
    /// (heredoc only) or at the newline preceding the closing marker line (which
    /// is included in the run).
    fn scan_heredoc_body(&mut self, label: &str, nowdoc: bool) {
        let start = self.pos;
        while self.pos < self.len() {
            let c = self.at(0);
            if !nowdoc {
                if c == b'\\' {
                    // A backslash before a newline escapes only itself; the
                    // newline must still be seen so the closing marker is found.
                    let step = if matches!(self.at(1), b'\n' | b'\r') { 1 } else { 2 };
                    self.pos = (self.pos + step).min(self.len());
                    continue;
                }
                if c == b'$' && (is_label_start(self.at(1)) || self.at(1) == b'{') {
                    break;
                }
                if c == b'{' && self.at(1) == b'$' {
                    break;
                }
            }
            if c == b'\n' {
                self.pos += 1;
                if self.pos >= self.len() || self.heredoc_close_at(self.pos, label).is_some() {
                    break;
                }
                continue;
            }
            self.pos += 1;
        }
        if self.pos > start {
            self.push(TokenKind::EncapsedAndWhitespace, start);
        }
    }

    // --- comments & strings -----------------------------------------------

    fn skip_line_comment(&mut self) {
        while self.pos < self.len() {
            let c = self.at(0);
            if c == b'\n' || c == b'\r' {
                break;
            }
            if c == b'?' && self.at(1) == b'>' {
                break;
            }
            self.pos += 1;
        }
    }

    fn lex_block_comment(&mut self) {
        let start = self.pos;
        self.pos += 2; // `/*`
        let mut terminated = false;
        while self.pos < self.len() {
            if self.at(0) == b'*' && self.at(1) == b'/' {
                self.pos += 2;
                terminated = true;
                break;
            }
            self.pos += 1;
        }
        if !terminated {
            self.diags.push(Diagnostic::error(
                Span::from_range(start..self.pos),
                "unterminated comment",
            ));
        }
        let is_doc = self.pos - start >= 4
            && self.bytes[start + 2] == b'*'
            && start + 3 < self.len()
            && is_ws(self.bytes[start + 3]);
        if is_doc {
            self.push(TokenKind::DocComment, start);
        }
    }

    /// Whether the double-quoted string opening at `open` contains interpolation
    /// (and therefore must be tokenized piecewise rather than as one literal).
    fn double_quoted_interpolated(&self, open: usize) -> bool {
        let b = self.bytes;
        let mut i = open + 1;
        while i < b.len() {
            match b[i] {
                b'\\' => {
                    i += 2;
                    continue;
                }
                b'"' => return false,
                b'$' if i + 1 < b.len() && (is_label_start(b[i + 1]) || b[i + 1] == b'{') => {
                    return true
                }
                b'{' if i + 1 < b.len() && b[i + 1] == b'$' => return true,
                _ => {}
            }
            i += 1;
        }
        false
    }

    /// A whole non-interpolated quoted literal (`'...'` or simple `"..."`).
    fn lex_string(&mut self, start: usize) {
        let quote = self.at(0);
        self.pos += 1;
        let mut terminated = false;
        while self.pos < self.len() {
            let c = self.at(0);
            if c == b'\\' {
                self.pos = (self.pos + 2).min(self.len());
                continue;
            }
            if c == quote {
                self.pos += 1;
                terminated = true;
                break;
            }
            self.pos += 1;
        }
        if !terminated {
            self.diags.push(Diagnostic::error(
                Span::from_range(start..self.pos),
                "unterminated string literal",
            ));
        }
        self.push(TokenKind::String, start);
    }

    fn consume_label(&mut self) {
        while self.pos < self.len() && is_label_cont(self.at(0)) {
            self.pos += 1;
        }
    }

    fn lex_backslash_name(&mut self) -> TokenKind {
        if is_label_start(self.at(1)) {
            self.pos += 1; // `\`
            self.consume_label();
            while self.at(0) == b'\\' && is_label_start(self.at(1)) {
                self.pos += 1;
                self.consume_label();
            }
            TokenKind::NameFullyQualified
        } else {
            self.pos += 1;
            TokenKind::NsSeparator
        }
    }

    fn lex_name(&mut self) -> TokenKind {
        let start = self.pos;
        self.consume_label();
        let first = &self.text[start..self.pos];

        if self.at(0) == b'\\' && is_label_start(self.at(1)) {
            let relative = first.eq_ignore_ascii_case("namespace");
            while self.at(0) == b'\\' && is_label_start(self.at(1)) {
                self.pos += 1;
                self.consume_label();
            }
            return if relative {
                TokenKind::NameRelative
            } else {
                TokenKind::NameQualified
            };
        }

        // `yield from` is a single token spanning the gap between the words.
        if first.eq_ignore_ascii_case("yield") {
            if let Some(end) = self.yield_from_end() {
                self.pos = end;
                return TokenKind::YieldFrom;
            }
        }

        // `enum` is contextual: a keyword only when it starts a declaration
        // (`enum Foo`), otherwise an identifier (`enum()`, `enum;`, `enum::X`).
        if first.eq_ignore_ascii_case("enum") && !self.enum_is_declaration() {
            return TokenKind::Identifier;
        }

        match Kw::lookup(&first.to_ascii_lowercase()) {
            Some(kw) => {
                // Asymmetric visibility: `private(set)` etc. is one token (no
                // space allowed, `set` case-insensitive).
                if let Some(set_kind) = self.visibility_set_suffix(kw) {
                    self.pos += 5; // `(set)`
                    return set_kind;
                }
                TokenKind::Keyword(kw)
            }
            None => TokenKind::Identifier,
        }
    }

    fn visibility_set_suffix(&self, kw: Kw) -> Option<TokenKind> {
        let base = match kw {
            Kw::Private => TokenKind::PrivateSet,
            Kw::Protected => TokenKind::ProtectedSet,
            Kw::Public => TokenKind::PublicSet,
            _ => return None,
        };
        let end = self.pos + 5;
        if end <= self.len() && self.bytes[self.pos..end].eq_ignore_ascii_case(b"(set)") {
            Some(base)
        } else {
            None
        }
    }

    /// Whether the just-lexed `enum` begins an enum declaration: followed by
    /// whitespace/comments then an identifier that is not `extends`/`implements`.
    fn enum_is_declaration(&self) -> bool {
        let b = self.bytes;
        let i = self.skip_ws_and_comments(self.pos);
        if i >= b.len() || !is_label_start(b[i]) {
            return false;
        }
        let mut j = i;
        while j < b.len() && is_label_cont(b[j]) {
            j += 1;
        }
        let word = &self.text[i..j];
        !word.eq_ignore_ascii_case("extends") && !word.eq_ignore_ascii_case("implements")
    }

    /// If `yield` is followed by whitespace/comments then the word `from`, return
    /// the offset just past `from`.
    fn yield_from_end(&self) -> Option<usize> {
        let i = self.skip_ws_and_comments(self.pos);
        let end = i + 4;
        if end <= self.len()
            && self.bytes[i..].len() >= 4
            && self.bytes[i..end].eq_ignore_ascii_case(b"from")
            && i > self.pos // require at least one separator
            && (end == self.len() || !is_label_cont(self.bytes[end]))
        {
            Some(end)
        } else {
            None
        }
    }

    /// Skip whitespace and `//`, `#`, `/* */` comments starting at `from`,
    /// returning the offset of the next significant byte.
    fn skip_ws_and_comments(&self, from: usize) -> usize {
        let b = self.bytes;
        let mut i = from;
        loop {
            while i < b.len() && is_ws(b[i]) {
                i += 1;
            }
            if i + 1 < b.len() && b[i] == b'/' && b[i + 1] == b'/' {
                i += 2;
                while i < b.len() && b[i] != b'\n' && b[i] != b'\r' {
                    if b[i] == b'?' && i + 1 < b.len() && b[i + 1] == b'>' {
                        break;
                    }
                    i += 1;
                }
                continue;
            }
            if i < b.len() && b[i] == b'#' && !(i + 1 < b.len() && b[i + 1] == b'[') {
                i += 1;
                while i < b.len() && b[i] != b'\n' && b[i] != b'\r' {
                    i += 1;
                }
                continue;
            }
            if i + 1 < b.len() && b[i] == b'/' && b[i + 1] == b'*' {
                i += 2;
                while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') {
                    i += 1;
                }
                i = (i + 2).min(b.len());
                continue;
            }
            break;
        }
        i
    }

    /// With the cursor just past a `&`, is the next significant token `$` or
    /// `...` (i.e. a by-reference variable or a spread)?
    fn amp_followed_by_var_or_vararg(&self) -> bool {
        let b = self.bytes;
        let i = self.skip_ws_and_comments(self.pos);
        if i < b.len() && b[i] == b'$' {
            return true;
        }
        i + 3 <= b.len() && &b[i..i + 3] == b"..."
    }

    /// With the cursor on `(`, recognize a cast `( ws* TYPE ws* )` (tabs/spaces
    /// only, case-insensitive). Returns the cast token and the offset past `)`.
    fn try_cast(&self) -> Option<(TokenKind, usize)> {
        let b = self.bytes;
        let mut i = self.pos + 1;
        while i < b.len() && matches!(b[i], b' ' | b'\t') {
            i += 1;
        }
        let ts = i;
        while i < b.len() && b[i].is_ascii_alphabetic() {
            i += 1;
        }
        let kind = match self.text[ts..i].to_ascii_lowercase().as_str() {
            "int" | "integer" => TokenKind::IntCast,
            "float" | "double" | "real" => TokenKind::DoubleCast,
            "string" | "binary" => TokenKind::StringCast,
            "array" => TokenKind::ArrayCast,
            "object" => TokenKind::ObjectCast,
            "bool" | "boolean" => TokenKind::BoolCast,
            "unset" => TokenKind::UnsetCast,
            "void" => TokenKind::VoidCast,
            _ => return None,
        };
        while i < b.len() && matches!(b[i], b' ' | b'\t') {
            i += 1;
        }
        if i < b.len() && b[i] == b')' {
            Some((kind, i + 1))
        } else {
            None
        }
    }

    fn lex_operator(&mut self) -> TokenKind {
        use TokenKind::*;
        let c = self.at(0);
        let (kind, len) = match c {
            b'+' => match self.at(1) {
                b'=' => (PlusEq, 2),
                b'+' => (Inc, 2),
                _ => (Plus, 1),
            },
            b'-' => match self.at(1) {
                b'=' => (MinusEq, 2),
                b'-' => (Dec, 2),
                b'>' => (Arrow, 2),
                _ => (Minus, 1),
            },
            b'*' => {
                if self.at(1) == b'*' && self.at(2) == b'=' {
                    (PowEq, 3)
                } else if self.at(1) == b'*' {
                    (Pow, 2)
                } else if self.at(1) == b'=' {
                    (MulEq, 2)
                } else {
                    (Star, 1)
                }
            }
            b'/' => match self.at(1) {
                b'=' => (DivEq, 2),
                _ => (Slash, 1),
            },
            b'%' => match self.at(1) {
                b'=' => (ModEq, 2),
                _ => (Percent, 1),
            },
            b'.' => {
                if self.at(1) == b'.' && self.at(2) == b'.' {
                    (Ellipsis, 3)
                } else if self.at(1) == b'=' {
                    (ConcatEq, 2)
                } else {
                    (Dot, 1)
                }
            }
            b'=' => {
                if self.at(1) == b'=' && self.at(2) == b'=' {
                    (IsIdentical, 3)
                } else if self.at(1) == b'=' {
                    (IsEqual, 2)
                } else if self.at(1) == b'>' {
                    (DoubleArrow, 2)
                } else {
                    (Eq, 1)
                }
            }
            b'!' => {
                if self.at(1) == b'=' && self.at(2) == b'=' {
                    (IsNotIdentical, 3)
                } else if self.at(1) == b'=' {
                    (IsNotEqual, 2)
                } else {
                    (Bang, 1)
                }
            }
            b'<' => {
                if self.at(1) == b'=' && self.at(2) == b'>' {
                    (Spaceship, 3)
                } else if self.at(1) == b'<' && self.at(2) == b'=' {
                    (SlEq, 3)
                } else if self.at(1) == b'<' {
                    (Sl, 2)
                } else if self.at(1) == b'=' {
                    (LtEq, 2)
                } else if self.at(1) == b'>' {
                    (IsNotEqual, 2)
                } else {
                    (Lt, 1)
                }
            }
            b'>' => {
                if self.at(1) == b'>' && self.at(2) == b'=' {
                    (SrEq, 3)
                } else if self.at(1) == b'>' {
                    (Sr, 2)
                } else if self.at(1) == b'=' {
                    (GtEq, 2)
                } else {
                    (Gt, 1)
                }
            }
            b'?' => {
                if self.at(1) == b'-' && self.at(2) == b'>' {
                    (NullsafeArrow, 3)
                } else if self.at(1) == b'?' && self.at(2) == b'=' {
                    (CoalesceEq, 3)
                } else if self.at(1) == b'?' {
                    (Coalesce, 2)
                } else {
                    (Question, 1)
                }
            }
            b':' => match self.at(1) {
                b':' => (DoubleColon, 2),
                _ => (Colon, 1),
            },
            // `&` is handled in scripting_step (the by-ref/intersection split).
            b'|' => match self.at(1) {
                b'|' => (BoolOr, 2),
                b'=' => (OrEq, 2),
                b'>' => (PipeOp, 2),
                _ => (Pipe, 1),
            },
            b'^' => match self.at(1) {
                b'=' => (XorEq, 2),
                _ => (Caret, 1),
            },
            b'~' => (Tilde, 1),
            b'@' => (At, 1),
            b';' => (Semicolon, 1),
            b',' => (Comma, 1),
            b'(' => (LParen, 1),
            b')' => (RParen, 1),
            b'[' => (LBracket, 1),
            b']' => (RBracket, 1),
            b'`' => (Backtick, 1),
            _ => {
                self.diags.push(Diagnostic::error(
                    Span::from_range(self.pos..self.pos + 1),
                    format!("unexpected character {:?}", c as char),
                ));
                (Unknown, 1)
            }
        };
        self.pos += len;
        kind
    }

    /// Consume a run of `valid` digits, allowing a `_` separator only when it
    /// sits between two valid digits (PHP forbids leading/trailing/doubled `_`).
    fn consume_number_digits(&mut self, valid: fn(u8) -> bool) {
        while self.pos < self.len() {
            let c = self.at(0);
            // A `_` is allowed only strictly between two valid digits.
            let underscore_between =
                c == b'_' && self.pos > 0 && valid(self.bytes[self.pos - 1]) && valid(self.at(1));
            if valid(c) || underscore_between {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn lex_number(&mut self) -> TokenKind {
        let start = self.pos;

        // Radix-prefixed integers — only if at least one valid digit follows the
        // prefix (otherwise `0xg` is the integer `0` followed by `xg`).
        if self.at(0) == b'0' {
            let valid: Option<fn(u8) -> bool> = match self.at(1) {
                b'x' | b'X' => Some(|d: u8| d.is_ascii_hexdigit()),
                b'b' | b'B' => Some(|d: u8| d == b'0' || d == b'1'),
                b'o' | b'O' => Some(|d: u8| (b'0'..=b'7').contains(&d)),
                _ => None,
            };
            if let Some(valid) = valid {
                if valid(self.at(2)) {
                    self.pos += 2;
                    self.consume_number_digits(valid);
                    return self.int_or_overflow_float(start);
                }
            }
        }

        let mut is_float = false;
        self.consume_number_digits(|d| d.is_ascii_digit());

        if self.at(0) == b'.' {
            let had_int = self.pos > start;
            let frac_digit = self.at(1).is_ascii_digit();
            if had_int || frac_digit {
                is_float = true;
                self.pos += 1;
                self.consume_number_digits(|d| d.is_ascii_digit());
            }
        }

        if matches!(self.at(0), b'e' | b'E') {
            let mut j = 1;
            if matches!(self.at(j), b'+' | b'-') {
                j += 1;
            }
            if self.at(j).is_ascii_digit() {
                is_float = true;
                self.pos += j;
                self.consume_number_digits(|d| d.is_ascii_digit());
            }
        }

        if is_float {
            TokenKind::Float
        } else {
            self.int_or_overflow_float(start)
        }
    }

    /// An integer literal whose value exceeds the platform int range
    /// (`i64::MAX`) is a `T_DNUMBER` in PHP, like the runtime promotes it.
    fn int_or_overflow_float(&self, start: usize) -> TokenKind {
        let text = &self.text[start..self.pos];
        if int_literal_overflows_i64(text) {
            TokenKind::Float
        } else {
            TokenKind::Int
        }
    }
}

/// Whether a (non-negative) integer literal overflows `i64::MAX`, accounting for
/// `0x`/`0b`/`0o` prefixes, legacy `0NNN` octal, and `_` digit separators.
fn int_literal_overflows_i64(text: &str) -> bool {
    let cleaned: String = text.chars().filter(|&c| c != '_').collect();
    let lower = cleaned.to_ascii_lowercase();
    let (radix, digits) = if let Some(d) = lower.strip_prefix("0x") {
        (16u32, d)
    } else if let Some(d) = lower.strip_prefix("0b") {
        (2, d)
    } else if let Some(d) = lower.strip_prefix("0o") {
        (8, d)
    } else if cleaned.len() > 1
        && cleaned.starts_with('0')
        && cleaned.bytes().all(|b| (b'0'..=b'7').contains(&b))
    {
        (8, &cleaned[1..]) // legacy octal
    } else {
        (10, cleaned.as_str())
    };
    match u128::from_str_radix(digits, radix) {
        Ok(v) => v > i64::MAX as u128,
        Err(_) => true, // too large even for u128 → certainly a float
    }
}
