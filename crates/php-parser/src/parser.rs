//! Hand-written recursive-descent + Pratt parser.

use php_ast::*;
use php_diagnostics::Diagnostic;
use php_intern::{Interner, Symbol};
use php_lexer::{Kw, Token, TokenKind as T};
use php_span::Span;

/// Recursion-depth cap for expression and block nesting. A hand-written
/// recursive-descent parser recurses once per nesting level, so adversarial or
/// machine-generated deeply-nested input can overflow the stack — and a stack
/// overflow aborts the process (it is *not* catchable by `catch_unwind`). When
/// the cap is hit we emit a diagnostic and stop descending, keeping `parse`
/// total. Real code nests far below this; PHP itself imposes similar limits.
const MAX_DEPTH: u32 = 256;

enum StaticMemberName {
    Property(MemberName),
    /// `::$$expr` — carries the `$`'s offset so the synthesized
    /// `VariableVariable` spans the member, not the whole `Class::$$x` expression.
    DollarExpr {
        dollar: u32,
        inner: Expr,
    },
    ConstOrMethod(MemberName),
}

pub struct Parser<'a> {
    src: &'a str,
    tokens: Vec<Token>,
    pos: usize,
    /// Borrowed (shared) so several files can share one project-wide interner —
    /// symbols are then comparable/resolvable across files (required for
    /// cross-file analysis), and the concurrent interner lets files parse in
    /// parallel into the same interner.
    interner: &'a Interner,
    diags: Vec<Diagnostic>,
    depth: u32,
    /// Doc-comments are kept out of the parse stream (so they never disrupt
    /// parsing) and attached to following declarations/statements by source
    /// position. `(end, text)`, in source order.
    ///
    /// The text is `Arc<str>`, allocated **once** per doc-comment at harvest:
    /// attaching it to a node is a refcount bump, and so is the parser's
    /// re-dispatch through `parse_attributed_decl` / `parse_class_like`. It used
    /// to be a `String` copied out of the source and then cloned again per
    /// attachment — two allocations of the full doc text per declaration, over
    /// 6MB of them across the corpus and stubs.
    docs: Vec<(u32, std::sync::Arc<str>)>,
}

impl<'a> Parser<'a> {
    pub fn new(source: &'a str, interner: &'a Interner) -> Parser<'a> {
        let (lexed, diags) = php_lexer::tokenize(source);
        let mut docs = Vec::new();
        let mut tokens = Vec::with_capacity(lexed.len());
        for t in lexed {
            if t.kind == T::DocComment {
                docs.push((t.span.end, std::sync::Arc::from(t.span.text(source))));
            } else {
                tokens.push(t);
            }
        }
        Parser {
            src: source,
            tokens,
            pos: 0,
            interner,
            diags,
            depth: 0,
            docs,
        }
    }

    /// The doc-comment preceding `offset`, if any: only whitespace and plain
    /// comments may sit between the two.
    ///
    /// Tolerating comments matters because the "docblock, `// TODO`,
    /// declaration" shape is everywhere, and requiring a whitespace-only gap
    /// silently drops the `@param`/`@return`/`@var` types for every one of them.
    /// Zend is stickier still (its `CG(doc_comment)` survives even an
    /// intervening statement); we follow PHP-Parser and stop at anything that
    /// isn't trivia, since a docblock separated from its declaration by real
    /// code is not documenting it.
    ///
    /// `docs` is sorted by end offset (the lexer emits in source order), so the
    /// candidate is found by binary search. The previous reverse linear scan
    /// walked past every doc-comment *after* `offset` on each call, which is
    /// quadratic in the number of docblocks per file — paid heavily by
    /// doc-dense sources like the stubs.
    fn doc_before(&self, offset: u32) -> Option<std::sync::Arc<str>> {
        let idx = self.docs.partition_point(|(end, _)| *end <= offset);
        let (end, text) = self.docs.get(idx.checked_sub(1)?)?;
        gap_is_trivia(&self.src[*end as usize..offset as usize]).then(|| text.clone())
    }

    /// Parse the token stream into a program + diagnostics. The interner is the
    /// borrowed one passed to [`Parser::new`] (the caller owns it), so this no
    /// longer returns it.
    pub fn parse(mut self) -> (Program, Vec<Diagnostic>) {
        let mut stmts = Vec::new();
        while !self.at_eof() {
            let before = self.pos;
            if let Some(s) = self.parse_stmt_or_marker() {
                stmts.push(s);
            }
            self.ensure_progress(before);
        }
        (Program { stmts }, self.diags)
    }

    // --- cursor -----------------------------------------------------------

    #[inline]
    fn peek(&self) -> T {
        self.tokens[self.pos].kind
    }
    #[inline]
    fn nth(&self, n: usize) -> T {
        self.tokens
            .get(self.pos + n)
            .map(|t| t.kind)
            .unwrap_or(T::Eof)
    }
    #[inline]
    fn at(&self, k: T) -> bool {
        self.peek() == k
    }
    #[inline]
    fn at_eof(&self) -> bool {
        self.peek() == T::Eof
    }
    #[inline]
    fn cur_start(&self) -> u32 {
        self.tokens[self.pos].span.start
    }
    #[inline]
    fn prev_end(&self) -> u32 {
        if self.pos > 0 {
            self.tokens[self.pos - 1].span.end
        } else {
            0
        }
    }
    /// A span from `start` to the end of the last consumed token, clamped so it
    /// is never reversed (an error node that consumed nothing gets a zero-width
    /// span at `start` rather than tripping the `Span` invariant).
    #[inline]
    fn span_to(&self, start: u32) -> Span {
        Span::new(start, self.prev_end().max(start))
    }
    fn bump(&mut self) -> Token {
        let t = self.tokens[self.pos];
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, k: T) -> bool {
        if self.at(k) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, k: T, what: &str) {
        if !self.eat(k) {
            self.error_here(&format!("expected {what}"));
        }
    }
    fn eat_amp(&mut self) -> bool {
        if matches!(self.peek(), T::AmpFollowedByVar | T::AmpNotFollowedByVar) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn text(&self, t: Token) -> &'a str {
        t.span.text(self.src)
    }
    fn intern_tok(&mut self, t: Token) -> Symbol {
        self.interner.intern(t.span.text(self.src))
    }
    /// Intern a `$name` token without its leading `$`.
    fn intern_var(&mut self, t: Token) -> Symbol {
        let s = t.span.text(self.src);
        self.interner.intern(s.strip_prefix('$').unwrap_or(s))
    }

    fn error_here(&mut self, msg: &str) {
        let span = self.tokens[self.pos].span;
        let code = if msg.starts_with("expected ") {
            "parse.expected"
        } else if msg.starts_with("unexpected ") {
            "parse.unexpected"
        } else {
            "parse.error"
        };
        self.diags
            .push(Diagnostic::error(span, msg.to_string()).with_code(code));
    }

    fn node(&self, start: u32, kind: ExprKind) -> Expr {
        Expr::new(self.span_to(start), kind)
    }

    // --- statements -------------------------------------------------------

    /// Parse a statement, or consume a non-statement marker (open/close tag)
    /// returning `None`.
    fn parse_stmt_or_marker(&mut self) -> Option<Stmt> {
        match self.peek() {
            T::OpenTag | T::CloseTag => {
                self.bump();
                None
            }
            T::InlineHtml => {
                let t = self.bump();
                Some(Stmt::new(
                    t.span,
                    StmtKind::InlineHtml(self.text(t).to_string()),
                ))
            }
            T::OpenTagEcho => {
                let start = self.cur_start();
                self.bump();
                let exprs = self.parse_expr_list();
                self.eat_stmt_end();
                Some(Stmt::new(self.span_to(start), StmtKind::Echo(exprs)))
            }
            T::Eof => None,
            _ => Some(self.parse_statement()),
        }
    }

    fn parse_statement(&mut self) -> Stmt {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            self.depth -= 1;
            let s = self.cur_start();
            self.error_here("nesting level too deep");
            self.synchronize();
            return Stmt::new(self.span_to(s), StmtKind::Error);
        }
        let start = self.cur_start();
        let doc = self.doc_before(start);
        let kind = match self.peek() {
            T::Semicolon => {
                self.bump();
                StmtKind::Nop
            }
            T::LBrace => StmtKind::Block(self.parse_brace_block()),
            T::Keyword(Kw::Echo) => {
                self.bump();
                let exprs = self.parse_expr_list();
                self.eat_stmt_end();
                StmtKind::Echo(exprs)
            }
            T::Keyword(Kw::Return) => {
                self.bump();
                let value = if self.at_stmt_end() {
                    None
                } else {
                    Some(self.parse_expr(0))
                };
                self.eat_stmt_end();
                StmtKind::Return(value)
            }
            T::Keyword(Kw::If) => self.parse_if(),
            T::Keyword(Kw::While) => self.parse_while(),
            T::Keyword(Kw::Do) => self.parse_do_while(),
            T::Keyword(Kw::For) => self.parse_for(),
            T::Keyword(Kw::Foreach) => self.parse_foreach(),
            T::Keyword(Kw::Switch) => self.parse_switch(),
            T::Keyword(Kw::Try) => self.parse_try(),
            T::Keyword(Kw::Break) => self.parse_break_continue(true),
            T::Keyword(Kw::Continue) => self.parse_break_continue(false),
            T::Keyword(Kw::Goto) => {
                self.bump();
                let name = self.expect_label_name();
                self.eat_stmt_end();
                StmtKind::Goto(name)
            }
            T::Keyword(Kw::Global) => {
                self.bump();
                let vars = self.parse_expr_list();
                self.eat_stmt_end();
                StmtKind::Global(vars)
            }
            T::Keyword(Kw::Static) if self.nth(1) == T::Variable => {
                self.bump();
                let vars = self.parse_static_vars();
                self.eat_stmt_end();
                StmtKind::StaticVars(vars)
            }
            T::Keyword(Kw::Unset) => {
                self.bump();
                self.expect(T::LParen, "`(`");
                let vars = self.parse_call_like_exprs();
                self.expect(T::RParen, "`)`");
                self.eat_stmt_end();
                StmtKind::Unset(vars)
            }
            T::Keyword(Kw::Declare) => self.parse_declare(),
            T::Keyword(Kw::Namespace) => self.parse_namespace(),
            T::Keyword(Kw::Use) => {
                let kind = self.parse_use();
                self.eat_stmt_end();
                kind
            }
            // --- declarations ---
            T::Attribute => self.parse_attributed_decl(doc.clone()),
            T::Keyword(Kw::Function) if self.is_function_decl() => {
                StmtKind::Function(self.parse_function_decl(Vec::new(), doc.clone()))
            }
            T::Keyword(Kw::Abstract | Kw::Final | Kw::Class | Kw::Interface | Kw::Trait) => {
                StmtKind::Class(self.parse_class_like(Vec::new(), doc.clone()))
            }
            T::Keyword(Kw::Readonly) if self.readonly_starts_class() => {
                StmtKind::Class(self.parse_class_like(Vec::new(), doc.clone()))
            }
            T::Keyword(Kw::Enum) if self.nth(1) == T::Identifier => {
                StmtKind::Class(self.parse_class_like(Vec::new(), doc.clone()))
            }
            T::Keyword(Kw::Const) => {
                let consts = self.parse_const_elems();
                self.eat_stmt_end();
                StmtKind::ConstDecl {
                    consts,
                    attrs: Vec::new(),
                }
            }
            T::Keyword(Kw::HaltCompiler) => {
                self.bump();
                self.eat(T::LParen);
                self.eat(T::RParen);
                self.eat_stmt_end();
                let offset = self.prev_end();
                // The lexer turned the trailing bytes into one T_INLINE_HTML;
                // PHP's AST does not include them, so drop it.
                self.eat(T::InlineHtml);
                StmtKind::HaltCompiler(offset)
            }

            // A label: `name:` (but not `name::` or `name ? :`).
            T::Identifier if self.nth(1) == T::Colon => {
                let t = self.bump();
                self.bump(); // `:`
                StmtKind::Label(self.intern_tok(t))
            }
            _ => {
                let e = self.parse_expr(0);
                self.eat_stmt_end();
                StmtKind::Expr(e)
            }
        };
        self.depth -= 1;
        let mut stmt = Stmt::new(self.span_to(start), kind);
        if stmt_allows_raw_doc(&stmt.kind) {
            stmt.doc = doc;
        }
        stmt
    }

    /// `{ stmt* }` — the statement list (depth is guarded by `parse_statement`).
    fn parse_brace_block(&mut self) -> Vec<Stmt> {
        self.expect(T::LBrace, "`{`");
        let stmts = self.stmt_list_until(&[]);
        self.expect(T::RBrace, "`}`");
        stmts
    }

    // --- control flow -----------------------------------------------------

    fn at_kw(&self, kw: Kw) -> bool {
        self.peek() == T::Keyword(kw)
    }
    fn at_kw_any(&self, kws: &[Kw]) -> bool {
        matches!(self.peek(), T::Keyword(k) if kws.contains(&k))
    }
    fn expect_kw(&mut self, kw: Kw, what: &str) {
        if !self.eat(T::Keyword(kw)) {
            self.error_here(&format!("expected {what}"));
        }
    }

    /// Statements until a terminating keyword, a `}`, or EOF (none consumed).
    fn stmt_list_until(&mut self, terms: &[Kw]) -> Vec<Stmt> {
        let mut v = Vec::new();
        while !self.at_eof() && !self.at(T::RBrace) && !self.at_kw_any(terms) {
            let before = self.pos;
            if let Some(s) = self.parse_stmt_or_marker() {
                v.push(s);
            }
            self.ensure_progress(before);
        }
        v
    }

    /// Error-recovery backstop: if a sub-parser made no progress, consume one
    /// token so loops can never spin forever.
    fn ensure_progress(&mut self, before: usize) {
        if self.pos == before && !self.at_eof() {
            self.bump();
        }
    }

    /// A loop/if body: either a single statement, or the alternative-syntax form
    /// `: stmt* end<kw>;`.
    fn parse_loop_body(&mut self, end: Kw) -> Box<Stmt> {
        if self.at(T::Colon) {
            let start = self.cur_start();
            self.bump(); // `:`
            let stmts = self.stmt_list_until(&[end]);
            self.expect_kw(end, "loop end keyword");
            self.eat_stmt_end();
            Box::new(Stmt::new(self.span_to(start), StmtKind::Block(stmts)))
        } else {
            Box::new(self.parse_statement())
        }
    }

    fn parse_if(&mut self) -> StmtKind {
        self.bump(); // if
        self.expect(T::LParen, "`(`");
        let cond = self.parse_expr(0);
        self.expect(T::RParen, "`)`");

        if self.at(T::Colon) {
            // Alternative syntax: if (..): .. elseif (..): .. else: .. endif;
            self.bump();
            let then = self.alt_block(&[Kw::Elseif, Kw::Else, Kw::Endif]);
            let mut elseifs = Vec::new();
            while self.at_kw(Kw::Elseif) {
                self.bump();
                self.expect(T::LParen, "`(`");
                let c = self.parse_expr(0);
                self.expect(T::RParen, "`)`");
                self.expect(T::Colon, "`:`");
                let body = self.alt_block(&[Kw::Elseif, Kw::Else, Kw::Endif]);
                elseifs.push(ElseIf { cond: c, body });
            }
            let els = if self.at_kw(Kw::Else) {
                self.bump();
                self.expect(T::Colon, "`:`");
                Some(Box::new(self.alt_block(&[Kw::Endif])))
            } else {
                None
            };
            self.expect_kw(Kw::Endif, "`endif`");
            self.eat_stmt_end();
            return StmtKind::If {
                cond,
                then: Box::new(then),
                elseifs,
                els,
            };
        }

        let then = Box::new(self.parse_statement());
        let mut elseifs = Vec::new();
        while self.at_kw(Kw::Elseif) {
            self.bump();
            self.expect(T::LParen, "`(`");
            let c = self.parse_expr(0);
            self.expect(T::RParen, "`)`");
            let body = self.parse_statement();
            elseifs.push(ElseIf { cond: c, body });
        }
        // `else` (note: `else if` parses as an `else` whose body is an `if`).
        let els = if self.at_kw(Kw::Else) {
            self.bump();
            Some(Box::new(self.parse_statement()))
        } else {
            None
        };
        StmtKind::If {
            cond,
            then,
            elseifs,
            els,
        }
    }

    /// An alternative-syntax body: statements until one of `terms`, wrapped in a
    /// synthetic block statement.
    fn alt_block(&mut self, terms: &[Kw]) -> Stmt {
        let start = self.cur_start();
        let stmts = self.stmt_list_until(terms);
        Stmt::new(self.span_to(start), StmtKind::Block(stmts))
    }

    fn parse_while(&mut self) -> StmtKind {
        self.bump();
        self.expect(T::LParen, "`(`");
        let cond = self.parse_expr(0);
        self.expect(T::RParen, "`)`");
        let body = self.parse_loop_body(Kw::Endwhile);
        StmtKind::While { cond, body }
    }

    fn parse_do_while(&mut self) -> StmtKind {
        self.bump();
        let body = Box::new(self.parse_statement());
        self.expect_kw(Kw::While, "`while`");
        self.expect(T::LParen, "`(`");
        let cond = self.parse_expr(0);
        self.expect(T::RParen, "`)`");
        self.eat_stmt_end();
        StmtKind::DoWhile { body, cond }
    }

    fn parse_for(&mut self) -> StmtKind {
        self.bump();
        self.expect(T::LParen, "`(`");
        let init = self.for_exprs(T::Semicolon);
        self.expect(T::Semicolon, "`;`");
        let cond = self.for_exprs(T::Semicolon);
        self.expect(T::Semicolon, "`;`");
        let update = self.for_exprs(T::RParen);
        self.expect(T::RParen, "`)`");
        let body = self.parse_loop_body(Kw::Endfor);
        StmtKind::For {
            init,
            cond,
            update,
            body,
        }
    }

    /// A comma-separated (possibly empty) expression list up to `stop`.
    fn for_exprs(&mut self, stop: T) -> Vec<Expr> {
        let mut v = Vec::new();
        if self.at(stop) {
            return v;
        }
        v.push(self.parse_expr(0));
        while self.eat(T::Comma) {
            if self.at(stop) {
                break;
            }
            v.push(self.parse_expr(0));
        }
        v
    }

    fn parse_foreach(&mut self) -> StmtKind {
        self.bump();
        self.expect(T::LParen, "`(`");
        let subject = self.parse_expr(0);
        self.expect_kw(Kw::As, "`as`");
        let by_ref1 = self.eat_amp();
        let first = self.parse_expr(0);
        let (key, value, by_ref, key_by_ref) = if self.eat(T::DoubleArrow) {
            let by_ref2 = self.eat_amp();
            let val = self.parse_expr(0);
            (Some(first), val, by_ref2, by_ref1)
        } else {
            (None, first, by_ref1, false)
        };
        self.expect(T::RParen, "`)`");
        let body = self.parse_loop_body(Kw::Endforeach);
        StmtKind::Foreach {
            subject,
            key,
            value,
            by_ref,
            key_by_ref,
            body,
        }
    }

    fn parse_switch(&mut self) -> StmtKind {
        self.bump();
        self.expect(T::LParen, "`(`");
        let subject = self.parse_expr(0);
        self.expect(T::RParen, "`)`");
        let alt = self.at(T::Colon);
        if alt {
            self.bump();
        } else {
            self.expect(T::LBrace, "`{`");
        }
        let mut cases = Vec::new();
        while !self.at_eof() && !self.at(T::RBrace) && !self.at_kw(Kw::Endswitch) {
            let test = if self.eat(T::Keyword(Kw::Case)) {
                let e = self.parse_expr(0);
                Some(e)
            } else if self.eat(T::Keyword(Kw::Default)) {
                None
            } else {
                // Stray token inside switch; recover.
                self.error_here("expected `case` or `default`");
                self.bump();
                continue;
            };
            if !self.eat(T::Colon) {
                self.eat(T::Semicolon);
            }
            let body = self.stmt_list_until(&[Kw::Case, Kw::Default, Kw::Endswitch]);
            cases.push(SwitchCase { test, body });
        }
        if alt {
            self.expect_kw(Kw::Endswitch, "`endswitch`");
            self.eat_stmt_end();
        } else {
            self.expect(T::RBrace, "`}`");
        }
        StmtKind::Switch { subject, cases }
    }

    fn parse_try(&mut self) -> StmtKind {
        self.bump();
        let body = self.parse_brace_block();
        let mut catches = Vec::new();
        while self.at_kw(Kw::Catch) {
            self.bump();
            self.expect(T::LParen, "`(`");
            let mut types = vec![self.parse_name()];
            while self.eat(T::Pipe) {
                types.push(self.parse_name());
            }
            let var = if self.at(T::Variable) {
                let t = self.bump();
                Some(self.intern_var(t))
            } else {
                None
            };
            self.expect(T::RParen, "`)`");
            let cbody = self.parse_brace_block();
            catches.push(Catch {
                types,
                var,
                body: cbody,
            });
        }
        let finally = if self.at_kw(Kw::Finally) {
            self.bump();
            Some(self.parse_brace_block())
        } else {
            None
        };
        StmtKind::Try {
            body,
            catches,
            finally,
        }
    }

    fn parse_break_continue(&mut self, is_break: bool) -> StmtKind {
        self.bump();
        let level = if self.at_stmt_end() {
            None
        } else {
            Some(self.parse_expr(0))
        };
        self.eat_stmt_end();
        if is_break {
            StmtKind::Break(level)
        } else {
            StmtKind::Continue(level)
        }
    }

    fn parse_static_vars(&mut self) -> Vec<StaticVar> {
        let mut vars = Vec::new();
        loop {
            let name = if self.at(T::Variable) {
                let t = self.bump();
                self.intern_var(t)
            } else {
                self.error_here("expected variable");
                self.interner.intern("")
            };
            let default = if self.eat(T::Eq) {
                Some(self.parse_expr(0))
            } else {
                None
            };
            vars.push(StaticVar { name, default });
            if !self.eat(T::Comma) {
                break;
            }
        }
        vars
    }

    /// A comma-separated expression list up to `)` (used by `unset(...)`).
    fn parse_call_like_exprs(&mut self) -> Vec<Expr> {
        let mut v = Vec::new();
        while !self.at(T::RParen) && !self.at_eof() {
            v.push(self.parse_expr(0));
            if !self.eat(T::Comma) {
                break;
            }
        }
        v
    }

    fn parse_declare(&mut self) -> StmtKind {
        self.bump();
        self.expect(T::LParen, "`(`");
        let mut directives = Vec::new();
        while !self.at(T::RParen) && !self.at_eof() {
            let name = if matches!(self.peek(), T::Identifier | T::Keyword(_)) {
                let t = self.bump();
                self.intern_tok(t)
            } else {
                self.error_here("expected directive name");
                self.interner.intern("")
            };
            self.expect(T::Eq, "`=`");
            let value = self.parse_expr(0);
            directives.push((name, value));
            if !self.eat(T::Comma) {
                break;
            }
        }
        self.expect(T::RParen, "`)`");
        let body = if self.at(T::LBrace) {
            Some(Box::new(Stmt::new(
                Span::new(self.cur_start(), self.cur_start()),
                StmtKind::Block(self.parse_brace_block()),
            )))
        } else if self.at(T::Colon) {
            self.bump();
            let start = self.cur_start();
            let stmts = self.stmt_list_until(&[Kw::Enddeclare]);
            self.expect_kw(Kw::Enddeclare, "`enddeclare`");
            self.eat_stmt_end();
            Some(Box::new(Stmt::new(
                self.span_to(start),
                StmtKind::Block(stmts),
            )))
        } else {
            self.eat_stmt_end();
            None
        };
        StmtKind::Declare { directives, body }
    }

    fn parse_namespace(&mut self) -> StmtKind {
        self.bump();
        // A reserved word may be a namespace-name segment (`namespace enum;`).
        let name = if matches!(
            self.peek(),
            T::Identifier
                | T::NameQualified
                | T::NameFullyQualified
                | T::NameRelative
                | T::Keyword(_)
        ) {
            Some(self.parse_name())
        } else {
            None
        };
        let body = if self.at(T::LBrace) {
            Some(self.parse_brace_block())
        } else {
            self.eat_stmt_end();
            None
        };
        StmtKind::Namespace { name, body }
    }

    fn parse_use(&mut self) -> StmtKind {
        self.bump(); // use
        let group_kind = self.use_type();
        let mut items = Vec::new();
        loop {
            let item_kind = self
                .use_type()
                .unwrap_or(group_kind.unwrap_or(UseKind::Class));
            let name = self.parse_name();
            // Group use: `use Prefix\{ ... }`. The `\` before `{` is a separate
            // namespace-separator token after the (qualified) prefix name.
            let is_group =
                self.at(T::LBrace) || (self.at(T::NsSeparator) && self.nth(1) == T::LBrace);
            if is_group {
                self.eat(T::NsSeparator);
                self.expect(T::LBrace, "`{`");
                let mut group_items = Vec::new();
                while !self.at(T::RBrace) && !self.at_eof() {
                    let sub_kind = self
                        .use_type()
                        .unwrap_or(group_kind.unwrap_or(UseKind::Class));
                    let sub = self.parse_name();
                    let alias = self.parse_use_alias();
                    group_items.push(UseItem {
                        kind: sub_kind,
                        name: sub,
                        alias,
                    });
                    if !self.eat(T::Comma) {
                        break;
                    }
                }
                self.expect(T::RBrace, "`}`");
                return StmtKind::GroupUse {
                    prefix: name,
                    kind: group_kind,
                    items: group_items,
                };
            }
            let alias = self.parse_use_alias();
            items.push(UseItem {
                kind: item_kind,
                name,
                alias,
            });
            if !self.eat(T::Comma) {
                break;
            }
        }
        StmtKind::Use(items)
    }

    fn use_type(&mut self) -> Option<UseKind> {
        if self.eat(T::Keyword(Kw::Function)) {
            Some(UseKind::Function)
        } else if self.eat(T::Keyword(Kw::Const)) {
            Some(UseKind::Const)
        } else {
            None
        }
    }

    fn parse_use_alias(&mut self) -> Option<Symbol> {
        if self.eat(T::Keyword(Kw::As)) {
            if matches!(self.peek(), T::Identifier | T::Keyword(_)) {
                let t = self.bump();
                return Some(self.intern_tok(t));
            }
            self.error_here("expected alias name");
        }
        None
    }

    /// Parse a (possibly qualified) name into an AST [`Name`].
    fn parse_name(&mut self) -> Name {
        if self.name_token_allows_keywords(self.peek()) {
            let t = self.bump();
            self.name_from_token(t)
        } else {
            self.error_here("expected a name");
            self.empty_name()
        }
    }

    fn parse_expr_name(&mut self) -> Name {
        if self.name_token(self.peek()) {
            let t = self.bump();
            self.name_from_token(t)
        } else {
            self.error_here("expected a name");
            self.empty_name()
        }
    }

    fn parse_type_simple_name(&mut self) -> Name {
        if self.type_name_token(self.peek()) {
            let t = self.bump();
            self.name_from_token(t)
        } else {
            self.error_here("expected a type");
            self.empty_name()
        }
    }

    fn name_from_token(&self, t: Token) -> Name {
        let fq = match t.kind {
            T::NameFullyQualified => NameFq::Fq,
            T::NameRelative => NameFq::Relative,
            _ => NameFq::NotFq,
        };
        Name {
            span: t.span,
            fq,
            text: self.text(t).to_string(),
        }
    }

    fn empty_name(&self) -> Name {
        Name {
            span: Span::at(self.cur_start()),
            fq: NameFq::NotFq,
            text: String::new(),
        }
    }

    fn name_token(&self, kind: T) -> bool {
        matches!(
            kind,
            T::Identifier | T::NameQualified | T::NameFullyQualified | T::NameRelative
        )
    }

    fn name_token_allows_keywords(&self, kind: T) -> bool {
        self.name_token(kind) || matches!(kind, T::Keyword(_))
    }

    fn type_name_token(&self, kind: T) -> bool {
        self.name_token(kind) || matches!(kind, T::Keyword(Kw::Array | Kw::Callable | Kw::Static))
    }

    fn expect_label_name(&mut self) -> Symbol {
        if matches!(self.peek(), T::Identifier | T::Keyword(_)) {
            let t = self.bump();
            self.intern_tok(t)
        } else {
            self.error_here("expected label name");
            self.interner.intern("")
        }
    }

    // --- declarations -----------------------------------------------------

    /// `function` begins a *named* function declaration when a name (or `&` + a
    /// name) follows; `function (` / `function &(` is a closure expression.
    fn is_function_decl(&self) -> bool {
        match self.nth(1) {
            T::Identifier | T::Keyword(_) => true,
            T::AmpFollowedByVar | T::AmpNotFollowedByVar => {
                matches!(self.nth(2), T::Identifier | T::Keyword(_))
            }
            _ => false,
        }
    }

    /// `readonly` begins a class declaration when followed by `class` or another
    /// class modifier (otherwise `readonly(...)` is a function call).
    fn readonly_starts_class(&self) -> bool {
        matches!(
            self.nth(1),
            T::Keyword(Kw::Class | Kw::Abstract | Kw::Final | Kw::Readonly)
        )
    }

    /// A reserved word or identifier used as a member/function name.
    fn member_ident(&mut self) -> Symbol {
        if matches!(self.peek(), T::Identifier | T::Keyword(_)) {
            let t = self.bump();
            self.intern_tok(t)
        } else {
            self.error_here("expected a name");
            self.interner.intern("")
        }
    }

    /// Like [`member_ident`](Self::member_ident) but also returns the span of the
    /// name token, for member-precise diagnostics.
    fn member_ident_spanned(&mut self) -> (Symbol, Span) {
        let start = self.cur_start();
        (self.member_ident(), self.span_to(start))
    }

    /// Whether the cursor sits on a closure or arrow function — the only
    /// expressions PHP lets an attribute decorate (an anonymous class is
    /// attributed after `new`, handled in [`Self::parse_new`]).
    fn at_attributable_closure(&self) -> bool {
        match self.peek() {
            T::Keyword(Kw::Function | Kw::Fn) => true,
            T::Keyword(Kw::Static) => matches!(self.nth(1), T::Keyword(Kw::Function | Kw::Fn)),
            _ => false,
        }
    }

    fn parse_attributed_decl(&mut self, doc: Option<std::sync::Arc<str>>) -> StmtKind {
        let attrs = self.parse_attributes();
        match self.peek() {
            T::Keyword(Kw::Function) if self.is_function_decl() => {
                StmtKind::Function(self.parse_function_decl(attrs, doc))
            }
            T::Keyword(Kw::Abstract | Kw::Final | Kw::Class | Kw::Interface | Kw::Trait) => {
                StmtKind::Class(self.parse_class_like(attrs, doc))
            }
            T::Keyword(Kw::Readonly) if self.readonly_starts_class() => {
                StmtKind::Class(self.parse_class_like(attrs, doc))
            }
            T::Keyword(Kw::Enum) if self.nth(1) == T::Identifier => {
                StmtKind::Class(self.parse_class_like(attrs, doc))
            }
            T::Keyword(Kw::Const) => {
                let consts = self.parse_const_elems();
                self.eat_stmt_end();
                StmtKind::ConstDecl { consts, attrs }
            }
            _ => {
                // Attributes on an expression (e.g. a closure) — parse the expr;
                // the attributes are not yet attached to expression nodes. Only
                // a closure or arrow function may carry them, so anything else
                // (`#[A] new Foo();`) is the parse error PHP reports, not a
                // silent drop.
                if !self.at_attributable_closure() {
                    self.error_here(MISPLACED_ATTRIBUTE);
                }
                let e = self.parse_expr(0);
                self.eat_stmt_end();
                StmtKind::Expr(e)
            }
        }
    }

    fn parse_attributes(&mut self) -> Vec<AttributeGroup> {
        let mut groups = Vec::new();
        while self.at(T::Attribute) {
            self.bump(); // `#[`
            let mut attrs = Vec::new();
            while !self.at(T::RBracket) && !self.at_eof() {
                let name = self.parse_name();
                let args = if self.at(T::LParen) {
                    Some(self.parse_args())
                } else {
                    None
                };
                attrs.push(Attribute { name, args });
                if !self.eat(T::Comma) {
                    break;
                }
            }
            self.expect(T::RBracket, "`]`");
            groups.push(AttributeGroup { attrs });
        }
        groups
    }

    fn parse_function_decl(
        &mut self,
        attrs: Vec<AttributeGroup>,
        doc: Option<std::sync::Arc<str>>,
    ) -> FunctionDecl {
        self.bump(); // function
        let by_ref = self.eat_amp();
        let (name, name_span) = self.member_ident_spanned();
        let params = self.parse_param_list();
        let return_type = if self.eat(T::Colon) {
            Some(self.parse_type())
        } else {
            None
        };
        let body = self.parse_brace_block();
        FunctionDecl {
            attrs,
            doc,
            name,
            name_span,
            by_ref,
            params,
            return_type,
            body,
        }
    }

    fn parse_param_list(&mut self) -> Vec<Param> {
        self.expect(T::LParen, "`(`");
        let mut params = Vec::new();
        while !self.at(T::RParen) && !self.at_eof() {
            params.push(self.parse_param());
            if !self.eat(T::Comma) {
                break;
            }
        }
        self.expect(T::RParen, "`)`");
        params
    }

    fn parse_param(&mut self) -> Param {
        let start = self.cur_start();
        let attrs = self.parse_attributes();
        let modifiers = self.parse_modifiers();
        let ty = if matches!(
            self.peek(),
            T::Variable | T::Ellipsis | T::AmpFollowedByVar | T::AmpNotFollowedByVar
        ) {
            None
        } else {
            Some(self.parse_type())
        };
        let by_ref = self.eat_amp();
        let variadic = self.eat(T::Ellipsis);
        let name = if self.at(T::Variable) {
            let t = self.bump();
            self.intern_var(t)
        } else {
            self.error_here("expected parameter variable");
            self.interner.intern("")
        };
        let default = if self.eat(T::Eq) {
            Some(self.parse_expr(0))
        } else {
            None
        };
        // Promoted property with hooks: `public $x { get => …; }`.
        let hooks = if self.at(T::LBrace) {
            self.parse_property_hooks()
        } else {
            Vec::new()
        };
        Param {
            span: self.span_to(start),
            attrs,
            modifiers,
            ty,
            by_ref,
            variadic,
            name,
            default,
            hooks,
        }
    }

    fn parse_modifiers(&mut self) -> Modifiers {
        let mut m = Modifiers::default();
        loop {
            match self.peek() {
                T::Keyword(Kw::Public) => m.visibility = Some(Visibility::Public),
                T::Keyword(Kw::Protected) => m.visibility = Some(Visibility::Protected),
                T::Keyword(Kw::Private) => m.visibility = Some(Visibility::Private),
                T::PublicSet => m.set_visibility = Some(Visibility::Public),
                T::ProtectedSet => m.set_visibility = Some(Visibility::Protected),
                T::PrivateSet => m.set_visibility = Some(Visibility::Private),
                T::Keyword(Kw::Static) => m.is_static = true,
                T::Keyword(Kw::Abstract) => m.is_abstract = true,
                T::Keyword(Kw::Final) => m.is_final = true,
                T::Keyword(Kw::Readonly) => m.is_readonly = true,
                _ => break,
            }
            self.bump();
        }
        m
    }

    fn parse_const_elems(&mut self) -> Vec<ConstElem> {
        self.bump(); // const
        let mut elems = Vec::new();
        loop {
            let (name, name_span) = self.member_ident_spanned();
            self.expect(T::Eq, "`=`");
            let value = self.parse_expr(0);
            elems.push(ConstElem {
                name,
                name_span,
                value,
            });
            if !self.eat(T::Comma) {
                break;
            }
        }
        elems
    }

    fn name_list(&mut self) -> Vec<Name> {
        let mut v = vec![self.parse_name()];
        while self.eat(T::Comma) {
            v.push(self.parse_name());
        }
        v
    }

    fn parse_class_like(
        &mut self,
        attrs: Vec<AttributeGroup>,
        doc: Option<std::sync::Arc<str>>,
    ) -> ClassDecl {
        let modifiers = self.parse_modifiers();
        let kind = match self.peek() {
            T::Keyword(Kw::Class) => ClassKind::Class,
            T::Keyword(Kw::Interface) => ClassKind::Interface,
            T::Keyword(Kw::Trait) => ClassKind::Trait,
            T::Keyword(Kw::Enum) => ClassKind::Enum,
            _ => {
                self.error_here("expected `class`, `interface`, `trait` or `enum`");
                ClassKind::Class
            }
        };
        self.bump();
        let (n, name_span) = self.member_ident_spanned();
        let name = Some(n);
        let backing = if kind == ClassKind::Enum && self.eat(T::Colon) {
            Some(self.parse_type())
        } else {
            None
        };
        let extends = if self.eat(T::Keyword(Kw::Extends)) {
            self.name_list()
        } else {
            Vec::new()
        };
        let implements = if self.eat(T::Keyword(Kw::Implements)) {
            self.name_list()
        } else {
            Vec::new()
        };
        let members = self.parse_class_body();
        ClassDecl {
            attrs,
            doc,
            kind,
            name,
            name_span,
            modifiers,
            extends,
            implements,
            backing,
            members,
        }
    }

    fn parse_class_body(&mut self) -> Vec<Member> {
        self.expect(T::LBrace, "`{`");
        let mut members = Vec::new();
        while !self.at(T::RBrace) && !self.at_eof() {
            let before = self.pos;
            let mstart = self.cur_start();
            let doc = self.doc_before(mstart);
            let attrs = self.parse_attributes();
            members.push(self.parse_member(attrs, doc));
            self.ensure_progress(before);
        }
        self.expect(T::RBrace, "`}`");
        members
    }

    fn parse_member(
        &mut self,
        attrs: Vec<AttributeGroup>,
        doc: Option<std::sync::Arc<str>>,
    ) -> Member {
        // `var` is a legacy public-property marker.
        if self.at(T::Keyword(Kw::Var)) {
            self.bump();
            let m = Modifiers {
                visibility: Some(Visibility::Public),
                ..Default::default()
            };
            return Member::Property(self.parse_property(attrs, doc, m));
        }
        let modifiers = self.parse_modifiers();
        match self.peek() {
            T::Keyword(Kw::Const) => {
                self.bump();
                // Optional const type (typed class constants).
                let ty = if matches!(self.peek(), T::Identifier | T::Keyword(_))
                    && self.nth(1) == T::Eq
                {
                    None
                } else {
                    Some(self.parse_type())
                };
                let mut consts = Vec::new();
                loop {
                    let (name, name_span) = self.member_ident_spanned();
                    self.expect(T::Eq, "`=`");
                    let value = self.parse_expr(0);
                    consts.push(ConstElem {
                        name,
                        name_span,
                        value,
                    });
                    if !self.eat(T::Comma) {
                        break;
                    }
                }
                self.eat_stmt_end();
                Member::ClassConst(ClassConstDecl {
                    attrs,
                    doc,
                    modifiers,
                    ty,
                    consts,
                })
            }
            T::Keyword(Kw::Function) => {
                self.bump();
                let by_ref = self.eat_amp();
                let (name, name_span) = self.member_ident_spanned();
                let params = self.parse_param_list();
                let return_type = if self.eat(T::Colon) {
                    Some(self.parse_type())
                } else {
                    None
                };
                let body = if self.at(T::LBrace) {
                    Some(self.parse_brace_block())
                } else {
                    self.eat_stmt_end(); // abstract / interface method
                    None
                };
                Member::Method(MethodDecl {
                    attrs,
                    doc,
                    modifiers,
                    by_ref,
                    name,
                    name_span,
                    params,
                    return_type,
                    body,
                })
            }
            T::Keyword(Kw::Case) => {
                self.bump();
                let (name, name_span) = self.member_ident_spanned();
                let value = if self.eat(T::Eq) {
                    Some(self.parse_expr(0))
                } else {
                    None
                };
                self.eat_stmt_end();
                Member::EnumCase(EnumCaseDecl {
                    attrs,
                    doc,
                    name,
                    name_span,
                    value,
                })
            }
            T::Keyword(Kw::Use) => {
                self.bump();
                let traits = self.name_list();
                let adaptations = if self.at(T::LBrace) {
                    self.parse_trait_adaptations()
                } else {
                    self.eat_stmt_end();
                    Vec::new()
                };
                Member::TraitUse(TraitUseDecl {
                    traits,
                    adaptations,
                })
            }
            _ => Member::Property(self.parse_property(attrs, doc, modifiers)),
        }
    }

    fn parse_property(
        &mut self,
        attrs: Vec<AttributeGroup>,
        doc: Option<std::sync::Arc<str>>,
        modifiers: Modifiers,
    ) -> PropertyDecl {
        let ty = if self.at(T::Variable) {
            None
        } else {
            Some(self.parse_type())
        };
        let mut props = Vec::new();
        let mut hooked = false;
        loop {
            let name_start = self.cur_start();
            let name = if self.at(T::Variable) {
                let t = self.bump();
                self.intern_var(t)
            } else {
                self.error_here("expected property variable");
                self.interner.intern("")
            };
            let name_span = self.span_to(name_start);
            let default = if self.eat(T::Eq) {
                Some(self.parse_expr(0))
            } else {
                None
            };
            // A hook block (`{ … }`, possibly empty) makes this a hooked property.
            let hooks = if self.at(T::LBrace) {
                hooked = true;
                Some(self.parse_property_hooks())
            } else {
                None
            };
            props.push(PropElem {
                name,
                name_span,
                default,
                hooks,
            });
            // A hooked property is a single declaration (no comma list).
            if hooked || !self.eat(T::Comma) {
                break;
            }
        }
        if !hooked {
            self.eat_stmt_end();
        }
        PropertyDecl {
            attrs,
            doc,
            modifiers,
            ty,
            props,
        }
    }

    /// `{ get …; set …; }` — property hooks.
    fn parse_property_hooks(&mut self) -> Vec<PropertyHook> {
        self.expect(T::LBrace, "`{`");
        let mut hooks = Vec::new();
        while !self.at(T::RBrace) && !self.at_eof() {
            let before = self.pos;
            let hstart = self.cur_start();
            let doc = self.doc_before(hstart);
            let attrs = self.parse_attributes();
            let modifiers = self.parse_modifiers();
            let by_ref = self.eat_amp();
            let (name, name_span) = self.member_ident_spanned();
            let params = if self.at(T::LParen) {
                Some(self.parse_param_list())
            } else {
                None
            };
            let body = if self.eat(T::Semicolon) {
                HookBody::Abstract
            } else if self.eat(T::DoubleArrow) {
                let e = self.parse_expr(0);
                self.eat_stmt_end();
                HookBody::Short(e)
            } else if self.at(T::LBrace) {
                HookBody::Block(self.parse_brace_block())
            } else {
                self.error_here("expected hook body");
                HookBody::Abstract
            };
            hooks.push(PropertyHook {
                attrs,
                doc,
                modifiers,
                by_ref,
                name,
                name_span,
                params,
                body,
            });
            self.ensure_progress(before);
        }
        self.expect(T::RBrace, "`}`");
        hooks
    }

    /// `{ A::foo insteadof B; bar as baz; }` — trait adaptations.
    fn parse_trait_adaptations(&mut self) -> Vec<TraitAdaptation> {
        self.expect(T::LBrace, "`{`");
        let mut out = Vec::new();
        while !self.at(T::RBrace) && !self.at_eof() {
            let before = self.pos;
            // A method reference: `Class::method` or a bare `method`.
            let first = self.parse_name();
            let (class, method) = if self.eat(T::DoubleColon) {
                (Some(first), self.member_ident())
            } else {
                (None, self.interner.intern(&first.text))
            };
            if self.eat(T::Keyword(Kw::Insteadof)) {
                let insteadof = self.name_list();
                let class = class.unwrap_or(Name {
                    span: Span::at(self.cur_start()),
                    fq: NameFq::NotFq,
                    text: String::new(),
                });
                out.push(TraitAdaptation::Precedence {
                    class,
                    method,
                    insteadof,
                });
            } else if self.eat(T::Keyword(Kw::As)) {
                // `as` may be followed by member modifiers (visibility, `final`,
                // …) and/or a new name.
                let modifiers = self.parse_modifiers();
                let alias = if matches!(self.peek(), T::Identifier | T::Keyword(_)) {
                    let t = self.bump();
                    Some(self.intern_tok(t))
                } else {
                    None
                };
                out.push(TraitAdaptation::Alias {
                    class,
                    method,
                    modifiers,
                    alias,
                });
            } else {
                self.error_here("expected `insteadof` or `as`");
            }
            self.eat(T::Semicolon);
            self.ensure_progress(before);
        }
        self.expect(T::RBrace, "`}`");
        out
    }

    // --- types ------------------------------------------------------------

    fn parse_type(&mut self) -> Type {
        let start = self.cur_start();
        if self.eat(T::Question) {
            let inner = self.parse_type_unit();
            return Type {
                span: self.span_to(start),
                kind: TypeKind::Nullable(Box::new(inner)),
            };
        }
        let first = self.parse_type_unit();
        if self.at(T::Pipe) {
            let mut parts = vec![first];
            while self.eat(T::Pipe) {
                parts.push(self.parse_type_unit());
            }
            Type {
                span: self.span_to(start),
                kind: TypeKind::Union(parts),
            }
        } else if self.at(T::AmpNotFollowedByVar) {
            let mut parts = vec![first];
            while self.eat(T::AmpNotFollowedByVar) {
                parts.push(self.parse_type_unit());
            }
            Type {
                span: self.span_to(start),
                kind: TypeKind::Intersection(parts),
            }
        } else {
            first
        }
    }

    /// A single type, or a parenthesized intersection (for DNF types).
    fn parse_type_unit(&mut self) -> Type {
        let start = self.cur_start();
        if self.eat(T::LParen) {
            let mut parts = vec![self.parse_type_name()];
            while self.eat(T::AmpNotFollowedByVar) {
                parts.push(self.parse_type_name());
            }
            self.expect(T::RParen, "`)`");
            return Type {
                span: self.span_to(start),
                kind: TypeKind::Intersection(parts),
            };
        }
        self.parse_type_name()
    }

    fn parse_type_name(&mut self) -> Type {
        let start = self.cur_start();
        let name = self.parse_type_simple_name();
        Type {
            span: self.span_to(start),
            kind: TypeKind::Simple(name),
        }
    }

    // --- closures / arrow functions / anonymous classes -------------------

    fn parse_closure(&mut self, start: u32, is_static: bool, attrs: Vec<AttributeGroup>) -> Expr {
        self.bump(); // function
        let by_ref = self.eat_amp();
        let params = self.parse_param_list();
        let mut uses = Vec::new();
        if self.eat(T::Keyword(Kw::Use)) {
            self.expect(T::LParen, "`(`");
            while !self.at(T::RParen) && !self.at_eof() {
                let by_ref = self.eat_amp();
                let name = if self.at(T::Variable) {
                    let t = self.bump();
                    self.intern_var(t)
                } else {
                    self.error_here("expected captured variable");
                    self.interner.intern("")
                };
                uses.push(ClosureUse { name, by_ref });
                if !self.eat(T::Comma) {
                    break;
                }
            }
            self.expect(T::RParen, "`)`");
        }
        let return_type = if self.eat(T::Colon) {
            Some(self.parse_type())
        } else {
            None
        };
        let body = self.parse_brace_block();
        self.node(
            start,
            ExprKind::Closure(Box::new(ClosureExpr {
                attrs,
                is_static,
                by_ref,
                params,
                uses,
                return_type,
                body,
            })),
        )
    }

    fn parse_arrow(&mut self, start: u32, is_static: bool, attrs: Vec<AttributeGroup>) -> Expr {
        self.bump(); // fn
        let by_ref = self.eat_amp();
        let params = self.parse_param_list();
        let return_type = if self.eat(T::Colon) {
            Some(self.parse_type())
        } else {
            None
        };
        self.expect(T::DoubleArrow, "`=>`");
        let body = self.parse_expr(0);
        self.node(
            start,
            ExprKind::ArrowFn(Box::new(ArrowFn {
                attrs,
                is_static,
                by_ref,
                params,
                return_type,
                body: Box::new(body),
            })),
        )
    }

    /// Lookahead: optional class modifiers followed by `class`.
    fn is_anon_class_ahead(&self) -> bool {
        let mut k = 0;
        while matches!(
            self.nth(k),
            T::Keyword(Kw::Readonly | Kw::Abstract | Kw::Final)
        ) {
            k += 1;
        }
        self.nth(k) == T::Keyword(Kw::Class)
    }

    fn parse_anon_class(
        &mut self,
        start: u32,
        attrs: Vec<AttributeGroup>,
        modifiers: Modifiers,
    ) -> Expr {
        let name_span = self.bump().span; // `class` keyword — the anon class's anchor
        let args = if self.at(T::LParen) {
            self.parse_args()
        } else {
            Vec::new()
        };
        let extends = if self.eat(T::Keyword(Kw::Extends)) {
            vec![self.parse_name()]
        } else {
            Vec::new()
        };
        let implements = if self.eat(T::Keyword(Kw::Implements)) {
            self.name_list()
        } else {
            Vec::new()
        };
        let members = self.parse_class_body();
        let class = ClassDecl {
            attrs,
            doc: None,
            kind: ClassKind::Class,
            name: None,
            name_span,
            modifiers,
            extends,
            implements,
            backing: None,
            members,
        };
        self.node(
            start,
            ExprKind::NewAnon {
                class: Box::new(class),
                args,
            },
        )
    }

    fn at_stmt_end(&self) -> bool {
        matches!(self.peek(), T::Semicolon | T::CloseTag | T::Eof)
    }

    /// Consume a statement terminator: `;`, or an implicit `?>`/EOF.
    fn eat_stmt_end(&mut self) {
        if self.eat(T::Semicolon) || matches!(self.peek(), T::CloseTag | T::Eof) {
            return;
        }
        self.error_here("expected `;`");
        self.synchronize();
    }

    /// Error recovery: skip to the next statement boundary.
    fn synchronize(&mut self) {
        while !self.at_eof() {
            if self.eat(T::Semicolon) {
                return;
            }
            if matches!(self.peek(), T::CloseTag | T::RBrace) {
                return;
            }
            self.bump();
        }
    }

    fn parse_expr_list(&mut self) -> Vec<Expr> {
        let mut v = vec![self.parse_expr(0)];
        while self.eat(T::Comma) {
            if self.at_stmt_end() {
                break;
            }
            v.push(self.parse_expr(0));
        }
        v
    }

    // --- expressions (Pratt) ---------------------------------------------

    fn parse_expr(&mut self, min_bp: u8) -> Expr {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            self.depth -= 1;
            return self.too_deep();
        }
        let mut lhs = self.parse_prefix();
        loop {
            let k = self.peek();
            let Some((lbp, rbp)) = infix_power(k) else {
                break;
            };
            if lbp <= min_bp {
                break;
            }
            lhs = self.parse_infix(lhs, k, rbp);
        }
        self.depth -= 1;
        lhs
    }

    /// Bail out of over-deep nesting: emit a diagnostic, consume one token to
    /// guarantee forward progress, and return an error node.
    fn too_deep(&mut self) -> Expr {
        let start = self.cur_start();
        self.error_here("nesting level too deep");
        if !self.at_eof() {
            self.bump();
        }
        self.node(start, ExprKind::Error)
    }

    fn parse_infix(&mut self, lhs: Expr, k: T, rbp: u8) -> Expr {
        let start = lhs.span.start;
        match k {
            T::Question => self.parse_ternary(lhs),
            T::Coalesce => {
                self.bump();
                let rhs = self.parse_expr(rbp);
                self.node(
                    start,
                    ExprKind::Coalesce {
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    },
                )
            }
            T::Keyword(Kw::Instanceof) => {
                self.bump();
                let class = self.parse_class_ref();
                self.node(
                    start,
                    ExprKind::Instanceof {
                        expr: Box::new(lhs),
                        class: Box::new(class),
                    },
                )
            }
            T::Eq => {
                self.bump();
                if self.eat_amp() {
                    // `=&` binds a *variable* reference, not a full expression:
                    // `$a = &$b + $c` is `($a = &$b) + $c`. Parse the RHS above
                    // all binary operators so only the variable (+ postfixes) is
                    // taken.
                    let rhs = self.parse_expr(BP_REF_RHS);
                    self.node(
                        start,
                        ExprKind::AssignRef {
                            target: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
                    )
                } else {
                    let rhs = self.parse_expr(rbp);
                    self.node(
                        start,
                        ExprKind::Assign {
                            target: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
                    )
                }
            }
            _ => {
                if let Some(op) = compound_assign_op(k) {
                    self.bump();
                    let rhs = self.parse_expr(rbp);
                    return self.node(
                        start,
                        ExprKind::AssignOp {
                            op,
                            target: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
                    );
                }
                let op = binop_of(k).expect("infix_power covers this token");
                self.bump();
                let rhs = self.parse_expr(rbp);
                self.node(
                    start,
                    ExprKind::Binary {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    },
                )
            }
        }
    }

    fn parse_ternary(&mut self, cond: Expr) -> Expr {
        let start = cond.span.start;
        self.bump(); // `?`
        if self.eat(T::Colon) {
            let els = self.parse_expr(BP_TERNARY_RHS);
            return self.node(
                start,
                ExprKind::Ternary {
                    cond: Box::new(cond),
                    then: None,
                    els: Box::new(els),
                },
            );
        }
        let then = self.parse_expr(0);
        self.expect(T::Colon, "`:`");
        let els = self.parse_expr(BP_TERNARY_RHS);
        self.node(
            start,
            ExprKind::Ternary {
                cond: Box::new(cond),
                then: Some(Box::new(then)),
                els: Box::new(els),
            },
        )
    }

    fn parse_prefix(&mut self) -> Expr {
        let start = self.cur_start();
        let e = match self.peek() {
            T::Int => {
                let t = self.bump();
                self.node(start, ExprKind::Int(parse_int(self.text(t))))
            }
            T::Float => {
                let t = self.bump();
                self.node(start, ExprKind::Float(parse_float(self.text(t))))
            }
            T::String => {
                let t = self.bump();
                self.node(
                    start,
                    ExprKind::Str(literals::decode_string_literal(self.text(t))),
                )
            }
            T::DoubleQuote => self.parse_interp(T::DoubleQuote),
            T::Backtick => self.parse_interp(T::Backtick),
            T::StartHeredoc => self.parse_heredoc(),
            T::Variable => {
                let t = self.bump();
                let s = self.intern_var(t);
                self.node(start, ExprKind::Variable(s))
            }
            T::Dollar => self.parse_variable_variable(),
            T::Identifier | T::NameQualified | T::NameFullyQualified | T::NameRelative => {
                self.parse_name_expr()
            }
            T::LParen => {
                self.bump();
                let inner = self.parse_expr(0);
                self.expect(T::RParen, "`)`");
                Expr::new(self.span_to(start), ExprKind::Paren(Box::new(inner)))
            }
            T::LBracket => self.parse_array(T::RBracket),
            T::Plus => self.parse_unary(UnOp::Plus, BP_UNARY2),
            T::Minus => self.parse_unary(UnOp::Minus, BP_UNARY2),
            T::Tilde => self.parse_unary(UnOp::BitNot, BP_UNARY2),
            T::Bang => self.parse_unary(UnOp::Not, BP_NOT),
            T::At => {
                self.bump();
                let e = self.parse_expr(BP_UNARY2);
                self.node(start, ExprKind::ErrorSuppress(Box::new(e)))
            }
            T::Inc => {
                self.bump();
                let e = self.parse_expr(BP_UNARY2);
                self.node(start, ExprKind::PreInc(Box::new(e)))
            }
            T::Dec => {
                self.bump();
                let e = self.parse_expr(BP_UNARY2);
                self.node(start, ExprKind::PreDec(Box::new(e)))
            }
            T::YieldFrom => {
                self.bump();
                let e = self.parse_expr(BP_YIELD);
                self.node(start, ExprKind::YieldFrom(Box::new(e)))
            }
            k if cast_kind(k).is_some() => {
                self.bump();
                let e = self.parse_expr(BP_UNARY2);
                self.node(
                    start,
                    ExprKind::Cast {
                        kind: cast_kind(k).unwrap(),
                        expr: Box::new(e),
                    },
                )
            }
            T::Keyword(kw) => return self.parse_keyword_prefix(kw, start),
            // Attributes in expression position decorate a closure / arrow fn.
            T::Attribute => {
                let attrs = self.parse_attributes();
                match self.peek() {
                    T::Keyword(Kw::Function) => self.parse_closure(start, false, attrs),
                    T::Keyword(Kw::Fn) => self.parse_arrow(start, false, attrs),
                    T::Keyword(Kw::Static) if self.nth(1) == T::Keyword(Kw::Function) => {
                        self.bump();
                        self.parse_closure(start, true, attrs)
                    }
                    T::Keyword(Kw::Static) if self.nth(1) == T::Keyword(Kw::Fn) => {
                        self.bump();
                        self.parse_arrow(start, true, attrs)
                    }
                    // PHP allows an attribute here only on a closure or an
                    // arrow function (and, via `parse_new`, an anonymous class).
                    // Anywhere else is a parse error, so say so — silently
                    // dropping the attributes accepted invalid code *and* left
                    // an attribute in the source with no trace in the AST.
                    _ => {
                        self.error_here(MISPLACED_ATTRIBUTE);
                        self.parse_prefix()
                    }
                }
            }
            _ => {
                self.error_here("unexpected token in expression");
                self.bump();
                self.node(start, ExprKind::Error)
            }
        };
        self.parse_postfix(e)
    }

    fn parse_unary(&mut self, op: UnOp, operand_bp: u8) -> Expr {
        let start = self.cur_start();
        self.bump();
        let e = self.parse_expr(operand_bp);
        self.node(
            start,
            ExprKind::Unary {
                op,
                expr: Box::new(e),
            },
        )
    }

    fn parse_keyword_prefix(&mut self, kw: Kw, start: u32) -> Expr {
        let e = match kw {
            Kw::Array => self.parse_array_call(ArraySyntax::Long),
            Kw::List => self.parse_array_call(ArraySyntax::List),
            Kw::New => self.parse_new(start),
            Kw::Clone => {
                self.bump();
                // PHP 8.5 clone-with-args uses call syntax only for `clone()`,
                // multiple/named/spread/placeholder args (`clone($a, $b)`,
                // `clone(...)`). A single `clone(EXPR)` is the clone *construct*
                // over a parenthesized operand — and that operand can continue
                // with postfixes (`clone (new C)->x` is `clone ((new C)->x)`).
                if self.at(T::LParen) && self.clone_uses_call_syntax() {
                    let args = self.parse_args();
                    let callee = Expr::new(
                        Span::at(start),
                        ExprKind::Name(Name {
                            span: Span::at(start),
                            fq: NameFq::Fq,
                            text: "clone".into(),
                        }),
                    );
                    self.node(
                        start,
                        ExprKind::Call {
                            callee: Box::new(callee),
                            args,
                        },
                    )
                } else {
                    let e = self.parse_expr(BP_CLONE);
                    self.node(start, ExprKind::Clone(Box::new(e)))
                }
            }
            Kw::Print => {
                self.bump();
                let e = self.parse_expr(BP_PRINT);
                self.node(start, ExprKind::Print(Box::new(e)))
            }
            Kw::Throw => {
                self.bump();
                let e = self.parse_expr(BP_THROW);
                self.node(start, ExprKind::Throw(Box::new(e)))
            }
            Kw::Exit => self.parse_exit(start),
            Kw::Yield => self.parse_yield(start),
            Kw::Match => self.parse_match(start),
            Kw::Include => self.parse_include(start, IncludeKind::Include),
            Kw::IncludeOnce => self.parse_include(start, IncludeKind::IncludeOnce),
            Kw::Require => self.parse_include(start, IncludeKind::Require),
            Kw::RequireOnce => self.parse_include(start, IncludeKind::RequireOnce),
            Kw::Eval => {
                self.bump();
                self.expect(T::LParen, "`(`");
                let e = self.parse_expr(0);
                self.expect(T::RParen, "`)`");
                self.node(start, ExprKind::Eval(Box::new(e)))
            }
            Kw::Isset => {
                self.bump();
                self.expect(T::LParen, "`(`");
                let vars = self.parse_call_like_exprs();
                self.expect(T::RParen, "`)`");
                self.node(start, ExprKind::Isset(vars))
            }
            Kw::Empty => {
                self.bump();
                self.expect(T::LParen, "`(`");
                let e = self.parse_expr(0);
                self.expect(T::RParen, "`)`");
                self.node(start, ExprKind::Empty(Box::new(e)))
            }
            Kw::Function => self.parse_closure(start, false, Vec::new()),
            Kw::Fn => self.parse_arrow(start, false, Vec::new()),
            Kw::Static if self.nth(1) == T::Keyword(Kw::Function) => {
                self.bump(); // static
                self.parse_closure(start, true, Vec::new())
            }
            Kw::Static if self.nth(1) == T::Keyword(Kw::Fn) => {
                self.bump(); // static
                self.parse_arrow(start, true, Vec::new())
            }
            Kw::Static => {
                let t = self.bump();
                self.node(
                    start,
                    ExprKind::Name(Name {
                        span: t.span,
                        fq: NameFq::NotFq,
                        text: self.text(t).to_string(),
                    }),
                )
            }
            // `readonly` is usable as a function name (PHP grammar's dedicated
            // `T_READONLY '(' ... )` rule), which builds an unflagged NAME.
            Kw::Readonly => {
                let t = self.bump();
                self.node(
                    start,
                    ExprKind::Name(Name {
                        span: t.span,
                        fq: NameFq::Fq,
                        text: self.text(t).to_string(),
                    }),
                )
            }
            // Magic constants (`__LINE__`, `__DIR__`, …). Represented as plain
            // names for now; a dedicated node can come with const resolution.
            Kw::Line
            | Kw::File
            | Kw::Dir
            | Kw::ClassC
            | Kw::TraitC
            | Kw::MethodC
            | Kw::FuncC
            | Kw::PropertyC
            | Kw::NsC => {
                let t = self.bump();
                self.node(
                    start,
                    ExprKind::Name(Name {
                        span: t.span,
                        fq: NameFq::NotFq,
                        text: self.text(t).to_string(),
                    }),
                )
            }
            _ => {
                // Deferred to later milestones (closures `function`/`fn`,
                // anonymous classes). Recover by consuming the keyword.
                self.error_here("expression form not yet supported");
                self.bump();
                self.node(start, ExprKind::Error)
            }
        };
        self.parse_postfix(e)
    }

    fn parse_include(&mut self, start: u32, kind: IncludeKind) -> Expr {
        self.bump();
        // `include`/`require` are very low precedence: `include $a or $b` binds
        // the whole `$a or $b` as the operand.
        let e = self.parse_expr(BP_INCLUDE);
        self.node(
            start,
            ExprKind::Include {
                kind,
                expr: Box::new(e),
            },
        )
    }

    fn parse_match(&mut self, start: u32) -> Expr {
        self.bump(); // match
        self.expect(T::LParen, "`(`");
        let subject = self.parse_expr(0);
        self.expect(T::RParen, "`)`");
        self.expect(T::LBrace, "`{`");
        let mut arms = Vec::new();
        while !self.at(T::RBrace) && !self.at_eof() {
            let conds = if self.eat(T::Keyword(Kw::Default)) {
                self.eat(T::Comma); // optional `default,` before `=>`
                None
            } else {
                let mut cs = vec![self.parse_expr(0)];
                while self.eat(T::Comma) {
                    if self.at(T::DoubleArrow) {
                        break;
                    }
                    cs.push(self.parse_expr(0));
                }
                Some(cs)
            };
            self.expect(T::DoubleArrow, "`=>`");
            let body = self.parse_expr(0);
            arms.push(MatchArm { conds, body });
            if !self.eat(T::Comma) {
                break;
            }
        }
        self.expect(T::RBrace, "`}`");
        self.node(
            start,
            ExprKind::Match {
                subject: Box::new(subject),
                arms,
            },
        )
    }

    /// With `self.pos` at the `(` after `clone`, decide whether it is the
    /// clone-with-args *call* form rather than `clone (parenthesized-expr)`.
    /// Call form: empty `()`, a named first arg (`(x: …)`), or a top-level `,`
    /// or `...` before the matching `)`.
    fn clone_uses_call_syntax(&self) -> bool {
        if self.nth(1) == T::RParen {
            return true; // clone()
        }
        if matches!(self.nth(1), T::Identifier | T::Keyword(_)) && self.nth(2) == T::Colon {
            return true; // clone(name: …)
        }
        let mut depth = 0u32;
        let mut k = 0;
        loop {
            match self.nth(k) {
                // `#[` is an opening bracket closed by a plain `]`; without
                // counting it, an attribute before the first top-level comma
                // (`clone(#[A] fn() => 1, $x)`) makes the scan hit `depth == 1`
                // on the attribute's own `]` and misread the call as a
                // construct.
                T::LParen | T::LBracket | T::LBrace | T::Attribute => depth += 1,
                T::RParen | T::RBracket | T::RBrace => {
                    if depth == 1 {
                        return false; // matching `)` with a single, comma-less expr
                    }
                    depth -= 1;
                }
                T::Comma | T::Ellipsis if depth == 1 => return true,
                T::Eof => return false,
                _ => {}
            }
            k += 1;
        }
    }

    fn parse_exit(&mut self, start: u32) -> Expr {
        self.bump(); // exit / die
        if self.at(T::LParen) {
            // `exit(...)` is a first-class callable to the `exit` function.
            if self.nth(1) == T::Ellipsis && self.nth(2) == T::RParen {
                let args = self.parse_args();
                let callee = Expr::new(
                    Span::at(start),
                    ExprKind::Name(Name {
                        span: Span::at(start),
                        fq: NameFq::Fq,
                        text: "exit".into(),
                    }),
                );
                return self.node(
                    start,
                    ExprKind::Call {
                        callee: Box::new(callee),
                        args,
                    },
                );
            }
            self.bump(); // `(`
            let arg = if self.at(T::RParen) {
                None
            } else {
                Some(Box::new(self.parse_expr(0)))
            };
            self.expect(T::RParen, "`)`");
            self.node(start, ExprKind::Exit(arg))
        } else {
            self.node(start, ExprKind::Exit(None))
        }
    }

    fn parse_yield(&mut self, start: u32) -> Expr {
        self.bump(); // yield
                     // `yield` has no operand when followed by a terminator, or by an infix
                     // operator that cannot also start an expression (so `yield * -1` parses
                     // as `(yield) * -1`, while `yield +1` yields `+1`).
        // `Colon` and `DoubleArrow` terminate too: neither can start an
        // expression, and neither carries an infix power. They appear after a
        // bare `yield` in `$a ? yield : 2`, `[yield => 1]` and `case yield:`
        // — the keyed `yield $k => $v` form is only reached once an operand has
        // parsed, so it is unaffected.
        let no_operand = matches!(
            self.peek(),
            T::Semicolon
                | T::RParen
                | T::RBracket
                | T::RBrace
                | T::CloseTag
                | T::Eof
                | T::Comma
                | T::Colon
                | T::DoubleArrow
        ) || (infix_power(self.peek()).is_some()
            && !matches!(self.peek(), T::Plus | T::Minus));
        if no_operand {
            return self.node(
                start,
                ExprKind::Yield {
                    key: None,
                    value: None,
                },
            );
        }
        let first = self.parse_expr(BP_YIELD);
        if self.eat(T::DoubleArrow) {
            let value = self.parse_expr(BP_YIELD);
            self.node(
                start,
                ExprKind::Yield {
                    key: Some(Box::new(first)),
                    value: Some(Box::new(value)),
                },
            )
        } else {
            self.node(
                start,
                ExprKind::Yield {
                    key: None,
                    value: Some(Box::new(first)),
                },
            )
        }
    }

    fn parse_name_expr(&mut self) -> Expr {
        let start = self.cur_start();
        let name = self.parse_expr_name();
        self.node(start, ExprKind::Name(name))
    }

    fn parse_variable_variable(&mut self) -> Expr {
        let start = self.cur_start();
        self.bump(); // `$`
        let inner = match self.peek() {
            T::LBrace => {
                self.bump();
                let e = self.parse_expr(0);
                self.expect(T::RBrace, "`}`");
                e
            }
            T::Variable => {
                let t = self.bump();
                let s = self.intern_var(t);
                self.node(t.span.start, ExprKind::Variable(s))
            }
            T::Dollar => self.parse_variable_variable(),
            _ => {
                self.error_here("expected variable name after `$`");
                self.node(start, ExprKind::Error)
            }
        };
        self.node(start, ExprKind::VariableVariable(Box::new(inner)))
    }

    // --- postfix (call / index / member / :: / ++ / --) -------------------

    fn parse_postfix(&mut self, mut e: Expr) -> Expr {
        let start = e.span.start;
        loop {
            e = match self.peek() {
                T::LParen => {
                    let args = self.parse_args();
                    self.node(
                        start,
                        ExprKind::Call {
                            callee: Box::new(e),
                            args,
                        },
                    )
                }
                T::LBracket => {
                    self.bump();
                    let index = if self.at(T::RBracket) {
                        None
                    } else {
                        Some(Box::new(self.parse_expr(0)))
                    };
                    self.expect(T::RBracket, "`]`");
                    self.node(
                        start,
                        ExprKind::Index {
                            base: Box::new(e),
                            index,
                        },
                    )
                }
                T::Arrow | T::NullsafeArrow => {
                    let nullsafe = self.peek() == T::NullsafeArrow;
                    self.bump();
                    let name = self.parse_member_name();
                    if self.at(T::LParen) {
                        let args = self.parse_args();
                        self.node(
                            start,
                            ExprKind::MethodCall {
                                recv: Box::new(e),
                                nullsafe,
                                method: name,
                                args,
                            },
                        )
                    } else {
                        self.node(
                            start,
                            ExprKind::Prop {
                                base: Box::new(e),
                                nullsafe,
                                name,
                            },
                        )
                    }
                }
                T::DoubleColon => self.parse_static_access(e, start),
                T::Inc => {
                    self.bump();
                    self.node(start, ExprKind::PostInc(Box::new(e)))
                }
                T::Dec => {
                    self.bump();
                    self.node(start, ExprKind::PostDec(Box::new(e)))
                }
                _ => break,
            };
        }
        e
    }

    /// After `::`, parse the `$`-led variable form of a static-member name
    /// (`$$x`, `${expr}`). The leading `$` denotes "property"; the result is the
    /// inner name expression (so `Foo::$$x`'s name is the `$x` expression).
    fn parse_static_prop_name(&mut self) -> Expr {
        let start = self.cur_start();
        self.bump(); // leading `$`
        match self.peek() {
            T::LBrace => {
                self.bump();
                let e = self.parse_expr(0);
                self.expect(T::RBrace, "`}`");
                e
            }
            T::Variable => {
                let t = self.bump();
                let s = self.intern_var(t);
                self.node(t.span.start, ExprKind::Variable(s))
            }
            T::Dollar => self.parse_variable_variable(),
            _ => {
                self.error_here("expected variable name after `$`");
                self.node(start, ExprKind::Error)
            }
        }
    }

    fn parse_static_access(&mut self, class: Expr, start: u32) -> Expr {
        self.bump(); // `::`
        let Some(target) = self.parse_static_member_name("expected member name after `::`") else {
            return self.node(start, ExprKind::Error);
        };
        match target {
            StaticMemberName::Property(name) => {
                if self.at(T::LParen) {
                    let args = self.parse_args();
                    self.node(
                        start,
                        ExprKind::StaticCall {
                            class: Box::new(class),
                            method: name,
                            args,
                        },
                    )
                } else {
                    self.node(
                        start,
                        ExprKind::StaticProp {
                            class: Box::new(class),
                            name,
                        },
                    )
                }
            }
            StaticMemberName::DollarExpr { dollar, inner } => {
                if self.at(T::LParen) {
                    // Spanned from the `$`: using `start` would make this node
                    // cover `Class::` too, mis-anchoring diagnostics and giving
                    // it a span that overlaps the whole static call.
                    let m = self.node(dollar, ExprKind::VariableVariable(Box::new(inner)));
                    let name = MemberName::Expr(Box::new(m));
                    let args = self.parse_args();
                    self.node(
                        start,
                        ExprKind::StaticCall {
                            class: Box::new(class),
                            method: name,
                            args,
                        },
                    )
                } else {
                    let name = MemberName::Expr(Box::new(inner));
                    self.node(
                        start,
                        ExprKind::StaticProp {
                            class: Box::new(class),
                            name,
                        },
                    )
                }
            }
            StaticMemberName::ConstOrMethod(name) => {
                if self.at(T::LParen) {
                    let args = self.parse_args();
                    self.node(
                        start,
                        ExprKind::StaticCall {
                            class: Box::new(class),
                            method: name,
                            args,
                        },
                    )
                } else {
                    self.node(
                        start,
                        ExprKind::ClassConst {
                            class: Box::new(class),
                            name,
                        },
                    )
                }
            }
        }
    }

    fn parse_member_name(&mut self) -> MemberName {
        match self.peek() {
            T::Identifier | T::Keyword(_) => self.parse_ident_member_name(),
            T::Variable => self.parse_variable_member_name(),
            T::LBrace => {
                self.bump();
                let e = self.parse_expr(0);
                self.expect(T::RBrace, "`}`");
                MemberName::Expr(Box::new(e))
            }
            T::Dollar => {
                let e = self.parse_variable_variable();
                MemberName::Expr(Box::new(e))
            }
            _ => {
                self.error_here("expected member name");
                MemberName::Ident(self.interner.intern(""))
            }
        }
    }

    fn parse_ident_member_name(&mut self) -> MemberName {
        let t = self.bump();
        MemberName::Ident(self.intern_tok(t))
    }

    fn parse_variable_member_name(&mut self) -> MemberName {
        let t = self.bump();
        MemberName::Var(self.intern_var(t))
    }

    fn parse_braced_member_name(&mut self) -> MemberName {
        self.bump();
        let e = self.parse_expr(0);
        self.expect(T::RBrace, "`}`");
        MemberName::Expr(Box::new(e))
    }

    fn parse_static_member_name(&mut self, error: &str) -> Option<StaticMemberName> {
        match self.peek() {
            T::Variable => Some(StaticMemberName::Property(
                self.parse_variable_member_name(),
            )),
            T::Dollar => {
                let dollar = self.cur_start();
                Some(StaticMemberName::DollarExpr {
                    dollar,
                    inner: self.parse_static_prop_name(),
                })
            }
            T::LBrace => Some(StaticMemberName::ConstOrMethod(
                self.parse_braced_member_name(),
            )),
            T::Identifier | T::Keyword(_) => Some(StaticMemberName::ConstOrMethod(
                self.parse_ident_member_name(),
            )),
            _ => {
                self.error_here(error);
                None
            }
        }
    }

    // --- arguments & arrays ----------------------------------------------

    fn parse_args(&mut self) -> Vec<Arg> {
        self.expect(T::LParen, "`(`");
        let mut args = Vec::new();
        // First-class callable syntax `f(...)`.
        if self.at(T::Ellipsis) && self.nth(1) == T::RParen {
            let astart = self.cur_start();
            self.bump();
            self.bump();
            args.push(Arg {
                span: self.span_to(astart),
                name: None,
                value: Expr::new(self.span_to(astart), ExprKind::CallablePlaceholder),
                spread: false,
                placeholder: true,
            });
            return args;
        }
        while !self.at(T::RParen) && !self.at_eof() {
            let astart = self.cur_start();
            let name = if matches!(self.peek(), T::Identifier | T::Keyword(_))
                && self.nth(1) == T::Colon
            {
                let t = self.bump();
                self.bump(); // `:`
                Some(self.intern_tok(t))
            } else {
                None
            };
            let spread = self.eat(T::Ellipsis);
            let value = self.parse_expr(0);
            args.push(Arg {
                span: self.span_to(astart),
                name,
                value,
                spread,
                placeholder: false,
            });
            if !self.eat(T::Comma) {
                break;
            }
        }
        self.expect(T::RParen, "`)`");
        args
    }

    fn parse_array_call(&mut self, syntax: ArraySyntax) -> Expr {
        // `array` or `list` keyword already current.
        let start = self.cur_start();
        self.bump(); // array / list
        self.expect(T::LParen, "`(`");
        let items = self.parse_array_items(T::RParen);
        self.expect(T::RParen, "`)`");
        self.node(start, ExprKind::Array { items, syntax })
    }

    fn parse_array(&mut self, close: T) -> Expr {
        // `[` already current (short array syntax).
        let start = self.cur_start();
        self.bump(); // `[`
        let items = self.parse_array_items(close);
        self.expect(close, "`]`");
        self.node(
            start,
            ExprKind::Array {
                items,
                syntax: ArraySyntax::Short,
            },
        )
    }

    fn parse_array_items(&mut self, close: T) -> Vec<ArrayItem> {
        let mut items = Vec::new();
        while !self.at(close) && !self.at_eof() {
            let istart = self.cur_start();
            // Elision in destructuring: `[, $x]`.
            if self.at(T::Comma) {
                items.push(ArrayItem {
                    span: Span::at(istart),
                    key: None,
                    value: None,
                    by_ref: false,
                    spread: false,
                });
                self.bump();
                continue;
            }
            if self.eat(T::Ellipsis) {
                let value = self.parse_expr(0);
                items.push(ArrayItem {
                    span: self.span_to(istart),
                    key: None,
                    value: Some(value),
                    by_ref: false,
                    spread: true,
                });
            } else if self.eat_amp() {
                let value = self.parse_expr(0);
                items.push(ArrayItem {
                    span: self.span_to(istart),
                    key: None,
                    value: Some(value),
                    by_ref: true,
                    spread: false,
                });
            } else {
                let first = self.parse_expr(0);
                if self.eat(T::DoubleArrow) {
                    let by_ref = self.eat_amp();
                    let value = self.parse_expr(0);
                    items.push(ArrayItem {
                        span: self.span_to(istart),
                        key: Some(first),
                        value: Some(value),
                        by_ref,
                        spread: false,
                    });
                } else {
                    items.push(ArrayItem {
                        span: self.span_to(istart),
                        key: None,
                        value: Some(first),
                        by_ref: false,
                        spread: false,
                    });
                }
            }
            if !self.eat(T::Comma) {
                break;
            }
        }
        items
    }

    // --- `new` ------------------------------------------------------------

    fn parse_new(&mut self, start: u32) -> Expr {
        self.bump(); // new
                     // `new #[Attr] readonly class {...}` — attributes/modifiers on an
                     // anonymous class.
        let attrs = self.parse_attributes();
        // `new [modifiers] class { … }` — anonymous class. Modifiers like
        // `final`/duplicate `readonly` are accepted syntactically; their
        // validity is a later semantic check (matching PHP).
        if self.is_anon_class_ahead() {
            let modifiers = self.parse_modifiers();
            return self.parse_anon_class(start, attrs, modifiers);
        }
        // `new #[A] Foo()` is a parse error in PHP: an attribute after `new`
        // belongs to an anonymous class and nothing else. Report it rather than
        // dropping the attributes on the floor.
        if !attrs.is_empty() {
            self.error_here("attributes are only allowed on an anonymous class here");
        }
        let class = self.parse_class_ref();
        let args = if self.at(T::LParen) {
            self.parse_args()
        } else {
            Vec::new()
        };
        self.node(
            start,
            ExprKind::New {
                class: Box::new(class),
                args,
            },
        )
    }

    /// A class-name reference (for `new`, `instanceof`): a name, a variable, a
    /// parenthesized expression, or `static`, with member/index access but no
    /// call (parentheses there are constructor arguments).
    fn parse_class_ref(&mut self) -> Expr {
        let start = self.cur_start();
        let mut e = match self.peek() {
            T::Identifier | T::NameQualified | T::NameFullyQualified | T::NameRelative => {
                self.parse_name_expr()
            }
            T::Keyword(Kw::Static) => {
                let t = self.bump();
                self.node(
                    start,
                    ExprKind::Name(Name {
                        span: t.span,
                        fq: NameFq::NotFq,
                        text: self.text(t).to_string(),
                    }),
                )
            }
            T::Variable => {
                let t = self.bump();
                let s = self.intern_var(t);
                self.node(start, ExprKind::Variable(s))
            }
            T::Dollar => self.parse_variable_variable(),
            T::LParen => {
                // `new (expr)` — keep the parens: a bare name inside is a
                // constant fetch (`new (FOO)` instantiates the class named by the
                // constant FOO), not a class name.
                self.bump();
                let inner = self.parse_expr(0);
                self.expect(T::RParen, "`)`");
                self.node(start, ExprKind::Paren(Box::new(inner)))
            }
            _ => {
                self.error_here("expected class name");
                self.node(start, ExprKind::Error)
            }
        };
        loop {
            e = match self.peek() {
                T::Arrow | T::NullsafeArrow => {
                    let nullsafe = self.peek() == T::NullsafeArrow;
                    self.bump();
                    let name = self.parse_member_name();
                    self.node(
                        start,
                        ExprKind::Prop {
                            base: Box::new(e),
                            nullsafe,
                            name,
                        },
                    )
                }
                T::DoubleColon => {
                    self.bump();
                    match self.parse_static_member_name("expected member after `::`") {
                        Some(StaticMemberName::Property(name)) => self.node(
                            start,
                            ExprKind::StaticProp {
                                class: Box::new(e),
                                name,
                            },
                        ),
                        Some(StaticMemberName::DollarExpr { inner, .. }) => self.node(
                            start,
                            ExprKind::StaticProp {
                                class: Box::new(e),
                                name: MemberName::Expr(Box::new(inner)),
                            },
                        ),
                        Some(StaticMemberName::ConstOrMethod(name)) => self.node(
                            start,
                            ExprKind::ClassConst {
                                class: Box::new(e),
                                name,
                            },
                        ),
                        None => {
                            let name = MemberName::Ident(self.interner.intern(""));
                            self.node(
                                start,
                                ExprKind::ClassConst {
                                    class: Box::new(e),
                                    name,
                                },
                            )
                        }
                    }
                }
                T::LBracket => {
                    self.bump();
                    let index = if self.at(T::RBracket) {
                        None
                    } else {
                        Some(Box::new(self.parse_expr(0)))
                    };
                    self.expect(T::RBracket, "`]`");
                    self.node(
                        start,
                        ExprKind::Index {
                            base: Box::new(e),
                            index,
                        },
                    )
                }
                _ => break,
            };
        }
        e
    }

    // --- interpolation ----------------------------------------------------

    fn parse_interp(&mut self, delim: T) -> Expr {
        let start = self.cur_start();
        self.bump(); // opening `"` or backtick
        let parts = self.parse_interp_parts(delim, false);
        self.expect(delim, "closing string delimiter");
        if delim == T::Backtick {
            self.node(start, ExprKind::ShellExec(parts))
        } else {
            self.node(start, ExprKind::Interpolated(parts))
        }
    }

    fn parse_heredoc(&mut self) -> Expr {
        let start = self.cur_start();
        let open = self.bump(); // T_START_HEREDOC
                                // A nowdoc opener quotes its label (`<<<'EOT'`); its body is taken
                                // verbatim with no escape processing.
        let nowdoc = self.text(open).contains('\'');
        let mut parts = self.parse_interp_parts(T::EndHeredoc, nowdoc);
        // The closing marker's leading whitespace is stripped from every body
        // line (flexible heredoc/nowdoc, PHP 7.3+).
        let indent = if self.at(T::EndHeredoc) {
            let t = self.text(self.tokens[self.pos]);
            t.bytes().take_while(|b| matches!(b, b' ' | b'\t')).count()
        } else {
            0
        };
        self.expect(T::EndHeredoc, "heredoc end marker");
        literals::normalize_heredoc_parts(&mut parts, indent);
        // PHP collapses a purely-literal heredoc/nowdoc to a plain string.
        match parts.len() {
            0 => self.node(start, ExprKind::Str(Vec::new())),
            1 if matches!(parts[0].kind, ExprKind::Str(_)) => {
                let s = match parts.pop().unwrap().kind {
                    ExprKind::Str(s) => s,
                    _ => unreachable!(),
                };
                self.node(start, ExprKind::Str(s))
            }
            _ => self.node(start, ExprKind::Interpolated(parts)),
        }
    }

    fn parse_interp_parts(&mut self, close: T, raw: bool) -> Vec<Expr> {
        // The delimiter-specific escapable quote: `\"` in double-quotes, `` \` ``
        // in backticks, none in heredoc (no closing quote inside the body).
        let quote = match close {
            T::Backtick => Some(b'`'),
            T::EndHeredoc => None,
            _ => Some(b'"'),
        };
        let mut parts = Vec::new();
        while !self.at(close) && !self.at_eof() {
            match self.peek() {
                T::EncapsedAndWhitespace => {
                    let t = self.bump();
                    // Nowdoc bodies are literal; everything else applies
                    // double-quote escape rules.
                    let s = if raw {
                        self.text(t).as_bytes().to_vec()
                    } else {
                        literals::decode_double(self.text(t), quote)
                    };
                    parts.push(self.node(t.span.start, ExprKind::Str(s)));
                }
                T::Variable => parts.push(self.parse_simple_interp_var()),
                T::CurlyOpen => {
                    self.bump();
                    let e = self.parse_expr(0);
                    self.expect(T::RBrace, "`}`");
                    parts.push(e);
                }
                T::DollarOpenCurly => parts.push(self.parse_dollar_curly()),
                _ => break,
            }
        }
        parts
    }

    fn parse_simple_interp_var(&mut self) -> Expr {
        let start = self.cur_start();
        let t = self.bump(); // Variable
        let s = self.intern_var(t);
        let var = self.node(start, ExprKind::Variable(s));
        match self.peek() {
            T::Arrow | T::NullsafeArrow => {
                let nullsafe = self.peek() == T::NullsafeArrow;
                self.bump();
                let nt = self.bump(); // Identifier
                let name = MemberName::Ident(self.intern_tok(nt));
                self.node(
                    start,
                    ExprKind::Prop {
                        base: Box::new(var),
                        nullsafe,
                        name,
                    },
                )
            }
            T::LBracket => {
                self.bump();
                let index = self.parse_interp_offset();
                self.expect(T::RBracket, "`]`");
                self.node(
                    start,
                    ExprKind::Index {
                        base: Box::new(var),
                        index: Some(Box::new(index)),
                    },
                )
            }
            _ => var,
        }
    }

    /// A simple-interpolation offset (`"$a[X]"`) is an integer only when `X` is a
    /// canonical integer string (round-trips through i64); `-0`, `00`, `0x0`, and
    /// out-of-range values stay strings.
    fn interp_offset_node(&self, start: u32, txt: String) -> Expr {
        match literals::canonical_int_key(&txt) {
            Some(n) => self.node(start, ExprKind::Int(n)),
            None => self.node(start, ExprKind::Str(txt.into_bytes())),
        }
    }

    fn parse_interp_offset(&mut self) -> Expr {
        let start = self.cur_start();
        match self.peek() {
            T::NumString => {
                let t = self.bump();
                let txt = self.text(t).to_string();
                self.interp_offset_node(start, txt)
            }
            T::Identifier => {
                let t = self.bump();
                self.node(start, ExprKind::Str(self.text(t).as_bytes().to_vec()))
            }
            T::Variable => {
                let t = self.bump();
                let s = self.intern_var(t);
                self.node(start, ExprKind::Variable(s))
            }
            T::Minus => {
                self.bump();
                let t = self.bump(); // NumString
                let txt = self.text(t).to_string();
                // PHP parses the positive magnitude first; `-0` and a magnitude
                // that overflows i64 (even if its negation would fit) stay strings.
                match literals::canonical_int_key(&txt) {
                    Some(n) if n != 0 => self.node(start, ExprKind::Int(-n)),
                    _ => self.node(start, ExprKind::Str(format!("-{txt}").into_bytes())),
                }
            }
            _ => {
                self.error_here("invalid offset in string interpolation");
                self.node(start, ExprKind::Error)
            }
        }
    }

    fn parse_dollar_curly(&mut self) -> Expr {
        let start = self.cur_start();
        self.bump(); // `${`
        let e = if self.at(T::StringVarname) {
            let t = self.bump();
            let s = self.interner.intern(self.text(t));
            // The variable spans just its name: sharing `start` with the
            // enclosing `DollarBrace` would make the two collide in span-keyed
            // maps (see `php_span::NodeKey`).
            let var = Expr::new(t.span, ExprKind::Variable(s));
            let inner = if self.eat(T::LBracket) {
                let index = self.parse_expr(0);
                self.expect(T::RBracket, "`]`");
                self.node(
                    start,
                    ExprKind::Index {
                        base: Box::new(var),
                        index: Some(Box::new(index)),
                    },
                )
            } else {
                var
            };
            // Closing brace consumed first so the wrapper's span covers `${…}`
            // and is therefore strictly wider than its child's — two nodes with
            // byte-identical spans are indistinguishable to span-keyed maps.
            self.expect(T::RBrace, "`}`");
            self.node(start, ExprKind::DollarBrace(Box::new(inner)))
        } else {
            // The general `${ expr }` form. Wrap in DollarBrace so interpolation
            // can flag it VAR#2 — but only when it is a *direct* `${…}` part, not
            // a `${…}` nested inside a `{…}` complex interpolation.
            let inner = self.parse_expr(0);
            let vv = self.node(start, ExprKind::VariableVariable(Box::new(inner)));
            self.expect(T::RBrace, "`}`");
            self.node(start, ExprKind::DollarBrace(Box::new(vv)))
        };
        e
    }
}

// ---------------------------------------------------------------------------
// Precedence (transcribed from zend_language_parser.y, lines ~53–87).
// Higher binding power binds tighter. Left-assoc: (lbp, lbp+1); right-assoc:
// (lbp, lbp-1). Prefix operands use the bare bps below.
// ---------------------------------------------------------------------------

const BP_THROW: u8 = 2;
const BP_INCLUDE: u8 = 3; // below `or`/`and` so they bind into the operand
const BP_PRINT: u8 = 10;
const BP_YIELD: u8 = 10;
const BP_NOT: u8 = 42; // `!`
const BP_UNARY2: u8 = 46; // `~`, casts, `@`, unary `+`/`-`
const BP_CLONE: u8 = 50;
const BP_REF_RHS: u8 = 50; // `=&` RHS: a variable, above all binary operators
const BP_TERNARY_RHS: u8 = 14; // `?:`/`?:` is left-associative (matches `%left '?' ':'`)

fn infix_power(k: T) -> Option<(u8, u8)> {
    operator_info(k).map(|op| (op.lbp, op.rbp))
}

fn binop_of(k: T) -> Option<BinOp> {
    operator_info(k).and_then(|op| op.binop)
}

fn compound_assign_op(k: T) -> Option<BinOp> {
    operator_info(k).and_then(|op| op.compound_assign)
}

#[derive(Debug, Clone, Copy)]
struct OperatorInfo {
    lbp: u8,
    rbp: u8,
    binop: Option<BinOp>,
    compound_assign: Option<BinOp>,
}

impl OperatorInfo {
    const fn special(lbp: u8, rbp: u8) -> Self {
        Self {
            lbp,
            rbp,
            binop: None,
            compound_assign: None,
        }
    }

    const fn binary(lbp: u8, rbp: u8, binop: BinOp) -> Self {
        Self {
            lbp,
            rbp,
            binop: Some(binop),
            compound_assign: None,
        }
    }

    const fn compound(binop: BinOp) -> Self {
        // Right-assoc; high left-bp so assignment binds to the immediate lvalue,
        // low right-bp so the RHS still captures binary operators.
        Self {
            lbp: 51,
            rbp: 11,
            binop: None,
            compound_assign: Some(binop),
        }
    }
}

fn operator_info(k: T) -> Option<OperatorInfo> {
    Some(match k {
        T::Keyword(Kw::LogicalOr) => OperatorInfo::binary(4, 5, BinOp::LogicalOr),
        T::Keyword(Kw::LogicalXor) => OperatorInfo::binary(6, 7, BinOp::LogicalXor),
        T::Keyword(Kw::LogicalAnd) => OperatorInfo::binary(8, 9, BinOp::LogicalAnd),
        T::Eq => OperatorInfo::special(51, 11),
        T::PlusEq => OperatorInfo::compound(BinOp::Add),
        T::MinusEq => OperatorInfo::compound(BinOp::Sub),
        T::MulEq => OperatorInfo::compound(BinOp::Mul),
        T::DivEq => OperatorInfo::compound(BinOp::Div),
        T::ModEq => OperatorInfo::compound(BinOp::Mod),
        T::PowEq => OperatorInfo::compound(BinOp::Pow),
        T::ConcatEq => OperatorInfo::compound(BinOp::Concat),
        T::AndEq => OperatorInfo::compound(BinOp::BitAnd),
        T::OrEq => OperatorInfo::compound(BinOp::BitOr),
        T::XorEq => OperatorInfo::compound(BinOp::BitXor),
        T::SlEq => OperatorInfo::compound(BinOp::Shl),
        T::SrEq => OperatorInfo::compound(BinOp::Shr),
        T::CoalesceEq => OperatorInfo::compound(BinOp::Coalesce),
        T::Question => OperatorInfo::special(14, 13),
        T::Coalesce => OperatorInfo::special(16, 15),
        T::BoolOr => OperatorInfo::binary(18, 19, BinOp::BoolOr),
        T::BoolAnd => OperatorInfo::binary(20, 21, BinOp::BoolAnd),
        T::Pipe => OperatorInfo::binary(22, 23, BinOp::BitOr),
        T::Caret => OperatorInfo::binary(24, 25, BinOp::BitXor),
        T::AmpFollowedByVar | T::AmpNotFollowedByVar => OperatorInfo::binary(26, 27, BinOp::BitAnd),
        T::IsEqual => OperatorInfo::binary(28, 29, BinOp::Eq),
        T::IsNotEqual => OperatorInfo::binary(28, 29, BinOp::NotEq),
        T::IsIdentical => OperatorInfo::binary(28, 29, BinOp::Identical),
        T::IsNotIdentical => OperatorInfo::binary(28, 29, BinOp::NotIdentical),
        T::Spaceship => OperatorInfo::binary(28, 29, BinOp::Spaceship),
        T::Lt => OperatorInfo::binary(30, 31, BinOp::Lt),
        T::LtEq => OperatorInfo::binary(30, 31, BinOp::LtEq),
        T::Gt => OperatorInfo::binary(30, 31, BinOp::Gt),
        T::GtEq => OperatorInfo::binary(30, 31, BinOp::GtEq),
        T::PipeOp => OperatorInfo::binary(32, 33, BinOp::Pipe),
        T::Dot => OperatorInfo::binary(34, 35, BinOp::Concat),
        T::Sl => OperatorInfo::binary(36, 37, BinOp::Shl),
        T::Sr => OperatorInfo::binary(36, 37, BinOp::Shr),
        T::Plus => OperatorInfo::binary(38, 39, BinOp::Add),
        T::Minus => OperatorInfo::binary(38, 39, BinOp::Sub),
        T::Star => OperatorInfo::binary(40, 41, BinOp::Mul),
        T::Slash => OperatorInfo::binary(40, 41, BinOp::Div),
        T::Percent => OperatorInfo::binary(40, 41, BinOp::Mod),
        T::Keyword(Kw::Instanceof) => OperatorInfo::special(44, 45),
        T::Pow => OperatorInfo::binary(48, 47, BinOp::Pow),
        _ => return None,
    })
}

fn cast_kind(k: T) -> Option<CastKind> {
    Some(match k {
        T::IntCast => CastKind::Int,
        T::DoubleCast => CastKind::Float,
        T::StringCast => CastKind::String,
        T::ArrayCast => CastKind::Array,
        T::ObjectCast => CastKind::Object,
        T::BoolCast => CastKind::Bool,
        T::UnsetCast => CastKind::Unset,
        T::VoidCast => CastKind::Void,
        _ => return None,
    })
}

// --- literal value decoding ------------------------------------------------

/// Reported where PHP rejects an attribute outright, so the attribute is never
/// just dropped: invalid source stayed silent, and the AST then claimed nothing
/// had been written.
const MISPLACED_ATTRIBUTE: &str =
    "attributes are not allowed here (only on a closure, arrow function or anonymous class)";

fn stmt_allows_raw_doc(kind: &StmtKind) -> bool {
    !matches!(kind, StmtKind::Function(_) | StmtKind::Class(_))
}

/// Whether `gap` holds nothing but whitespace and plain comments — what PHP
/// allows between a doc-comment and the declaration it documents.
///
/// Anything else (including `#[`, a close tag, or an unterminated block
/// comment) means real content intervened, so the docblock is not attached.
fn gap_is_trivia(gap: &str) -> bool {
    let b = gap.as_bytes();
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b' ' | b'\t' | b'\r' | b'\n' => i += 1,
            // `#[` opens an attribute — code, not a comment.
            b'#' if b.get(i + 1) != Some(&b'[') => i = line_comment_end(b, i + 1),
            b'/' if b.get(i + 1) == Some(&b'/') => i = line_comment_end(b, i + 2),
            b'/' if b.get(i + 1) == Some(&b'*') => match gap[i + 2..].find("*/") {
                Some(rel) => i += 2 + rel + 2,
                None => return false,
            },
            _ => return false,
        }
    }
    true
}

/// One past the end of a line comment whose body starts at `from`.
///
/// A line comment stops at the newline, or before a `?>` close tag — which the
/// caller then rejects, since leaving PHP is not trivia.
fn line_comment_end(b: &[u8], from: usize) -> usize {
    let mut i = from;
    while i < b.len() {
        match b[i] {
            b'\n' => return i + 1,
            b'?' if b.get(i + 1) == Some(&b'>') => return i,
            _ => i += 1,
        }
    }
    i
}

fn parse_int(text: &str) -> i64 {
    php_lexer::number::parse_int_literal(text)
}

fn parse_float(text: &str) -> f64 {
    php_lexer::number::parse_float_literal(text)
}
