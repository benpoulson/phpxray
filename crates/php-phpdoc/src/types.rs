//! M-D1: the PHPDoc **type-expression grammar** — its own tokenizer + recursive
//! descent parser for the phpstan/psalm dialect.
//!
//! Grammar (low → high precedence):
//! ```text
//! type         := union
//! union        := intersection ('|' intersection)*
//! intersection := postfix      ('&' postfix)*
//! postfix      := atom ('[' ']')*                 // T[], T[][]
//! atom         := '?' atom
//!               | '(' type ')'
//!               | literal                         // 'str' | "str" | 42 | -1
//!               | name suffix?
//! suffix       := '<' type (',' type)* '>'        // generics: array<…>, int<0,100>, C<…>
//!               | '{' shape-fields '}'            // array shapes: array{id: int, …}
//!               | '(' params? ')' (':' type)?     // callables: callable(int): bool
//! ```
//! The parser never panics; malformed input yields `None` (tracked for coverage).

/// A parsed PHPDoc type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DocType {
    /// A bare name: scalar (`int`), class (`Foo\Bar`), keyword (`mixed`, `void`,
    /// `self`, `static`, `$this`, `true`, `null`), or special (`class-string`,
    /// `array-key`, `list`, …). Stored as written.
    Named(String),
    /// `?T` (shorthand for `T|null`).
    Nullable(Box<DocType>),
    /// `A|B|C`.
    Union(Vec<DocType>),
    /// `A&B`.
    Intersection(Vec<DocType>),
    /// `T[]` — array of `T` (legacy suffix syntax).
    Array(Box<DocType>),
    /// `base<args>` — generics, incl. `array<K, V>`, `list<T>`, `int<0, 100>`.
    Generic { base: String, args: Vec<DocType> },
    /// `base{fields}` — an array/object shape; `sealed` is false when it ends `…, ...`.
    Shape { base: String, fields: Vec<ShapeField>, sealed: bool },
    /// `base(params): ret` — a callable signature (`callable`/`Closure`).
    Callable { base: String, params: Vec<DocType>, ret: Option<Box<DocType>> },
    /// A literal string type (`'a'|'b'`), value without quotes.
    ConstString(String),
    /// A literal integer type (`0`, `-1`).
    ConstInt(String),
}

/// One field of an array/object shape (`key?: type`, or keyless `type`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShapeField {
    /// `None` for a keyless (list-style) field.
    pub key: Option<String>,
    pub optional: bool,
    pub ty: DocType,
}

/// Parse a complete type string. Returns `None` if it doesn't parse or has
/// trailing tokens.
pub fn parse_type(s: &str) -> Option<DocType> {
    let toks = lex(s);
    let mut p = Parser { toks, pos: 0 };
    let t = p.union()?;
    p.at(Tk::Eof).then_some(t)
}

/// Parse a *leading* type and report how many bytes it consumed — for splitting
/// `type $var description` in `@param`-style tags. `None` if no type parses.
pub fn parse_type_prefix(s: &str) -> Option<(DocType, usize)> {
    let toks = lex(s);
    let mut p = Parser { toks, pos: 0 };
    let t = p.union()?;
    // Byte offset just past the last consumed token.
    let consumed = if p.pos == 0 { 0 } else { p.toks[p.pos - 1].end };
    Some((t, consumed))
}

// --- tokenizer ---------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tk {
    Ident(String),
    Int(String),
    Str(String),
    Pipe,
    Amp,
    Question,
    Lt,
    Gt,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Colon,
    Ellipsis,
    Eof,
}

struct Tok {
    kind: Tk,
    /// Byte offset just past this token in the source.
    end: usize,
}

fn lex(s: &str) -> Vec<Tok> {
    let b = s.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    let push = |kind, end, out: &mut Vec<Tok>| out.push(Tok { kind, end });
    while i < b.len() {
        let c = b[i];
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        match c {
            b'|' => { push(Tk::Pipe, i + 1, &mut out); i += 1; }
            b'&' => { push(Tk::Amp, i + 1, &mut out); i += 1; }
            b'?' => { push(Tk::Question, i + 1, &mut out); i += 1; }
            b'<' => { push(Tk::Lt, i + 1, &mut out); i += 1; }
            b'>' => { push(Tk::Gt, i + 1, &mut out); i += 1; }
            b'(' => { push(Tk::LParen, i + 1, &mut out); i += 1; }
            b')' => { push(Tk::RParen, i + 1, &mut out); i += 1; }
            b'{' => { push(Tk::LBrace, i + 1, &mut out); i += 1; }
            b'}' => { push(Tk::RBrace, i + 1, &mut out); i += 1; }
            b'[' => { push(Tk::LBracket, i + 1, &mut out); i += 1; }
            b']' => { push(Tk::RBracket, i + 1, &mut out); i += 1; }
            b',' => { push(Tk::Comma, i + 1, &mut out); i += 1; }
            b':' => { push(Tk::Colon, i + 1, &mut out); i += 1; }
            b'.' if b[i..].starts_with(b"...") => { push(Tk::Ellipsis, i + 3, &mut out); i += 3; }
            b'\'' | b'"' => {
                let quote = c;
                let mut j = i + 1;
                while j < b.len() && b[j] != quote {
                    // Skip an escaped char.
                    j += if b[j] == b'\\' && j + 1 < b.len() { 2 } else { 1 };
                }
                let inner = s[i + 1..j.min(b.len())].to_string();
                let end = (j + 1).min(b.len());
                push(Tk::Str(inner), end, &mut out);
                i = end;
            }
            b'-' if i + 1 < b.len() && b[i + 1].is_ascii_digit() => {
                let start = i;
                i += 1;
                while i < b.len() && b[i].is_ascii_digit() {
                    i += 1;
                }
                push(Tk::Int(s[start..i].to_string()), i, &mut out);
            }
            b'0'..=b'9' => {
                let start = i;
                while i < b.len() && b[i].is_ascii_digit() {
                    i += 1;
                }
                push(Tk::Int(s[start..i].to_string()), i, &mut out);
            }
            _ if is_ident_start(c) => {
                let start = i;
                i += 1;
                while i < b.len() && is_ident_cont(b[i]) {
                    i += 1;
                }
                push(Tk::Ident(s[start..i].to_string()), i, &mut out);
            }
            // Unknown byte — stop; the parser will see whatever was collected.
            _ => break,
        }
    }
    out.push(Tok { kind: Tk::Eof, end: i });
    out
}

fn is_ident_start(c: u8) -> bool {
    c.is_ascii_alphabetic() || c == b'_' || c == b'\\' || c == b'$'
}
fn is_ident_cont(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_' || c == b'\\' || c == b'-'
}

// --- parser ------------------------------------------------------------------

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> &Tk {
        &self.toks[self.pos].kind
    }
    fn at(&self, k: Tk) -> bool {
        *self.peek() == k
    }
    fn bump(&mut self) -> Tk {
        let k = self.toks[self.pos].kind.clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        k
    }
    fn eat(&mut self, k: Tk) -> bool {
        if self.at(k) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn union(&mut self) -> Option<DocType> {
        let mut parts = vec![self.intersection()?];
        while self.eat(Tk::Pipe) {
            parts.push(self.intersection()?);
        }
        Some(if parts.len() == 1 { parts.pop().unwrap() } else { DocType::Union(parts) })
    }

    fn intersection(&mut self) -> Option<DocType> {
        let mut parts = vec![self.postfix()?];
        // `&` is intersection only when a type follows. `&$var` is a by-reference
        // marker that belongs to the param layer, not the type (the same `&`
        // ambiguity PHP's own grammar has).
        while self.at(Tk::Amp) && self.amp_is_intersection() {
            self.bump();
            parts.push(self.postfix()?);
        }
        Some(if parts.len() == 1 { parts.pop().unwrap() } else { DocType::Intersection(parts) })
    }

    /// Whether the `&` at the current position joins another type (vs. preceding
    /// a `$variable`, i.e. a by-ref marker).
    fn amp_is_intersection(&self) -> bool {
        match self.toks.get(self.pos + 1).map(|t| &t.kind) {
            Some(Tk::Ident(s)) => !s.starts_with('$'),
            Some(Tk::Question | Tk::LParen | Tk::Str(_) | Tk::Int(_)) => true,
            _ => false,
        }
    }

    fn postfix(&mut self) -> Option<DocType> {
        let mut t = self.atom()?;
        while self.at(Tk::LBracket) {
            self.bump();
            if !self.eat(Tk::RBracket) {
                return None; // `[` without `]` (offset access etc. unsupported)
            }
            t = DocType::Array(Box::new(t));
        }
        Some(t)
    }

    fn atom(&mut self) -> Option<DocType> {
        match self.peek().clone() {
            Tk::Question => {
                self.bump();
                Some(DocType::Nullable(Box::new(self.atom()?)))
            }
            Tk::LParen => {
                self.bump();
                let t = self.union()?;
                self.eat(Tk::RParen).then_some(t)
            }
            Tk::Str(s) => {
                self.bump();
                Some(DocType::ConstString(s))
            }
            Tk::Int(s) => {
                self.bump();
                Some(DocType::ConstInt(s))
            }
            Tk::Ident(name) => {
                self.bump();
                self.named_suffix(name)
            }
            _ => None,
        }
    }

    /// A name optionally followed by generics `<…>`, a shape `{…}`, or a callable
    /// signature `(…): ret`.
    fn named_suffix(&mut self, name: String) -> Option<DocType> {
        match self.peek() {
            Tk::Lt => {
                self.bump();
                let mut args = vec![self.union()?];
                while self.eat(Tk::Comma) {
                    if self.at(Tk::Gt) {
                        break; // trailing comma
                    }
                    args.push(self.union()?);
                }
                self.eat(Tk::Gt).then_some(DocType::Generic { base: name, args })
            }
            Tk::LBrace => {
                self.bump();
                self.shape(name)
            }
            Tk::LParen if is_callable(&name) => {
                self.bump();
                self.callable(name)
            }
            _ => Some(DocType::Named(name)),
        }
    }

    fn shape(&mut self, base: String) -> Option<DocType> {
        let mut fields = Vec::new();
        let mut sealed = true;
        while !self.at(Tk::RBrace) && !self.at(Tk::Eof) {
            if self.eat(Tk::Ellipsis) {
                sealed = false;
                break;
            }
            fields.push(self.shape_field()?);
            if !self.eat(Tk::Comma) {
                break;
            }
        }
        self.eat(Tk::RBrace).then_some(DocType::Shape { base, fields, sealed })
    }

    fn shape_field(&mut self) -> Option<ShapeField> {
        // Try `key (?)? :` — otherwise it's a keyless field.
        let start = self.pos;
        let key = match self.peek().clone() {
            Tk::Ident(s) | Tk::Int(s) => Some(s),
            Tk::Str(s) => Some(s),
            _ => None,
        };
        if key.is_some() {
            self.bump();
            let optional = self.eat(Tk::Question);
            if self.eat(Tk::Colon) {
                let ty = self.union()?;
                return Some(ShapeField { key, optional, ty });
            }
            self.pos = start; // not a keyed field; rewind
        }
        Some(ShapeField { key: None, optional: false, ty: self.union()? })
    }

    fn callable(&mut self, base: String) -> Option<DocType> {
        let mut params = Vec::new();
        while !self.at(Tk::RParen) && !self.at(Tk::Eof) {
            // Parameters may carry a leading `...` (variadic) or trailing `$name`;
            // we keep only the type.
            self.eat(Tk::Ellipsis);
            params.push(self.union()?);
            // Skip an optional `$name`/`=` decoration on the parameter.
            if let Tk::Ident(n) = self.peek() {
                if n.starts_with('$') {
                    self.bump();
                }
            }
            if !self.eat(Tk::Comma) {
                break;
            }
        }
        if !self.eat(Tk::RParen) {
            return None;
        }
        let ret = if self.eat(Tk::Colon) { Some(Box::new(self.union()?)) } else { None };
        Some(DocType::Callable { base, params, ret })
    }
}

fn is_callable(name: &str) -> bool {
    let n = name.trim_start_matches('\\');
    n.eq_ignore_ascii_case("callable") || n.eq_ignore_ascii_case("Closure")
}

#[cfg(test)]
mod tests {
    use super::DocType::*;
    use super::*;

    fn p(s: &str) -> DocType {
        parse_type(s).unwrap_or_else(|| panic!("failed to parse {s:?}"))
    }
    fn named(n: &str) -> DocType {
        Named(n.to_string())
    }

    #[test]
    fn scalars_and_classes() {
        assert_eq!(p("int"), named("int"));
        assert_eq!(p("Foo\\Bar"), named("Foo\\Bar"));
        assert_eq!(p("$this"), named("$this"));
        assert_eq!(p("class-string"), named("class-string"));
    }

    #[test]
    fn nullable_union_intersection() {
        assert_eq!(p("?int"), Nullable(Box::new(named("int"))));
        assert_eq!(p("int|string|null"), Union(vec![named("int"), named("string"), named("null")]));
        assert_eq!(p("A&B"), Intersection(vec![named("A"), named("B")]));
        // `&` binds tighter than `|`.
        assert_eq!(p("A&B|C"), Union(vec![Intersection(vec![named("A"), named("B")]), named("C")]));
    }

    #[test]
    fn array_suffix() {
        assert_eq!(p("int[]"), Array(Box::new(named("int"))));
        assert_eq!(p("int[][]"), Array(Box::new(Array(Box::new(named("int"))))));
        assert_eq!(p("(A|B)[]"), Array(Box::new(Union(vec![named("A"), named("B")]))));
    }

    #[test]
    fn generics() {
        assert_eq!(p("array<int>"), Generic { base: "array".into(), args: vec![named("int")] });
        assert_eq!(
            p("array<string, User>"),
            Generic { base: "array".into(), args: vec![named("string"), named("User")] }
        );
        assert_eq!(
            p("array<int, array<string>>"),
            Generic {
                base: "array".into(),
                args: vec![named("int"), Generic { base: "array".into(), args: vec![named("string")] }]
            }
        );
        assert_eq!(p("list<int>"), Generic { base: "list".into(), args: vec![named("int")] });
    }

    #[test]
    fn int_ranges_are_generics() {
        assert_eq!(
            p("int<0, 100>"),
            Generic { base: "int".into(), args: vec![ConstInt("0".into()), ConstInt("100".into())] }
        );
        assert_eq!(
            p("int<min, max>"),
            Generic { base: "int".into(), args: vec![named("min"), named("max")] }
        );
    }

    #[test]
    fn literal_unions() {
        assert_eq!(
            p("'draft'|'published'"),
            Union(vec![ConstString("draft".into()), ConstString("published".into())])
        );
        assert_eq!(p("1|2|3"), Union(vec![ConstInt("1".into()), ConstInt("2".into()), ConstInt("3".into())]));
    }

    #[test]
    fn array_shapes() {
        assert_eq!(
            p("array{id: int, name: string}"),
            Shape {
                base: "array".into(),
                sealed: true,
                fields: vec![
                    ShapeField { key: Some("id".into()), optional: false, ty: named("int") },
                    ShapeField { key: Some("name".into()), optional: false, ty: named("string") },
                ],
            }
        );
    }

    #[test]
    fn shape_optional_keyless_and_unsealed() {
        assert_eq!(
            p("array{foo?: int, string, ...}"),
            Shape {
                base: "array".into(),
                sealed: false,
                fields: vec![
                    ShapeField { key: Some("foo".into()), optional: true, ty: named("int") },
                    ShapeField { key: None, optional: false, ty: named("string") },
                ],
            }
        );
    }

    #[test]
    fn callables() {
        assert_eq!(
            p("callable(int, string): bool"),
            Callable {
                base: "callable".into(),
                params: vec![named("int"), named("string")],
                ret: Some(Box::new(named("bool"))),
            }
        );
        assert_eq!(
            p("Closure(): void"),
            Callable { base: "Closure".into(), params: vec![], ret: Some(Box::new(named("void"))) }
        );
    }

    #[test]
    fn prefix_reports_consumed_length() {
        // `@param` style: type then `$var description`.
        let (t, n) = parse_type_prefix("array<int> $items the items").unwrap();
        assert_eq!(t, Generic { base: "array".into(), args: vec![named("int")] });
        assert_eq!(&"array<int> $items the items"[n..], " $items the items");
    }

    #[test]
    fn malformed_yields_none_not_panic() {
        assert_eq!(parse_type("array<int"), None); // unclosed generic
        assert_eq!(parse_type("|int"), None); // leading pipe
        assert_eq!(parse_type(""), None);
        assert_eq!(parse_type("array{id:"), None);
    }
}
