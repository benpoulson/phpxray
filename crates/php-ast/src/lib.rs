//! The PHP abstract syntax tree.
//!
//! A typed, tooling-friendly AST (in the spirit of nikic/PHP-Parser), **not** a
//! mirror of Zend's bit-packed compiler AST. Pattern matching on the `*Kind`
//! enums gives compiler-enforced exhaustiveness, which the analysis phases rely
//! on heavily.
//!
//! ## Conventions
//!
//! * Every node is a `struct { span: Span, kind: SomeKind }`. The span is a byte
//!   range into the original source; line/column are derived on demand via
//!   `php_span::LineIndex`, never stored here.
//! * Parse errors are explicit [`StmtKind::Error`] / [`ExprKind::Error`] nodes
//!   rather than aborting, so a tree always exists.
//! * Names are interned ([`php_intern::Symbol`]); literal values are decoded onto
//!   the node where cheap (ints/floats); string contents are kept raw for now.
//!
//! Grows across milestones M4–M8. M4 covers the expression core (full operator
//! precedence, primaries, calls/access) and a statement skeleton. Closures, arrow
//! functions, `match`, anonymous classes, `list()` destructuring, generators and
//! declarations arrive in later milestones.

use php_intern::Symbol;
use php_span::Span;

pub mod walk;

/// A whole parsed source unit.
#[derive(Clone, PartialEq, Debug)]
pub struct Program {
    pub stmts: Vec<Stmt>,
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Debug)]
pub struct Stmt {
    pub span: Span,
    pub kind: StmtKind,
}

impl Stmt {
    pub fn new(span: Span, kind: StmtKind) -> Stmt {
        Stmt { span, kind }
    }
}

#[derive(Clone, PartialEq, Debug)]
#[non_exhaustive]
pub enum StmtKind {
    /// An expression used as a statement (`foo();`).
    Expr(Expr),
    /// `echo $a, $b;`
    Echo(Vec<Expr>),
    /// `return;` / `return $x;`
    Return(Option<Expr>),
    /// A `{ ... }` block.
    Block(Vec<Stmt>),

    // --- control flow ---
    If {
        cond: Expr,
        then: Box<Stmt>,
        elseifs: Vec<ElseIf>,
        els: Option<Box<Stmt>>,
    },
    While {
        cond: Expr,
        body: Box<Stmt>,
    },
    DoWhile {
        body: Box<Stmt>,
        cond: Expr,
    },
    For {
        init: Vec<Expr>,
        cond: Vec<Expr>,
        update: Vec<Expr>,
        body: Box<Stmt>,
    },
    Foreach {
        subject: Expr,
        key: Option<Expr>,
        value: Expr,
        by_ref: bool,
        /// A `&` on the key (`foreach ($a as &$k => $v)`) — illegal in PHP but
        /// still parsed (PHP wraps the key in a `REF` node, then errors).
        key_by_ref: bool,
        body: Box<Stmt>,
    },
    Switch {
        subject: Expr,
        cases: Vec<SwitchCase>,
    },
    Try {
        body: Vec<Stmt>,
        catches: Vec<Catch>,
        finally: Option<Vec<Stmt>>,
    },
    Break(Option<Expr>),
    Continue(Option<Expr>),
    Goto(Symbol),
    Label(Symbol),

    // --- declarations of bindings ---
    Global(Vec<Expr>),
    StaticVars(Vec<StaticVar>),
    Unset(Vec<Expr>),
    Declare {
        directives: Vec<(Symbol, Expr)>,
        body: Option<Box<Stmt>>,
    },
    Namespace {
        name: Option<Name>,
        body: Option<Vec<Stmt>>,
    },
    Use(Vec<UseItem>),
    /// `use Prefix\{ ... }` — group use. `kind` is the optional group-level
    /// type keyword (`function`/`const`); per-element kinds live on each item.
    GroupUse {
        prefix: Name,
        kind: Option<UseKind>,
        items: Vec<UseItem>,
    },

    // --- declarations ---
    Function(FunctionDecl),
    Class(ClassDecl),
    /// Top-level `const A = 1, B = 2;`
    ConstDecl {
        consts: Vec<ConstElem>,
        attrs: Vec<AttributeGroup>,
    },

    /// `__halt_compiler();` — the byte offset where the trailing data begins.
    HaltCompiler(u32),
    /// Literal text outside `<?php ?>`.
    InlineHtml(String),
    /// An empty statement (`;`).
    Nop,
    /// A syntactically invalid statement that was recovered from.
    Error,
}

// --- declarations ----------------------------------------------------------

#[derive(Clone, PartialEq, Debug)]
pub struct FunctionDecl {
    pub attrs: Vec<AttributeGroup>,
    pub doc: Option<String>,
    pub name: Symbol,
    pub by_ref: bool,
    pub params: Vec<Param>,
    pub return_type: Option<Type>,
    pub body: Vec<Stmt>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct ClassDecl {
    pub attrs: Vec<AttributeGroup>,
    pub doc: Option<String>,
    pub kind: ClassKind,
    /// `None` for an anonymous class.
    pub name: Option<Symbol>,
    pub modifiers: Modifiers,
    /// `extends`: a class has 0–1; an interface may have many.
    pub extends: Vec<Name>,
    pub implements: Vec<Name>,
    /// Enum backing type (`enum E: int`).
    pub backing: Option<Type>,
    pub members: Vec<Member>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ClassKind {
    Class,
    Interface,
    Trait,
    Enum,
}

#[derive(Clone, PartialEq, Debug)]
pub enum Member {
    Method(MethodDecl),
    Property(PropertyDecl),
    ClassConst(ClassConstDecl),
    EnumCase(EnumCaseDecl),
    TraitUse(TraitUseDecl),
}

#[derive(Clone, PartialEq, Debug)]
pub struct MethodDecl {
    pub attrs: Vec<AttributeGroup>,
    pub doc: Option<String>,
    pub modifiers: Modifiers,
    pub by_ref: bool,
    pub name: Symbol,
    pub params: Vec<Param>,
    pub return_type: Option<Type>,
    /// `None` for abstract/interface methods.
    pub body: Option<Vec<Stmt>>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct PropertyDecl {
    pub attrs: Vec<AttributeGroup>,
    pub doc: Option<String>,
    pub modifiers: Modifiers,
    pub ty: Option<Type>,
    pub props: Vec<PropElem>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct PropElem {
    pub name: Symbol,
    pub default: Option<Expr>,
    /// Property hooks (`{ get; set { … } }`). `None` = a plain property (no
    /// brace block); `Some` = a hook block was present (possibly empty `{}`).
    pub hooks: Option<Vec<PropertyHook>>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct PropertyHook {
    pub attrs: Vec<AttributeGroup>,
    pub modifiers: Modifiers,
    /// `&get` — by-reference hook.
    pub by_ref: bool,
    /// `get` or `set`.
    pub name: Symbol,
    /// An explicit parameter list (`set(Type $v)`).
    pub params: Option<Vec<Param>>,
    pub body: HookBody,
}

#[derive(Clone, PartialEq, Debug)]
pub enum HookBody {
    /// `get;` — no body (interface / abstract).
    Abstract,
    /// `get { … }`
    Block(Vec<Stmt>),
    /// `get => expr;`
    Short(Expr),
}

#[derive(Clone, PartialEq, Debug)]
pub struct ClassConstDecl {
    pub attrs: Vec<AttributeGroup>,
    pub doc: Option<String>,
    pub modifiers: Modifiers,
    pub ty: Option<Type>,
    pub consts: Vec<ConstElem>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct ConstElem {
    pub name: Symbol,
    pub value: Expr,
}

#[derive(Clone, PartialEq, Debug)]
pub struct EnumCaseDecl {
    pub attrs: Vec<AttributeGroup>,
    pub doc: Option<String>,
    pub name: Symbol,
    pub value: Option<Expr>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct TraitUseDecl {
    pub traits: Vec<Name>,
    pub adaptations: Vec<TraitAdaptation>,
}

#[derive(Clone, PartialEq, Debug)]
pub enum TraitAdaptation {
    /// `A::foo insteadof B, C;`
    Precedence {
        class: Name,
        method: Symbol,
        insteadof: Vec<Name>,
    },
    /// `A::foo as protected bar;` / `foo as bar;` / `foo as final;`
    Alias {
        class: Option<Name>,
        method: Symbol,
        /// Modifiers applied by the alias (`public`/`protected`/`private`,
        /// `final`, …); empty for a plain rename.
        modifiers: Modifiers,
        alias: Option<Symbol>,
    },
}

#[derive(Clone, PartialEq, Debug)]
pub struct Param {
    pub attrs: Vec<AttributeGroup>,
    /// Constructor property promotion modifiers (empty for plain params).
    pub modifiers: Modifiers,
    pub ty: Option<Type>,
    pub by_ref: bool,
    pub variadic: bool,
    pub name: Symbol,
    pub default: Option<Expr>,
    /// Hooks on a promoted property param (`public $x { get => … }`).
    pub hooks: Vec<PropertyHook>,
}

/// Modifiers on a member, param-promotion, or class.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Modifiers {
    pub visibility: Option<Visibility>,
    /// Asymmetric set-visibility (`private(set)` etc.).
    pub set_visibility: Option<Visibility>,
    pub is_static: bool,
    pub is_abstract: bool,
    pub is_final: bool,
    pub is_readonly: bool,
}

impl Modifiers {
    pub fn is_empty(&self) -> bool {
        *self == Modifiers::default()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Visibility {
    Public,
    Protected,
    Private,
}

// --- closures / arrow functions (expressions) ------------------------------

#[derive(Clone, PartialEq, Debug)]
pub struct ClosureExpr {
    pub attrs: Vec<AttributeGroup>,
    pub is_static: bool,
    pub by_ref: bool,
    pub params: Vec<Param>,
    pub uses: Vec<ClosureUse>,
    pub return_type: Option<Type>,
    pub body: Vec<Stmt>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct ClosureUse {
    pub name: Symbol,
    pub by_ref: bool,
}

#[derive(Clone, PartialEq, Debug)]
pub struct ArrowFn {
    pub attrs: Vec<AttributeGroup>,
    pub is_static: bool,
    pub by_ref: bool,
    pub params: Vec<Param>,
    pub return_type: Option<Type>,
    pub body: Box<Expr>,
}

// --- attributes ------------------------------------------------------------

#[derive(Clone, PartialEq, Debug)]
pub struct AttributeGroup {
    pub attrs: Vec<Attribute>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Attribute {
    pub name: Name,
    /// `None` for `#[Attr]` (no parens); `Some` for `#[Attr(...)]`.
    pub args: Option<Vec<Arg>>,
}

// --- types -----------------------------------------------------------------

#[derive(Clone, PartialEq, Debug)]
pub struct Type {
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Clone, PartialEq, Debug)]
pub enum TypeKind {
    /// A single type name (`int`, `Foo\Bar`, `array`, `callable`, `static`, …).
    Simple(Name),
    /// `?T`
    Nullable(Box<Type>),
    /// `A|B|C` (elements may be intersections for DNF types).
    Union(Vec<Type>),
    /// `A&B&C`
    Intersection(Vec<Type>),
}

#[derive(Clone, PartialEq, Debug)]
pub struct ElseIf {
    pub cond: Expr,
    pub body: Stmt,
}

#[derive(Clone, PartialEq, Debug)]
pub struct SwitchCase {
    /// `None` for `default:`.
    pub test: Option<Expr>,
    pub body: Vec<Stmt>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Catch {
    pub types: Vec<Name>,
    pub var: Option<Symbol>,
    pub body: Vec<Stmt>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct StaticVar {
    pub name: Symbol,
    pub default: Option<Expr>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct UseItem {
    pub kind: UseKind,
    pub name: Name,
    pub alias: Option<Symbol>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UseKind {
    Class,
    Function,
    Const,
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Debug)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

impl Expr {
    pub fn new(span: Span, kind: ExprKind) -> Expr {
        Expr { span, kind }
    }
    pub fn boxed(span: Span, kind: ExprKind) -> Box<Expr> {
        Box::new(Expr { span, kind })
    }
}

#[derive(Clone, PartialEq, Debug)]
#[non_exhaustive]
pub enum ExprKind {
    // --- literals ---
    Int(i64),
    Float(f64),
    /// A string literal's decoded value. PHP strings are byte sequences (an
    /// escape like `\xff` yields a raw byte, not valid UTF-8), so this is a
    /// `Vec<u8>`, not a `String`.
    Str(Vec<u8>),
    /// An interpolated string / heredoc: literal parts ([`ExprKind::Str`])
    /// interleaved with embedded expressions.
    Interpolated(Vec<Expr>),
    /// A backtick shell-exec `` `cmd $x` ``; same parts as [`ExprKind::Interpolated`].
    ShellExec(Vec<Expr>),

    // --- references ---
    /// `$name` — the interned name without the leading `$`.
    Variable(Symbol),
    /// `$$x` / `${ expr }` — a variable whose name is computed.
    VariableVariable(Box<Expr>),
    /// The `${ bareword }` / `${ bareword[idx] }` interpolation form. Wraps the
    /// inner `Variable`/`Index`; PHP flags this distinctly only inside strings.
    DollarBrace(Box<Expr>),
    /// A bare name: a constant, or a function/class reference depending on context.
    Name(Name),

    // --- composite ---
    Array {
        items: Vec<ArrayItem>,
        syntax: ArraySyntax,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Arg>,
    },
    MethodCall {
        recv: Box<Expr>,
        nullsafe: bool,
        method: MemberName,
        args: Vec<Arg>,
    },
    StaticCall {
        class: Box<Expr>,
        method: MemberName,
        args: Vec<Arg>,
    },
    New {
        class: Box<Expr>,
        args: Vec<Arg>,
    },
    Index {
        base: Box<Expr>,
        index: Option<Box<Expr>>,
    },
    Prop {
        base: Box<Expr>,
        nullsafe: bool,
        name: MemberName,
    },
    StaticProp {
        class: Box<Expr>,
        name: MemberName,
    },
    ClassConst {
        class: Box<Expr>,
        name: MemberName,
    },

    // --- operators ---
    Unary {
        op: UnOp,
        expr: Box<Expr>,
    },
    Binary {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Assign {
        target: Box<Expr>,
        rhs: Box<Expr>,
    },
    AssignOp {
        op: BinOp,
        target: Box<Expr>,
        rhs: Box<Expr>,
    },
    AssignRef {
        target: Box<Expr>,
        rhs: Box<Expr>,
    },
    Cast {
        kind: CastKind,
        expr: Box<Expr>,
    },
    /// `c ? t : e`; `t` is `None` for the short form `c ?: e`.
    Ternary {
        cond: Box<Expr>,
        then: Option<Box<Expr>>,
        els: Box<Expr>,
    },
    Coalesce {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    PreInc(Box<Expr>),
    PreDec(Box<Expr>),
    PostInc(Box<Expr>),
    PostDec(Box<Expr>),
    Instanceof {
        expr: Box<Expr>,
        class: Box<Expr>,
    },
    Clone(Box<Expr>),
    Print(Box<Expr>),
    Throw(Box<Expr>),
    /// `@expr`
    ErrorSuppress(Box<Expr>),
    /// `yield` / `yield $v` / `yield $k => $v`
    Yield {
        key: Option<Box<Expr>>,
        value: Option<Box<Expr>>,
    },
    /// `yield from $g`
    YieldFrom(Box<Expr>),
    /// `exit` / `die` with an optional argument.
    Exit(Option<Box<Expr>>),
    /// `match (subject) { arms }`
    Match {
        subject: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    /// `include` / `require` (and their `_once` variants).
    Include {
        kind: IncludeKind,
        expr: Box<Expr>,
    },
    /// `eval(expr)`
    Eval(Box<Expr>),
    /// `isset($a, $b)`
    Isset(Vec<Expr>),
    /// `empty($x)`
    Empty(Box<Expr>),
    /// `function (...) use (...) { ... }`
    Closure(Box<ClosureExpr>),
    /// `fn (...) => expr`
    ArrowFn(Box<ArrowFn>),
    /// `new class (args) extends … { … }`
    NewAnon {
        class: Box<ClassDecl>,
        args: Vec<Arg>,
    },

    /// A parenthesized expression `( expr )`. Kept because PHP records
    /// parenthesization on a few node kinds (conditionals, arrow fns, static
    /// props) and treats a parenthesized name as a constant fetch.
    Paren(Box<Expr>),

    /// A syntactically invalid expression that was recovered from.
    Error,
}

#[derive(Clone, PartialEq, Debug)]
pub struct MatchArm {
    /// `None` for the `default` arm.
    pub conds: Option<Vec<Expr>>,
    pub body: Expr,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IncludeKind {
    Include,
    IncludeOnce,
    Require,
    RequireOnce,
}

// ---------------------------------------------------------------------------
// Supporting types
// ---------------------------------------------------------------------------

/// A (possibly qualified) name reference, stored as written (segments joined by
/// `\`). Resolution to a FQN happens in a later phase; `span` makes each
/// occurrence addressable for resolution results and diagnostics.
#[derive(Clone, PartialEq, Debug)]
pub struct Name {
    pub span: Span,
    pub fq: NameFq,
    pub text: String,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NameFq {
    /// `Foo\Bar`
    NotFq,
    /// `\Foo\Bar`
    Fq,
    /// `namespace\Foo`
    Relative,
}

/// The name in a member access (`->name`, `::name`).
#[derive(Clone, PartialEq, Debug)]
pub enum MemberName {
    /// A literal identifier (`->prop`, `::CONST`, `::class`).
    Ident(Symbol),
    /// A simple variable member (`->$prop`, `::$static`).
    Var(Symbol),
    /// A computed member (`->{expr}`, `::{expr}`).
    Expr(Box<Expr>),
}

/// A call argument.
#[derive(Clone, PartialEq, Debug)]
pub struct Arg {
    pub span: Span,
    /// `name:` for a named argument.
    pub name: Option<Symbol>,
    pub value: Expr,
    /// `...$args` spread.
    pub spread: bool,
    /// The lone `...` first-class-callable placeholder (`f(...)`).
    pub placeholder: bool,
}

/// An array element. `value` is `None` only for elision in destructuring.
#[derive(Clone, PartialEq, Debug)]
pub struct ArrayItem {
    pub span: Span,
    pub key: Option<Expr>,
    pub value: Option<Expr>,
    pub by_ref: bool,
    pub spread: bool,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnOp {
    Plus,
    Minus,
    Not,
    BitNot,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Concat,
    BitOr,
    BitAnd,
    BitXor,
    Shl,
    Shr,
    Eq,
    NotEq,
    Identical,
    NotIdentical,
    Lt,
    LtEq,
    Gt,
    GtEq,
    Spaceship,
    BoolAnd,
    BoolOr,
    LogicalAnd,
    LogicalOr,
    LogicalXor,
    Pipe,
    /// Only used by `??=` (the `??` operator itself is [`ExprKind::Coalesce`]).
    Coalesce,
}

/// How an array literal / destructuring target was written.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ArraySyntax {
    /// `list(...)`
    List,
    /// `array(...)`
    Long,
    /// `[...]`
    Short,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CastKind {
    Int,
    Float,
    String,
    Array,
    Object,
    Bool,
    Unset,
    Void,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ast_debug_snapshot() {
        let program = Program {
            stmts: vec![Stmt::new(
                Span::new(0, 4),
                StmtKind::Expr(Expr::new(Span::new(0, 3), ExprKind::Int(123))),
            )],
        };
        insta::assert_debug_snapshot!(program);
    }
}
