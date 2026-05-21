//! Token kinds and their mapping to PHP's canonical `T_*` names.
//!
//! `php_name` returns exactly what `PhpToken::getTokenName()` returns for the
//! equivalent token (a `T_*` name, or the literal spelling for single-character
//! tokens), which is what the golden harness compares against.

use php_span::Span;

/// A lexed token. Text is recovered from the source via `span`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Token {
        Token { kind, span }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum TokenKind {
    // --- structural / HTML island ---
    InlineHtml,
    OpenTag,
    OpenTagEcho,
    CloseTag,
    DocComment,

    // --- literals ---
    Variable, // $name
    Int,      // T_LNUMBER
    Float,    // T_DNUMBER
    String,   // T_CONSTANT_ENCAPSED_STRING (no interpolation)

    // --- interpolation (strings, heredoc, backticks) ---
    DoubleQuote,           // a `"` delimiter around an interpolated string
    EncapsedAndWhitespace, // literal run inside an interpolated string
    NumString,             // T_NUM_STRING (an offset inside "$a[0]")
    StringVarname,         // T_STRING_VARNAME (the name inside "${name}")
    DollarOpenCurly,       // ${
    CurlyOpen,             // the `{` of {$expr}
    StartHeredoc,          // <<<LABEL\n
    EndHeredoc,            // the (optionally indented) closing LABEL

    // --- names ---
    Identifier,         // T_STRING
    NameQualified,      // A\B
    NameFullyQualified, // \A\B
    NameRelative,       // namespace\A

    Keyword(Kw),

    // --- operators & punctuation ---
    // single-character
    Eq,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Dot,
    Bang,
    Tilde,
    Caret,
    /// `&` immediately (modulo whitespace/comments) before `$` or `...` — by-ref.
    AmpFollowedByVar,
    /// `&` otherwise — bitwise-and / intersection-type. The split lets the parser
    /// disambiguate `A&$b` (by-ref param) from `A&B` (intersection type).
    AmpNotFollowedByVar,
    Pipe,
    Lt,
    Gt,
    Question,
    Colon,
    Semicolon,
    Comma,
    At,
    Dollar,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Backtick,
    NsSeparator, // a lone `\`

    // multi-character
    Pow,            // **
    Sl,             // <<
    Sr,             // >>
    Coalesce,       // ??
    Inc,            // ++
    Dec,            // --
    Arrow,          // ->
    NullsafeArrow,  // ?->
    DoubleArrow,    // =>
    DoubleColon,    // ::
    IsEqual,        // ==
    IsNotEqual,     // != or <>
    IsIdentical,    // ===
    IsNotIdentical, // !==
    LtEq,           // <=
    GtEq,           // >=
    Spaceship,      // <=>
    BoolAnd,        // &&
    BoolOr,         // ||
    PlusEq,         // +=
    MinusEq,        // -=
    MulEq,          // *=
    DivEq,          // /=
    ConcatEq,       // .=
    ModEq,          // %=
    PowEq,          // **=
    AndEq,          // &=
    OrEq,           // |=
    XorEq,          // ^=
    SlEq,           // <<=
    SrEq,           // >>=
    CoalesceEq,     // ??=
    Ellipsis,       // ...
    Attribute,      // #[
    PipeOp,         // |>

    // casts: `(int)`, `(float)`, ...
    IntCast,
    DoubleCast,
    StringCast,
    ArrayCast,
    ObjectCast,
    BoolCast,
    UnsetCast,
    VoidCast,

    YieldFrom, // `yield from`

    // asymmetric visibility (PHP 8.4): `private(set)` etc. — one fixed token.
    PrivateSet,
    ProtectedSet,
    PublicSet,

    /// Synthetic end-of-input marker (no `token_get_all` analogue).
    Eof,
    /// A byte that could not be classified.
    Unknown,
}

impl TokenKind {
    /// The canonical name used in golden fixtures. `None` for kinds with no
    /// `token_get_all()` analogue (`Eof`).
    pub fn php_name(self) -> Option<&'static str> {
        use TokenKind::*;
        Some(match self {
            InlineHtml => "T_INLINE_HTML",
            OpenTag => "T_OPEN_TAG",
            OpenTagEcho => "T_OPEN_TAG_WITH_ECHO",
            CloseTag => "T_CLOSE_TAG",
            DocComment => "T_DOC_COMMENT",

            Variable => "T_VARIABLE",
            Int => "T_LNUMBER",
            Float => "T_DNUMBER",
            String => "T_CONSTANT_ENCAPSED_STRING",

            DoubleQuote => "\"",
            EncapsedAndWhitespace => "T_ENCAPSED_AND_WHITESPACE",
            NumString => "T_NUM_STRING",
            StringVarname => "T_STRING_VARNAME",
            DollarOpenCurly => "T_DOLLAR_OPEN_CURLY_BRACES",
            CurlyOpen => "T_CURLY_OPEN",
            StartHeredoc => "T_START_HEREDOC",
            EndHeredoc => "T_END_HEREDOC",

            Identifier => "T_STRING",
            NameQualified => "T_NAME_QUALIFIED",
            NameFullyQualified => "T_NAME_FULLY_QUALIFIED",
            NameRelative => "T_NAME_RELATIVE",

            Keyword(kw) => kw.php_name(),

            Eq => "=",
            Plus => "+",
            Minus => "-",
            Star => "*",
            Slash => "/",
            Percent => "%",
            Dot => ".",
            Bang => "!",
            Tilde => "~",
            Caret => "^",
            AmpFollowedByVar => "T_AMPERSAND_FOLLOWED_BY_VAR_OR_VARARG",
            AmpNotFollowedByVar => "T_AMPERSAND_NOT_FOLLOWED_BY_VAR_OR_VARARG",
            Pipe => "|",
            Lt => "<",
            Gt => ">",
            Question => "?",
            Colon => ":",
            Semicolon => ";",
            Comma => ",",
            At => "@",
            Dollar => "$",
            LParen => "(",
            RParen => ")",
            LBracket => "[",
            RBracket => "]",
            LBrace => "{",
            RBrace => "}",
            Backtick => "`",
            NsSeparator => "T_NS_SEPARATOR",

            Pow => "T_POW",
            Sl => "T_SL",
            Sr => "T_SR",
            Coalesce => "T_COALESCE",
            Inc => "T_INC",
            Dec => "T_DEC",
            Arrow => "T_OBJECT_OPERATOR",
            NullsafeArrow => "T_NULLSAFE_OBJECT_OPERATOR",
            DoubleArrow => "T_DOUBLE_ARROW",
            DoubleColon => "T_DOUBLE_COLON",
            IsEqual => "T_IS_EQUAL",
            IsNotEqual => "T_IS_NOT_EQUAL",
            IsIdentical => "T_IS_IDENTICAL",
            IsNotIdentical => "T_IS_NOT_IDENTICAL",
            LtEq => "T_IS_SMALLER_OR_EQUAL",
            GtEq => "T_IS_GREATER_OR_EQUAL",
            Spaceship => "T_SPACESHIP",
            BoolAnd => "T_BOOLEAN_AND",
            BoolOr => "T_BOOLEAN_OR",
            PlusEq => "T_PLUS_EQUAL",
            MinusEq => "T_MINUS_EQUAL",
            MulEq => "T_MUL_EQUAL",
            DivEq => "T_DIV_EQUAL",
            ConcatEq => "T_CONCAT_EQUAL",
            ModEq => "T_MOD_EQUAL",
            PowEq => "T_POW_EQUAL",
            AndEq => "T_AND_EQUAL",
            OrEq => "T_OR_EQUAL",
            XorEq => "T_XOR_EQUAL",
            SlEq => "T_SL_EQUAL",
            SrEq => "T_SR_EQUAL",
            CoalesceEq => "T_COALESCE_EQUAL",
            Ellipsis => "T_ELLIPSIS",
            Attribute => "T_ATTRIBUTE",
            PipeOp => "T_PIPE",

            IntCast => "T_INT_CAST",
            DoubleCast => "T_DOUBLE_CAST",
            StringCast => "T_STRING_CAST",
            ArrayCast => "T_ARRAY_CAST",
            ObjectCast => "T_OBJECT_CAST",
            BoolCast => "T_BOOL_CAST",
            UnsetCast => "T_UNSET_CAST",
            VoidCast => "T_VOID_CAST",

            YieldFrom => "T_YIELD_FROM",

            PrivateSet => "T_PRIVATE_SET",
            ProtectedSet => "T_PROTECTED_SET",
            PublicSet => "T_PUBLIC_SET",

            Unknown => "T_BAD_CHARACTER",
            Eof => return None,
        })
    }
}

/// PHP reserved keywords. PHP keywords are case-insensitive; [`Kw::lookup`]
/// expects an already-lowercased identifier.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kw {
    Exit,
    Eval,
    Include,
    IncludeOnce,
    Require,
    RequireOnce,
    LogicalOr,
    LogicalXor,
    LogicalAnd,
    Print,
    Yield,
    Instanceof,
    New,
    Clone,
    If,
    Elseif,
    Else,
    Endif,
    Echo,
    Do,
    While,
    Endwhile,
    For,
    Endfor,
    Foreach,
    Endforeach,
    Declare,
    Enddeclare,
    As,
    Switch,
    Endswitch,
    Case,
    Default,
    Match,
    Break,
    Continue,
    Goto,
    Function,
    Fn,
    Const,
    Return,
    Try,
    Catch,
    Finally,
    Throw,
    Use,
    Insteadof,
    Global,
    Static,
    Abstract,
    Final,
    Private,
    Protected,
    Public,
    Readonly,
    Var,
    Unset,
    Isset,
    Empty,
    HaltCompiler,
    Class,
    Trait,
    Interface,
    Enum,
    Extends,
    Implements,
    Namespace,
    List,
    Array,
    Callable,
    Line,
    File,
    Dir,
    ClassC,
    TraitC,
    MethodC,
    FuncC,
    PropertyC,
    NsC,
}

impl Kw {
    /// Look up a keyword from an already-lowercased identifier.
    pub fn lookup(lower: &str) -> Option<Kw> {
        use Kw::*;
        Some(match lower {
            "exit" | "die" => Exit,
            "eval" => Eval,
            "include" => Include,
            "include_once" => IncludeOnce,
            "require" => Require,
            "require_once" => RequireOnce,
            "or" => LogicalOr,
            "xor" => LogicalXor,
            "and" => LogicalAnd,
            "print" => Print,
            "yield" => Yield,
            "instanceof" => Instanceof,
            "new" => New,
            "clone" => Clone,
            "if" => If,
            "elseif" => Elseif,
            "else" => Else,
            "endif" => Endif,
            "echo" => Echo,
            "do" => Do,
            "while" => While,
            "endwhile" => Endwhile,
            "for" => For,
            "endfor" => Endfor,
            "foreach" => Foreach,
            "endforeach" => Endforeach,
            "declare" => Declare,
            "enddeclare" => Enddeclare,
            "as" => As,
            "switch" => Switch,
            "endswitch" => Endswitch,
            "case" => Case,
            "default" => Default,
            "match" => Match,
            "break" => Break,
            "continue" => Continue,
            "goto" => Goto,
            "function" => Function,
            "fn" => Fn,
            "const" => Const,
            "return" => Return,
            "try" => Try,
            "catch" => Catch,
            "finally" => Finally,
            "throw" => Throw,
            "use" => Use,
            "insteadof" => Insteadof,
            "global" => Global,
            "static" => Static,
            "abstract" => Abstract,
            "final" => Final,
            "private" => Private,
            "protected" => Protected,
            "public" => Public,
            "readonly" => Readonly,
            "var" => Var,
            "unset" => Unset,
            "isset" => Isset,
            "empty" => Empty,
            "__halt_compiler" => HaltCompiler,
            "class" => Class,
            "trait" => Trait,
            "interface" => Interface,
            "enum" => Enum,
            "extends" => Extends,
            "implements" => Implements,
            "namespace" => Namespace,
            "list" => List,
            "array" => Array,
            "callable" => Callable,
            "__line__" => Line,
            "__file__" => File,
            "__dir__" => Dir,
            "__class__" => ClassC,
            "__trait__" => TraitC,
            "__method__" => MethodC,
            "__function__" => FuncC,
            "__property__" => PropertyC,
            "__namespace__" => NsC,
            _ => return None,
        })
    }

    pub fn php_name(self) -> &'static str {
        use Kw::*;
        match self {
            Exit => "T_EXIT",
            Eval => "T_EVAL",
            Include => "T_INCLUDE",
            IncludeOnce => "T_INCLUDE_ONCE",
            Require => "T_REQUIRE",
            RequireOnce => "T_REQUIRE_ONCE",
            LogicalOr => "T_LOGICAL_OR",
            LogicalXor => "T_LOGICAL_XOR",
            LogicalAnd => "T_LOGICAL_AND",
            Print => "T_PRINT",
            Yield => "T_YIELD",
            Instanceof => "T_INSTANCEOF",
            New => "T_NEW",
            Clone => "T_CLONE",
            If => "T_IF",
            Elseif => "T_ELSEIF",
            Else => "T_ELSE",
            Endif => "T_ENDIF",
            Echo => "T_ECHO",
            Do => "T_DO",
            While => "T_WHILE",
            Endwhile => "T_ENDWHILE",
            For => "T_FOR",
            Endfor => "T_ENDFOR",
            Foreach => "T_FOREACH",
            Endforeach => "T_ENDFOREACH",
            Declare => "T_DECLARE",
            Enddeclare => "T_ENDDECLARE",
            As => "T_AS",
            Switch => "T_SWITCH",
            Endswitch => "T_ENDSWITCH",
            Case => "T_CASE",
            Default => "T_DEFAULT",
            Match => "T_MATCH",
            Break => "T_BREAK",
            Continue => "T_CONTINUE",
            Goto => "T_GOTO",
            Function => "T_FUNCTION",
            Fn => "T_FN",
            Const => "T_CONST",
            Return => "T_RETURN",
            Try => "T_TRY",
            Catch => "T_CATCH",
            Finally => "T_FINALLY",
            Throw => "T_THROW",
            Use => "T_USE",
            Insteadof => "T_INSTEADOF",
            Global => "T_GLOBAL",
            Static => "T_STATIC",
            Abstract => "T_ABSTRACT",
            Final => "T_FINAL",
            Private => "T_PRIVATE",
            Protected => "T_PROTECTED",
            Public => "T_PUBLIC",
            Readonly => "T_READONLY",
            Var => "T_VAR",
            Unset => "T_UNSET",
            Isset => "T_ISSET",
            Empty => "T_EMPTY",
            HaltCompiler => "T_HALT_COMPILER",
            Class => "T_CLASS",
            Trait => "T_TRAIT",
            Interface => "T_INTERFACE",
            Enum => "T_ENUM",
            Extends => "T_EXTENDS",
            Implements => "T_IMPLEMENTS",
            Namespace => "T_NAMESPACE",
            List => "T_LIST",
            Array => "T_ARRAY",
            Callable => "T_CALLABLE",
            Line => "T_LINE",
            File => "T_FILE",
            Dir => "T_DIR",
            ClassC => "T_CLASS_C",
            TraitC => "T_TRAIT_C",
            MethodC => "T_METHOD_C",
            FuncC => "T_FUNC_C",
            PropertyC => "T_PROPERTY_C",
            NsC => "T_NS_C",
        }
    }
}
