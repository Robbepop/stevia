
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Loc(u32);

impl Loc {
    pub fn zero() -> Self {
        Loc(0)
    }

    pub fn to_u32(self) -> u32 {
        self.0
    }
}

impl From<u32> for Loc {
    fn from(val: u32) -> Self {
        Loc(val)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    pub begin: Loc,
    pub end: Loc,
}

impl Span {
    pub fn zero() -> Self {
        Span {
            begin: Loc::zero(),
            end: Loc::zero(),
        }
    }

    pub fn new(begin: Loc, end: Loc) -> Self {
        Span { begin, end }
    }

    pub fn len(self) -> usize {
        (self.end.to_usize()) - (self.begin.to_usize()) + 1
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TokenKind {
    Comment,
    Whitespace,

    Numeral,
    Decimal,
    StringLiteral,

    OpenParen,
    CloseParen,

    Underscore,
    ExclamationMark,

    As,
    Let,
    Exists,
    Forall,
    Match,
    Par,

    SimpleSymbol,
    QuotedSymbol,
    Keyword,

    EndOfFile,
    Unknown,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Token {
    kind: TokenKind,
    span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn kind(self) -> TokenKind {
        self.kind
    }

    pub fn span(self) -> Span {
        self.span
    }
}
