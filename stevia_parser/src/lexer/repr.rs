
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Loc(u32);

impl Loc {
    pub fn zero() -> Self {
        Loc(0)
    }

    pub fn to_u32(self) -> u32 {
        self.0
    }

    pub fn to_usize(self) -> usize {
        self.0 as usize
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
        ((self.end.to_usize() as isize) - (self.begin.to_usize() as isize) + 1) as usize
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RawTokenKind {
    Comment,
    Whitespace,

    Numeral,
    Decimal,
    StringLiteral,

    OpenParen,
    CloseParen,

    SimpleSymbol,
    QuotedSymbol,
    Keyword
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GenericToken<T> {
    kind: T,
    span: Span,
}

pub type RawToken = GenericToken<RawTokenKind>;
pub type Token = GenericToken<TokenKind>;

impl<T> GenericToken<T> {
    pub fn new(kind: T, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn kind(self) -> T {
        self.kind
    }

    pub fn span(self) -> Span {
        self.span
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

    Symbol,
    Keyword,

    ExclamationMark,
    Underscore,

    As,
    Let,
    Exists,
    Forall,
    Match,
    Par,

    MetaSpec(MetaSpec),
    Command(Command)
}

impl TokenKind {
    pub fn has_semantic_meaning(self) -> bool {
        match self {
            TokenKind::Comment    |
            TokenKind::Whitespace => false,
            _ => true
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MetaSpec {
    Binary,
    Hexadecimal,
    Decimal,
    Numeral,
    String
}

impl MetaSpec {
    pub fn to_str(self) -> &'static str {
        use self::MetaSpec::*;
        match self {
            Binary => "BINARY",
            Hexadecimal => "HEXADECIMAL",
            Decimal => "DECIMAL",
            Numeral => "NUMERAL",
            String => "STRING"
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Command {
    Assert,
    CheckSat,
    CheckSatAssuming,
    DeclareConst,
    DeclareDatatype,
    DeclareDatatypes,
    DeclareFun,
    DeclareSort,
    DefineFun,
    DefineFunRec,
    DefineFunsRec,
    DefineSort,
    Echo,
    Exit,
    GetAssertions,
    GetAssignment,
    GetInfo,
    GetModel,
    GetOption,
    GetProof,
    GetUnsatAssumptions,
    GetUnsatCore,
    GetValue,
    Pop,
    Push,
    Reset,
    ResetAssertions,
    SetInfo,
    SetLogic,
    SetOption
}

impl Command {
    pub fn to_str(self) -> &'static str {
        use self::Command::*;
        match self {
            Assert => "assert",
            CheckSat => "check-sat",
            CheckSatAssuming => "check-sat-assuming",
            DeclareConst => "declare-const",
            DeclareDatatype => "declare-datatype",
            DeclareDatatypes => "declare-datatypes",
            DeclareFun => "declare-fun",
            DeclareSort => "declare-sort",
            DefineFun => "define-fun",
            DefineFunRec => "define-fun-rec",
            DefineFunsRec => "define-funs-rec",
            DefineSort => "define-sort",
            Echo => "echo",
            Exit => "exit",
            GetAssertions => "get-assertions",
            GetAssignment => "get-assignment",
            GetInfo => "get-info",
            GetModel => "get-model",
            GetOption => "get-option",
            GetProof => "get-proof",
            GetUnsatAssumptions => "get-unsat-assumptions",
            GetUnsatCore => "get-unsat-core",
            GetValue => "get-value",
            Pop => "pop",
            Push => "push",
            Reset => "reset",
            ResetAssertions => "reset-assertions",
            SetInfo => "set-info",
            SetLogic => "set-logic",
            SetOption => "set-option"
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod span {
        use super::*;

        #[test]
        fn len_ok() {
            assert_eq!(Span::new(Loc::from(0), Loc::from(42)).len(), 43);
            assert_eq!(Span::new(Loc::from(100), Loc::from(200)).len(), 101);
            assert_eq!(Span::new(Loc::from(3), Loc::from(5)).len(), 3);
        }

        #[test]
        fn empty_span_len() {
            assert_eq!(Span::new(Loc::from(1), Loc::from(0)).len(), 0);
        }
    }
}
