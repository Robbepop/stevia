use lexer::error::LexerResult;
use lexer::raw_lexer::RawTokenIter;
use lexer::repr::{Command, Loc, MetaSpec, RawTokenKind, Span, Token, TokenKind};

use std::collections::HashMap;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ReservedWord {
    Underscore,
    ExclamationMark,

    As,
    Let,
    Exists,
    Forall,
    Match,
    Par,

    MetaSpec(MetaSpec),
    Command(Command),
}

impl From<ReservedWord> for TokenKind {
    fn from(reserved_word: ReservedWord) -> Self {
        use self::ReservedWord::*;
        match reserved_word {
            Underscore => TokenKind::Underscore,
            ExclamationMark => TokenKind::ExclamationMark,

            As => TokenKind::As,
            Let => TokenKind::Let,
            Exists => TokenKind::Exists,
            Forall => TokenKind::Forall,
            Match => TokenKind::Match,
            Par => TokenKind::Par,

            MetaSpec(meta_spec) => TokenKind::MetaSpec(meta_spec),
            Command(command) => TokenKind::Command(command),
        }
    }
}

lazy_static! {
    static ref RESERVED_NAMES: HashMap<&'static str, ReservedWord> = {
        let mut reserved_names = HashMap::new();
        reserved_names.insert("_", ReservedWord::Underscore);
        reserved_names.insert("!", ReservedWord::ExclamationMark);
        reserved_names.insert("as", ReservedWord::As);
        reserved_names.insert("let", ReservedWord::Let);
        reserved_names.insert("exists", ReservedWord::Exists);
        reserved_names.insert("forall", ReservedWord::Forall);
        reserved_names.insert("match", ReservedWord::Match);
        reserved_names.insert("par", ReservedWord::Par);
        for &meta_spec in &[
            MetaSpec::Binary,
            MetaSpec::Hexadecimal,
            MetaSpec::Decimal,
            MetaSpec::Numeral,
            MetaSpec::String,
        ] {
            reserved_names.insert(meta_spec.to_str(), ReservedWord::MetaSpec(meta_spec));
        }
        use self::Command::*;
        for &command in &[
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
            SetOption,
        ] {
            reserved_names.insert(command.to_str(), ReservedWord::Command(command));
        }
        reserved_names
    };
}

pub struct TokenIter<'c> {
    raw_lexer: RawTokenIter<'c>,
}

impl<'c> TokenIter<'c> {
    fn resolve_simple_symbol(&self, span: Span) -> TokenKind {
        if let Some(&reserved) = RESERVED_NAMES.get(self.raw_lexer.span_to_str(span)) {
            return TokenKind::from(reserved);
        }
        TokenKind::Symbol
    }

    pub fn next_token(&mut self) -> LexerResult<Token> {
        let raw_tok = self.raw_lexer.next_token()?;
        let simple_kind = match raw_tok.kind() {
            RawTokenKind::Comment => TokenKind::Comment,
            RawTokenKind::Whitespace => TokenKind::Whitespace,
            RawTokenKind::Numeral => TokenKind::Numeral,
            RawTokenKind::Decimal => TokenKind::Decimal,
            RawTokenKind::StringLiteral => TokenKind::StringLiteral,
            RawTokenKind::OpenParen => TokenKind::OpenParen,
            RawTokenKind::CloseParen => TokenKind::CloseParen,
            RawTokenKind::Keyword => TokenKind::Keyword,
            RawTokenKind::SimpleSymbol => self.resolve_simple_symbol(raw_tok.span()),
            RawTokenKind::QuotedSymbol => {
                let simple_span = Span::new(
                    Loc::from(raw_tok.span().begin.to_u32() + 1),
                    Loc::from(raw_tok.span().end.to_u32() - 1),
                );
                return Ok(Token::new(TokenKind::Symbol, simple_span));
            }
        };
        Ok(Token::new(simple_kind, raw_tok.span()))
    }
}

impl<'c> Iterator for TokenIter<'c> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token().ok()
    }
}
