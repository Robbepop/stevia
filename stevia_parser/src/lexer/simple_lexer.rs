use lexer::{
    error::{LexerError, LexerErrorKind, LexerResult},
    raw_lexer::RawTokenIter,
    raw_smtlib2_tokens,
    repr::{Command, Loc, MetaSpec, RawTokenKind, Span, Token, TokenKind},
};

use std::collections::HashMap;

pub fn smtlib2_tokens(input: &str) -> TokenIter {
    debug_assert!(input.len() >= 1); // TODO: convert to error.
    TokenIter::new(raw_smtlib2_tokens(input))
}

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

fn longest_reserved_name() -> usize {
    *LONGEST_RESERVED_NAME
}

lazy_static! {
    static ref LONGEST_RESERVED_NAME: usize = {
        RESERVED_NAMES.iter().map(|r| r.0.len()).max().unwrap()
    };
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
    pub(crate) fn new(raw_lexer: RawTokenIter<'c>) -> Self {
        Self { raw_lexer }
    }

    fn resolve_simple_symbol(&self, span: Span) -> TokenKind {
        if span.len() > longest_reserved_name() {
            // This is an optimization:
            // Early return for all symbol names for which their
            // length exceeds the length of even the longest reserved name.
            return TokenKind::Symbol
        }
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

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_input<I>(input: &str, expected_toks: I)
    where
        I: IntoIterator<Item = (TokenKind, (u32, u32))>,
    {
        let expected_toks = expected_toks
            .into_iter()
            .map(|(kind, (begin, end))| {
                Token::new(kind, Span::new(Loc::from(begin), Loc::from(end)))
            })
            .collect::<Vec<_>>();
        let actual_toks = smtlib2_tokens(input).collect::<Vec<_>>();
        assert_eq!(actual_toks.len(), expected_toks.len());
        for (actual, expected) in actual_toks.into_iter().zip(expected_toks.into_iter()) {
            assert_eq!(actual, expected);
        }
    }

    type RawResult = ::std::result::Result<TokenKind, LexerErrorKind>;

    fn assert_raw_input<I>(input: &str, expected_toks: I)
    where
        I: IntoIterator<Item = (RawResult, (u32, u32))>,
    {
        let expected_toks = expected_toks.into_iter().map(|(raw, (begin, end))| {
            let loc = Span::new(Loc::from(begin), Loc::from(end));
            raw.map(|tok| Token::new(tok, loc))
                .map_err(|err| LexerError::new(err, loc))
        });
        let mut actual_toks = smtlib2_tokens(input);
        for expected in expected_toks {
            let actual = actual_toks.next_token().map_err(|mut err| {
                err.clear_context();
                err
            });
            assert_eq!(actual, expected)
        }
    }

    #[test]
    fn keywords() {
        assert_input("_", vec![(TokenKind::Underscore, (0, 0))]);
        assert_input("!", vec![(TokenKind::ExclamationMark, (0, 0))]);
        assert_input("as", vec![(TokenKind::As, (0, 1))]);
        assert_input("let", vec![(TokenKind::Let, (0, 2))]);
        assert_input("exists", vec![(TokenKind::Exists, (0, 5))]);
        assert_input("forall", vec![(TokenKind::Forall, (0, 5))]);
        assert_input("match", vec![(TokenKind::Match, (0, 4))]);
        assert_input("par", vec![(TokenKind::Par, (0, 2))]);
    }

    #[test]
    }

    #[test]
    fn par_keyword() {
        assert_input("par", vec![(TokenKind::Par, (0, 2))]);
    }

    // MetaSpec(MetaSpec),
    // Command(Command),

}
