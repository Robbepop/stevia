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
    fn meta_spec() {
        assert_input("BINARY", vec![(TokenKind::MetaSpec(MetaSpec::Binary), (0, 5))]);
        assert_input("DECIMAL", vec![(TokenKind::MetaSpec(MetaSpec::Decimal), (0, 6))]);
        assert_input("HEXADECIMAL", vec![(TokenKind::MetaSpec(MetaSpec::Hexadecimal), (0, 10))]);
        assert_input("STRING", vec![(TokenKind::MetaSpec(MetaSpec::String), (0, 5))]);
        assert_input("NUMERAL", vec![(TokenKind::MetaSpec(MetaSpec::Numeral), (0, 6))]);
    }

    #[test]
    fn commands() {
        assert_input("assert", vec![(TokenKind::Command(Command::Assert), (0, 5))]);
        assert_input("check-sat", vec![(TokenKind::Command(Command::CheckSat), (0, 8))]);
        assert_input("check-sat-assuming", vec![(TokenKind::Command(Command::CheckSatAssuming), (0, 17))]);
        assert_input("declare-const", vec![(TokenKind::Command(Command::DeclareConst), (0, 12))]);
        assert_input("declare-datatype", vec![(TokenKind::Command(Command::DeclareDatatype), (0, 15))]);
        assert_input("declare-datatypes", vec![(TokenKind::Command(Command::DeclareDatatypes), (0, 16))]);
        assert_input("declare-fun", vec![(TokenKind::Command(Command::DeclareFun), (0, 10))]);
        assert_input("declare-sort", vec![(TokenKind::Command(Command::DeclareSort), (0, 11))]);
        assert_input("define-fun", vec![(TokenKind::Command(Command::DefineFun), (0, 9))]);
        assert_input("define-fun-rec", vec![(TokenKind::Command(Command::DefineFunRec), (0, 13))]);
        assert_input("define-funs-rec", vec![(TokenKind::Command(Command::DefineFunsRec), (0, 14))]);
        assert_input("define-sort", vec![(TokenKind::Command(Command::DefineSort), (0, 10))]);
        assert_input("echo", vec![(TokenKind::Command(Command::Echo), (0, 3))]);
        assert_input("exit", vec![(TokenKind::Command(Command::Exit), (0, 3))]);
        assert_input("get-assertions", vec![(TokenKind::Command(Command::GetAssertions), (0, 13))]);
        assert_input("get-assignment", vec![(TokenKind::Command(Command::GetAssignment), (0, 13))]);
        assert_input("get-info", vec![(TokenKind::Command(Command::GetInfo), (0, 7))]);
        assert_input("get-model", vec![(TokenKind::Command(Command::GetModel), (0, 8))]);
        assert_input("get-option", vec![(TokenKind::Command(Command::GetOption), (0, 9))]);
        assert_input("get-proof", vec![(TokenKind::Command(Command::GetProof), (0, 8))]);
        assert_input("get-unsat-assumptions", vec![(TokenKind::Command(Command::GetUnsatAssumptions), (0, 20))]);
        assert_input("get-unsat-core", vec![(TokenKind::Command(Command::GetUnsatCore), (0, 13))]);
        assert_input("get-value", vec![(TokenKind::Command(Command::GetValue), (0, 8))]);
        assert_input("pop", vec![(TokenKind::Command(Command::Pop), (0, 2))]);
        assert_input("push", vec![(TokenKind::Command(Command::Push), (0, 3))]);
        assert_input("reset", vec![(TokenKind::Command(Command::Reset), (0, 4))]);
        assert_input("reset-assertions", vec![(TokenKind::Command(Command::ResetAssertions), (0, 15))]);
        assert_input("set-info", vec![(TokenKind::Command(Command::SetInfo), (0, 7))]);
        assert_input("set-logic", vec![(TokenKind::Command(Command::SetLogic), (0, 8))]);
        assert_input("set-option", vec![(TokenKind::Command(Command::SetOption), (0, 9))]);
    }
}
