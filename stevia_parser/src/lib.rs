//! Parser for the SMTLib 2.6 standard
//!
//! ## Core components
//!
//! - Theory Declarations
//! - Logic Declarations
//! - Scripts
//!
//! The syntax is similar to that of LISP.
//! Every expression in this version is a legal S-expression of Common LISP.
//!
//! Comments:
//! Starting with ';' (semi-colon) until end of the same line.
//!
//! White space:
//! Tab, Line Feed, Carriage Return, Space
//!
//! Digit: 0-9
//!
//! Letter: a-z and A-Z
//!
//! Numeral: 0 or non-empty sequence of Digits not starting with 0
//!
//! Decimal: <Numeral>.0*<Numeral>
//!
//! Hexadecimal: [0-9a-fA-F] non-empty, starting with '#x'
//!
//! Binaries: {0,1} starting with '#b'
//!
//! String literals:
//!
//! Starting and ending with '"', can have '""' as escape sequence to represent a single '"'.
//! Can have line breaks.
//!
//! Reserved words:
//!
//! - BINARY
//! - DECIMAL
//! - HEXADECIMAL
//! - NUMERAL
//! - STRING
//! - _
//! - !
//! - as
//! - let
//! - exists
//! - forall
//! - match
//! - par
//!
//! Also each command name is a reserved word:
//!
//! - set-logic
//! - set-option
//! - etc... (Section 3.9)
//!
//! Symbol:
//!
//! Simple Symbol or Quoted Symbol
//!
//! Simple Symbol:
//!
//! Any non-empty sequence of elements of <Letter> and <Digit> and {~, !, $, %, ^, &, *, _, -, +, =, <, >, ., ?, /}
//! that does not start with a digit and is not a reserved word.
//!
//! Quoted Symbol:
//!
//! Starts and ends with '|' and may not contain '|' or '\'.
//!
//! Simple Symbols starting with '@' or '.' are reserved for solver use.
//!
//! Keywords:
//!
//! Is a token of the form ':<Simple Symbol>'
//! They have special use in the language: Used as attributes or option names.

#[cfg(test)]
#[macro_use]
extern crate indoc;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Loc(u32);

impl Loc {
    pub fn zero() -> Self {
        Loc(0)
    }
}

impl From<u32> for Loc {
    fn from(val: u32) -> Self {
        Loc(val)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    begin: Loc,
    end: Loc,
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
}

pub fn lex_smtlib2(input: &str) -> LexemIter {
    LexemIter::new(input)
}

use std::str::CharIndices;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct CharAndLoc {
    pub ch: char,
    pub loc: Loc,
}

impl CharAndLoc {
    pub fn new(ch: char, loc: Loc) -> Self {
        Self { ch, loc }
    }
}

#[derive(Debug, Clone)]
pub struct LexemIter<'c> {
    input: CharIndices<'c>,
    loc: Span,
    peek: Option<CharAndLoc>,
}

impl<'c> LexemIter<'c> {
    pub(self) fn new(input: &'c str) -> Self {
        let mut iter = LexemIter {
            input: input.char_indices(),
            loc: Span::zero(),
            peek: None,
        };
        iter.pull();
        iter
    }

    fn pull(&mut self) {
        self.peek = self
            .input
            .next()
            .map(|(loc, ch)| CharAndLoc::new(ch, Loc::from(loc as u32)))
    }

    fn peek(&mut self) -> Option<char> {
        // assert!(self.peek.is_some(), "unexpected end of file");
        self.peek.map(|ch_loc| ch_loc.ch)
        // .unwrap()
    }

    fn consume(&mut self) -> &mut Self {
        assert!(self.peek.is_some(), "unexpected end of file");
        let peek = self.peek.unwrap();
        self.loc.end = peek.loc;
        // println!("consume: peek = {:?}, peek, self.loc.end = {:?}", peek, self.loc.end);
        self.pull();
        self
    }

    fn tok(&mut self, kind: TokenKind) -> Token {
        let tok = Token::new(kind, self.loc);
        // println!("tok: kind = {:?}, self.loc.begin = {:?}, self.loc.end = {:?}", kind, self.loc.begin, self.loc.end);
        if let Some(peek) = self.peek {
            self.loc.begin = peek.loc;
        };
        tok
    }

    fn scan_whitespace(&mut self) -> Token {
        while let Some(peek) = self.peek() {
            if !peek.is_whitespace() {
                break;
            }
            self.consume();
        }
        self.tok(TokenKind::Whitespace)
    }

    fn scan_comment(&mut self) -> Token {
        fn is_line_ending(ch: char) -> bool {
            ch == '\n' || ch == '\r'
        }
        while let Some(peek) = self.peek() {
            self.consume();
            if is_line_ending(peek) {
                break;
            }
        }
        self.tok(TokenKind::Comment)
    }

    fn next_token(&mut self) -> Token {
        use self::TokenKind::*;
        let peek = match self.peek() {
            Some(peek) => peek,
            None => return self.tok(EndOfFile),
        };
        match peek {
            c if c.is_whitespace() => self.scan_whitespace(),
            ';' => self.scan_comment(),
            '(' => self.consume().tok(OpenParen),
            ')' => self.consume().tok(CloseParen),
            _ => self.consume().tok(Unknown),
        }
    }
}

impl<'c> Iterator for LexemIter<'c> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let tok = self.next_token();
        if let TokenKind::EndOfFile = tok.kind {
            return None;
        }
        Some(tok)
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
        let actual_toks = lex_smtlib2(input).collect::<Vec<_>>();
        assert_eq!(actual_toks.len(), expected_toks.len());
        for (actual, expected) in actual_toks.into_iter().zip(expected_toks.into_iter()) {
            assert_eq!(actual, expected);
        }
    }

    mod comment {
        use super::*;

        #[test]
        fn single_line() {
            let mut toks = lex_smtlib2("; this is a comment");
            assert_eq!(toks.next(), Some(Token::new(TokenKind::Comment, Span::new(Loc::from(0), Loc::from(18)))));
            assert_eq!(toks.next(), None)
        }

        #[test]
        fn multi_line() {
            let mut toks = lex_smtlib2(indoc!(
                "; first line
                 ; second line
                 ; third line")
            );
            use self::TokenKind::Comment;
            assert_eq!(toks.next(), Some(Token::new(Comment, Span::new(Loc::from(0), Loc::from(12)))));
            assert_eq!(toks.next(), Some(Token::new(Comment, Span::new(Loc::from(13), Loc::from(26)))));
            assert_eq!(toks.next(), Some(Token::new(Comment, Span::new(Loc::from(27), Loc::from(38)))));
            assert_eq!(toks.next(), None)
        }

        #[test]
        fn multiple_semi_colons() {
            let mut toks = lex_smtlib2(";;;;;");
            assert_eq!(toks.next(), Some(Token::new(TokenKind::Comment, Span::new(Loc::from(0), Loc::from(4)))));
            assert_eq!(toks.next(), None)
        }

        #[test]
        fn empty_lines() {
            let mut toks = lex_smtlib2(indoc!(
                ";
                 ;
                 ;"
            ));
            use self::TokenKind::Comment;
            assert_eq!(toks.next(), Some(Token::new(Comment, Span::new(Loc::from(0), Loc::from(1)))));
            assert_eq!(toks.next(), Some(Token::new(Comment, Span::new(Loc::from(2), Loc::from(3)))));
            assert_eq!(toks.next(), Some(Token::new(Comment, Span::new(Loc::from(4), Loc::from(4)))));
            assert_eq!(toks.next(), None)
        }
    }

    mod whitespace {
        use super::*;

        #[test]
        fn any() {
            let mut toks = lex_smtlib2(" \t\n\r");
            assert_eq!(toks.next(), Some(Token::new(TokenKind::Whitespace, Span::new(Loc::from(0), Loc::from(3)))));
            assert_eq!(toks.next(), None)
    mod paren {
        use super::*;

        #[test]
        fn open() {
            assert_input("(", vec![(TokenKind::OpenParen, (0, 0))]);
        }

        #[test]
        fn close() {
            assert_input(")", vec![(TokenKind::CloseParen, (0, 0))]);
        }
    }
}
