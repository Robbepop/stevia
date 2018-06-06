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

use std::error;
use std::fmt;

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

pub fn lex_smtlib2(input: &str) -> LexemeIter {
    LexemeIter::new(input)
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum LexerErrorKind {
    UnexpectedEndOfFile,
    UnexpectedCharacter(char),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LexerError {
    kind: LexerErrorKind,
    span: Span,
    context: Option<String>,
}

impl LexerError {
    fn new(kind: LexerErrorKind, span: Span) -> Self {
        Self {
            kind,
            span,
            context: None,
        }
    }

    pub fn context_msg<S>(self, msg: S) -> Self
    where
        S: Into<String>,
    {
        let mut this = self;
        this.context = Some(msg.into());
        this
    }

    pub fn kind(&self) -> LexerErrorKind {
        self.kind
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn context(&self) -> &str {
        match &self.context {
            None => "",
            Some(s) => s
        }
    }

    pub fn unexpected_end_of_file(span: Span) -> Self {
        Self::new(LexerErrorKind::UnexpectedEndOfFile, span)
    }

    pub fn unexpected_character(span: Span, ch: char) -> Self {
        Self::new(LexerErrorKind::UnexpectedCharacter(ch), span)
    }
}

impl fmt::Display for LexerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::LexerErrorKind::*;
        match self.kind() {
            UnexpectedEndOfFile => write!(
                f,
                "error ({}:{}): unexpected end of file: {:?}",
                self.span.begin.to_u32(),
                self.span.end.to_u32(),
                self.context
            ),
            UnexpectedCharacter(ch) => write!(
                f,
                "error ({}:{}): unexpected character (= {}): {:?}",
                self.span.begin.to_u32(),
                self.span.end.to_u32(),
                ch,
                self.context
            )
        }
    }
}

impl error::Error for LexerError {
    fn description(&self) -> &str {
        use self::LexerErrorKind::*;
        match self.kind() {
            UnexpectedEndOfFile => "unexpected end of file",
            UnexpectedCharacter(_) => "unexpected character",
        }
    }
}

#[derive(Debug, Clone)]
pub struct LexemeIter<'c> {
    input: CharIndices<'c>,
    loc: Span,
    peek: Option<CharAndLoc>,
}

impl<'c> LexemeIter<'c> {
    pub(self) fn new(input: &'c str) -> Self {
        let mut iter = LexemeIter {
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
        self.peek.map(|ch_loc| ch_loc.ch)
    }

    fn consume(&mut self) -> &mut Self {
        debug_assert!(self.peek.is_some(), "unexpected end of file");
        let peek = self.peek.unwrap();
        self.loc.end = peek.loc;
        self.pull();
        self
    }

    fn tok(&mut self, kind: TokenKind) -> Token {
        let tok = Token::new(kind, self.loc);
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

    fn scan_numeral(&mut self) -> Token {
        debug_assert!(self.peek().is_some());
        debug_assert!(self.peek().unwrap().is_digit(10));

        while let Some(peek) = self.peek() {
            match peek {
                c if c.is_digit(10) => {
                    self.consume();
                }
                '.' => return self.scan_decimal(),
                _ => break,
            }
        }
        self.tok(TokenKind::Numeral)
    }

    fn scan_decimal(&mut self) -> Token {
        debug_assert!(self.peek().is_some());
        debug_assert!(self.peek().unwrap() == '.');

        self.consume();
        match self.peek() {
            None => panic!("unexpected end of file while scanning a decimal number"),
            Some(peek) => match peek {
                c if c.is_digit(10) => {
                    while let Some(peek) = self.peek() {
                        if !peek.is_digit(10) {
                            break;
                        }
                        self.consume();
                    }
                    return self.tok(TokenKind::Decimal);
                }
                _ => panic!("unexpected character while scanning a decimal number"),
            },
        }
    }

    fn scan_numeral_or_decimal(&mut self) -> Token {
        debug_assert!(self.peek().is_some());
        debug_assert!(self.peek().unwrap().is_digit(10));

        match self.peek().unwrap() {
            '0' => match self.consume().peek() {
                None => self.tok(TokenKind::Numeral),
                Some(peek) => match peek {
                    c if c.is_digit(10) => self.scan_numeral(),
                    '.' => self.scan_decimal(),
                    c => panic!(
                        "unexpected character (= {:?}) after while scanning for numeral or decimal literal", c)
                }
            }
            _ => self.scan_numeral()
        }
    }

    fn scan_hexdec_numeral(&mut self) -> Token {
        debug_assert!(self.peek().is_some());
        debug_assert_eq!(self.peek().unwrap(), 'x');

        self.consume();
        match self.peek() {
            None => panic!("unexpected end of file while scanning for hexdec numeral"),
            Some(peek) => match peek {
                c if c.is_digit(16) => {
                    while let Some(peek) = self.peek() {
                        if !peek.is_digit(16) {
                            break;
                        }
                        self.consume();
                    }
                    self.tok(TokenKind::Numeral)
                }
                _ => panic!("unexpected character (= {:?}) while scanning for hexdec numeral"),
            },
        }
    }

    fn scan_binary_numeral(&mut self) -> Token {
        debug_assert!(self.peek().is_some());
        debug_assert_eq!(self.peek().unwrap(), 'b');

        self.consume();
        match self.peek() {
            None => panic!("unexpected end of file while scanning for binary numeral"),
            Some(peek) => match peek {
                c if c.is_digit(2) => {
                    while let Some(peek) = self.peek() {
                        if !peek.is_digit(2) {
                            break;
                        }
                        self.consume();
                    }
                    self.tok(TokenKind::Numeral)
                }
                _ => panic!("unexpected character (= {:?}) while scanning for binary numeral"),
            },
        }
    }

    fn scan_binary_or_hexdec_numeral(&mut self) -> Token {
        debug_assert!(self.peek().is_some());
        debug_assert_eq!(self.peek().unwrap(), '#');

        self.consume();
        match self.peek() {
            None => panic!("unexpected end of file while scanning binary or hexdec numeral"),
            Some(peek) => match peek {
                'x' => self.scan_hexdec_numeral(),
                'b' => self.scan_binary_numeral(),
                _ => {
                    panic!("unexpected character (= {:?}) while scanning binary or hexdec numeral")
                }
            },
        }
    }

    fn next_token(&mut self) -> Token {
        use self::TokenKind::*;
        let peek = match self.peek() {
            Some(peek) => peek,
            None => return self.tok(EndOfFile),
        };
        match peek {
            c if c.is_whitespace() => self.scan_whitespace(),
            c if c.is_digit(10) => self.scan_numeral_or_decimal(),
            ';' => self.scan_comment(),
            '(' => self.consume().tok(OpenParen),
            ')' => self.consume().tok(CloseParen),
            '#' => self.scan_binary_or_hexdec_numeral(),
            _ => self.consume().tok(Unknown),
        }
    }
}

impl<'c> Iterator for LexemeIter<'c> {
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
            assert_input("; this is a comment", vec![(TokenKind::Comment, (0, 18))]);
        }

        #[test]
        fn multi_line() {
            assert_input(
                indoc!(
                    "; first line
                     ; second line
                     ; third line"
                ),
                vec![
                    (TokenKind::Comment, (0, 12)),
                    (TokenKind::Comment, (13, 26)),
                    (TokenKind::Comment, (27, 38)),
                ],
            );
        }

        #[test]
        fn multiple_semi_colons() {
            assert_input(";;;;;", vec![(TokenKind::Comment, (0, 4))]);
        }

        #[test]
        fn empty_lines() {
            assert_input(
                ";\n;\n;",
                vec![
                    (TokenKind::Comment, (0, 1)),
                    (TokenKind::Comment, (2, 3)),
                    (TokenKind::Comment, (4, 4)),
                ],
            );
        }
    }

    mod whitespace {
        use super::*;

        #[test]
        fn any() {
            assert_input(" \t\n\r", vec![(TokenKind::Whitespace, (0, 3))]);
        }
    }

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

        #[test]
        fn open_close() {
            assert_input(
                "()",
                vec![
                    (TokenKind::OpenParen, (0, 0)),
                    (TokenKind::CloseParen, (1, 1)),
                ],
            );
        }

        #[test]
        fn nested() {
            assert_input(
                "(())",
                vec![
                    (TokenKind::OpenParen, (0, 0)),
                    (TokenKind::OpenParen, (1, 1)),
                    (TokenKind::CloseParen, (2, 2)),
                    (TokenKind::CloseParen, (3, 3)),
                ],
            );
        }
    }

    mod numeral {
        use super::*;

        #[test]
        fn single_zero() {
            assert_input("0", vec![(TokenKind::Numeral, (0, 0))]);
        }

        #[test]
        fn multiple_zeros() {
            assert_input("000", vec![(TokenKind::Numeral, (0, 2))]);
        }

        #[test]
        fn simple() {
            assert_input("123456789", vec![(TokenKind::Numeral, (0, 8))]);
        }
    }

    mod decimal {
        use super::*;

        #[test]
        fn zero_dot_zero() {
            assert_input("0.0", vec![(TokenKind::Decimal, (0, 2))])
        }

        #[test]
        fn multiple_zero_dot_zero() {
            assert_input("00.0", vec![(TokenKind::Decimal, (0, 3))])
        }

        #[test]
        fn simple() {
            assert_input("12345.67890", vec![(TokenKind::Decimal, (0, 10))])
        }

        #[test]
        fn non_zero_start() {
            assert_input("7.77", vec![(TokenKind::Decimal, (0, 3))])
        }

        #[test]
        #[should_panic]
        fn zero_missing_after_dot_err() {
            assert_input("0.", vec![])
        }

        #[test]
        #[should_panic]
        fn one_missing_after_dot_err() {
            assert_input("1.", vec![])
        }

        #[test]
        #[should_panic]
        fn double_dot_err() {
            assert_input("1..2", vec![])
        }
    }

    mod hexdec_numeral {
        use super::*;

        #[test]
        fn zero() {
            assert_input("#x0", vec![(TokenKind::Numeral, (0, 2))])
        }

        #[test]
        fn whole_range_upper_case() {
            assert_input("#xFEDCBA9876543210", vec![(TokenKind::Numeral, (0, 17))])
        }

        #[test]
        fn whole_range_lower_case() {
            assert_input("#xfedcba9876543210", vec![(TokenKind::Numeral, (0, 17))])
        }

        #[test]
        #[should_panic]
        fn empty_after_x_err() {
            assert_input("#x", vec![])
        }
    }

    mod binary_numeral {
        use super::*;

        #[test]
        fn zero() {
            assert_input("#b0", vec![(TokenKind::Numeral, (0, 2))])
        }

        #[test]
        fn whole_range_upper_case() {
            assert_input("#b01", vec![(TokenKind::Numeral, (0, 3))])
        }

        #[test]
        fn long() {
            assert_input("#b01101101010111001", vec![(TokenKind::Numeral, (0, 18))])
        }

        #[test]
        #[should_panic]
        fn empty_after_x_err() {
            assert_input("#b", vec![])
        }

        #[test]
        #[should_panic]
        fn out_of_bounds_digit_err() {
            assert_input("#b012", vec![])
        }
    }
}
