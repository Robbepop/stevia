use lexer::{Loc, Span, Token, TokenKind};

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

    fn scan_string_literal(&mut self) -> Token {
        debug_assert!(self.peek().is_some());
        debug_assert_eq!(self.peek().unwrap(), '"');

        self.consume();
        'outer: while let Some(peek) = self.peek() {
            self.consume();
            if peek == '"' {
                match self.peek() {
                    None => return self.tok(TokenKind::StringLiteral),
                    Some(peek) => match peek {
                        '"' => {
                            self.consume();
                            continue 'outer;
                        }
                        _ => return self.tok(TokenKind::StringLiteral),
                    },
                }
            }
        }
        panic!("unexpected end of file before closing the current string literal")
    }

    fn scan_simple_symbol(&mut self) -> Token {
        debug_assert!(self.peek().is_some());
        debug_assert!(is_symbol_char(self.peek().unwrap()));

        while let Some(peek) = self.peek() {
            if !(peek.is_digit(10) || is_symbol_char(peek)) {
                break;
            }
            self.consume();
        }
        self.tok(TokenKind::SimpleSymbol)
    }

    fn scan_keyword(&mut self) -> Token {
        debug_assert!(self.peek().is_some());
        debug_assert_eq!(self.peek().unwrap(), ':');

        self.consume();
        if self.peek().is_none() {
            panic!("unexpected end of file while scanning for keyword")
        }
        let peek = self.peek().unwrap();
        if !(peek.is_digit(10) || is_symbol_char(peek)) {
            panic!("unexpected character (= {:?}) while scanning for keyword")
        }
        self.consume();
        while let Some(peek) = self.peek() {
            if !(peek.is_digit(10) || is_symbol_char(peek)) {
                break;
            }
            self.consume();
        }
        self.tok(TokenKind::Keyword)
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
            c if is_symbol_char(c) => self.scan_simple_symbol(),
            ';' => self.scan_comment(),
            ':' => self.scan_keyword(),
            '(' => self.consume().tok(OpenParen),
            ')' => self.consume().tok(CloseParen),
            '#' => self.scan_binary_or_hexdec_numeral(),
            '"' => self.scan_string_literal(),
            _ => self.consume().tok(Unknown),
        }
    }
}

fn is_symbol_punctuation(ch: char) -> bool {
    match ch {
        | '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-' | '+' | '=' | '<' | '>' | '.'
        | '?' | '/' => true,
        _ => false,
    }
}

fn is_symbol_char(ch: char) -> bool {
    ch.is_ascii_alphabetic() || is_symbol_punctuation(ch)
}

impl<'c> Iterator for LexemeIter<'c> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let tok = self.next_token();
        if let TokenKind::EndOfFile = tok.kind() {
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

    mod string_literal {
        use super::*;

        #[test]
        fn empty() {
            assert_input(r#""""#, vec![(TokenKind::StringLiteral, (0, 1))])
        }

        #[test]
        fn single_char() {
            assert_input(r#""a""#, vec![(TokenKind::StringLiteral, (0, 2))])
        }

        #[test]
        fn escaped_quote() {
            assert_input(r#""""""#, vec![(TokenKind::StringLiteral, (0, 3))])
        }

        #[test]
        fn new_line() {
            assert_input(
                indoc!(
                    "\"first
                 second\""
                ),
                vec![(TokenKind::StringLiteral, (0, 13))],
            )
        }

        #[test]
        fn seperating_whitespace() {
            assert_input(
                "\"this is a string literal\"",
                vec![(TokenKind::StringLiteral, (0, 25))],
            )
        }

        #[test]
        fn ignore_default_escapes() {
            assert_input(r#""\n\r\t\\""#, vec![(TokenKind::StringLiteral, (0, 9))])
        }

        #[test]
        #[should_panic]
        fn unexpected_end_of_file() {
            assert_input(r#""not terminated correctly"#, vec![])
        }
    }

    mod simple_symbol {
        use super::*;

        #[test]
        fn single_punctuation() {
            fn assert_single_punctuation(punctuation: &str) {
                assert_input(punctuation, vec![(TokenKind::SimpleSymbol, (0, 0))]);
            }
            assert_single_punctuation("~");
            assert_single_punctuation("!");
            assert_single_punctuation("@");
            assert_single_punctuation("$");
            assert_single_punctuation("%");
            assert_single_punctuation("^");
            assert_single_punctuation("&");
            assert_single_punctuation("*");
            assert_single_punctuation("_");
            assert_single_punctuation("-");
            assert_single_punctuation("+");
            assert_single_punctuation("=");
            assert_single_punctuation("<");
            assert_single_punctuation(">");
            assert_single_punctuation(".");
        }

        #[test]
        fn selection() {
            assert_input("<=", vec![(TokenKind::SimpleSymbol, (0, 1))]);
            assert_input("x", vec![(TokenKind::SimpleSymbol, (0, 0))]);
            assert_input("plus", vec![(TokenKind::SimpleSymbol, (0, 3))]);
            assert_input("**", vec![(TokenKind::SimpleSymbol, (0, 1))]);
            assert_input("<sas", vec![(TokenKind::SimpleSymbol, (0, 3))]);
            assert_input("<adf>", vec![(TokenKind::SimpleSymbol, (0, 4))]);
            assert_input("abc77", vec![(TokenKind::SimpleSymbol, (0, 4))]);
            assert_input("*$s&6", vec![(TokenKind::SimpleSymbol, (0, 4))]);
            assert_input(".kkk", vec![(TokenKind::SimpleSymbol, (0, 3))]);
            assert_input(".8", vec![(TokenKind::SimpleSymbol, (0, 1))]);
            assert_input("+34", vec![(TokenKind::SimpleSymbol, (0, 2))]);
            assert_input("-32", vec![(TokenKind::SimpleSymbol, (0, 2))]);
            assert_input("SMTLib2.0", vec![(TokenKind::SimpleSymbol, (0, 8))]);
            assert_input("this_is-unfortunate", vec![(TokenKind::SimpleSymbol, (0, 18))]);
        }
    }

    mod keyword {
        use super::*;

        #[test]
        #[should_panic]
        fn empty() {
            assert_input(":", vec![]);
        }

        #[test]
        fn selection() {
            assert_input(":date", vec![(TokenKind::Keyword, (0, 4))]);
            assert_input(":a2", vec![(TokenKind::Keyword, (0, 2))]);
            assert_input(":foo-bar", vec![(TokenKind::Keyword, (0, 7))]);
            assert_input(":<=", vec![(TokenKind::Keyword, (0, 2))]);
            assert_input(":42", vec![(TokenKind::Keyword, (0, 2))]);
            assert_input(":-56", vec![(TokenKind::Keyword, (0, 3))]);
            assert_input(":->", vec![(TokenKind::Keyword, (0, 2))]);
        }
    }
}
