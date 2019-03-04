use crate::lexer::{
    LexerError,
    LexerResult,
    Loc,
    RawToken,
    RawTokenKind,
    Span,
};

pub fn raw_smtlib2_tokens(input: &str) -> RawTokenIter {
    RawTokenIter::new(input)
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
pub struct RawTokenIter<'c> {
    /// The input iterator over characters and their byte offsets.
    input: CharIndices<'c>,
    /// The input string slice.
    ///
    /// # Note
    ///
    /// `CharIndices::as_str` cannot be used since it returns the remaining
    /// string slice instead of the full which is required.
    input_str: &'c str,
    /// The location of the token that is to be yielded next.
    loc: Span,
    /// The currently peeked token and its byte position.
    peek: Option<CharAndLoc>,
    /// If an error has already occured.
    ///
    /// # Note
    ///
    /// This is important to only return errors after the first error has happened.
    error_occured: bool,
}

impl<'c> RawTokenIter<'c> {
    pub(self) fn new(input: &'c str) -> Self {
        let mut iter = RawTokenIter {
            input: input.char_indices(),
            input_str: input,
            loc: Span::zero(),
            peek: None,
            error_occured: false,
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

    fn tok(&mut self, kind: RawTokenKind) -> RawToken {
        let tok = RawToken::new(kind, self.loc);
        if let Some(peek) = self.peek {
            self.loc.begin = peek.loc;
        };
        tok
    }

    pub(crate) fn span_to_str(&self, span: Span) -> &str {
        debug_assert!(!self.input_str.as_bytes().is_empty());
        debug_assert!(span.begin.to_usize() < self.input_str.as_bytes().len());
        debug_assert!(span.end.to_usize() < self.input_str.as_bytes().len());
        unsafe {
            self.input_str
                .get_unchecked(span.begin.to_usize()..span.end.to_usize() + 1)
        }
    }

    fn unexpected_char<C>(&mut self, ch: char, opt_ctx: C) -> LexerError
    where
        C: Into<Option<&'static str>>,
    {
        debug_assert!(self.peek().is_some());

        self.error_occured = true;
        self.consume();
        let err = LexerError::unexpected_character(self.loc, ch);
        if let Some(ctx) = opt_ctx.into() {
            return err.context_msg(ctx.to_owned());
        }
        err
    }

    fn unexpected_end_of_file<C>(&mut self, opt_ctx: C) -> LexerError
    where
        C: Into<Option<&'static str>>,
    {
        self.error_occured = true;
        let err = LexerError::unexpected_end_of_file(self.loc);
        if let Some(ctx) = opt_ctx.into() {
            return err.context_msg(ctx.to_owned());
        }
        err
    }

    fn scan_whitespace(&mut self) -> LexerResult<RawToken> {
        debug_assert!(self.peek().is_some());
        debug_assert!(self.peek().unwrap().is_whitespace());

        while let Some(peek) = self.peek() {
            if !peek.is_whitespace() {
                break;
            }
            self.consume();
        }
        Ok(self.tok(RawTokenKind::Whitespace))
    }

    fn scan_comment(&mut self) -> LexerResult<RawToken> {
        debug_assert!(self.peek().is_some());
        debug_assert_eq!(self.peek().unwrap(), ';');

        fn is_line_ending(ch: char) -> bool {
            ch == '\n' || ch == '\r'
        }
        while let Some(peek) = self.peek() {
            self.consume();
            if is_line_ending(peek) {
                break;
            }
        }
        Ok(self.tok(RawTokenKind::Comment))
    }

    fn scan_numeral(&mut self) -> LexerResult<RawToken> {
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
        Ok(self.tok(RawTokenKind::Numeral))
    }

    fn scan_decimal(&mut self) -> LexerResult<RawToken> {
        debug_assert!(self.peek().is_some());
        debug_assert!(self.peek().unwrap() == '.');

        self.consume();
        match self.peek() {
            None => Err(self.unexpected_end_of_file("while scanning for a decimal number")),
            Some(peek) => match peek {
                c if c.is_digit(10) => {
                    while let Some(peek) = self.peek() {
                        if !peek.is_digit(10) {
                            break;
                        }
                        self.consume();
                    }
                    Ok(self.tok(RawTokenKind::Decimal))
                }
                c => Err(self.unexpected_char(c, "while scanning for a decimal number")),
            },
        }
    }

    fn scan_numeral_or_decimal(&mut self) -> LexerResult<RawToken> {
        debug_assert!(self.peek().is_some());
        debug_assert!(self.peek().unwrap().is_digit(10));

        match self.peek().unwrap() {
            '0' => {
                match self.consume().peek() {
                    None => Ok(self.tok(RawTokenKind::Numeral)),
                    Some(peek) => match peek {
                        '.' => self.scan_decimal(),
                        c if c.is_digit(10) => self.scan_numeral(),
                        c => Err(self
                            .unexpected_char(c, "while scanning for numeral or decimal literal")),
                    },
                }
            }
            _ => self.scan_numeral(),
        }
    }

    fn scan_hexdec_numeral(&mut self) -> LexerResult<RawToken> {
        debug_assert!(self.peek().is_some());
        debug_assert_eq!(self.peek().unwrap(), 'x');

        self.consume();
        match self.peek() {
            None => Err(self.unexpected_end_of_file("while scanning for hexdec numeral")),
            Some(peek) => match peek {
                c if c.is_digit(16) => {
                    'inner: while let Some(peek) = self.peek() {
                        if peek.is_digit(16) {
                            self.consume();
                            continue 'inner;
                        }
                        if peek == '(' || peek == ')' || peek.is_whitespace() {
                            return Ok(self.tok(RawTokenKind::Numeral));
                        }
                        return Err(self.unexpected_char(peek, "while scanning for hexdec numeral"));
                    }
                    Ok(self.tok(RawTokenKind::Numeral))
                }
                c => Err(self.unexpected_char(c, "while scanning for hexdec numeral")),
            },
        }
    }

    fn scan_binary_numeral(&mut self) -> LexerResult<RawToken> {
        debug_assert!(self.peek().is_some());
        debug_assert_eq!(self.peek().unwrap(), 'b');

        self.consume();
        match self.peek() {
            None => Err(self.unexpected_end_of_file("while scanning for binary numeral")),
            Some(peek) => match peek {
                c if c.is_digit(2) => {
                    'inner: while let Some(peek) = self.peek() {
                        if peek.is_digit(2) {
                            self.consume();
                            continue 'inner;
                        }
                        if peek == '(' || peek == ')' || peek.is_whitespace() {
                            return Ok(self.tok(RawTokenKind::Numeral));
                        }
                        return Err(self.unexpected_char(peek, "while scanning for binary numeral"));
                    }
                    Ok(self.tok(RawTokenKind::Numeral))
                }
                c => Err(self.unexpected_char(c, "while scanning for binary numeral")),
            },
        }
    }

    fn scan_binary_or_hexdec_numeral(&mut self) -> LexerResult<RawToken> {
        debug_assert!(self.peek().is_some());
        debug_assert_eq!(self.peek().unwrap(), '#');

        self.consume();
        match self.peek() {
            None => Err(self.unexpected_end_of_file("while scanning for binary or hexdec numeral")),
            Some(peek) => match peek {
                'x' => self.scan_hexdec_numeral(),
                'b' => self.scan_binary_numeral(),
                c => Err(self.unexpected_char(c, "while scanning for binary or hexdec numeral")),
            },
        }
    }

    fn scan_string_literal(&mut self) -> LexerResult<RawToken> {
        debug_assert!(self.peek().is_some());
        debug_assert_eq!(self.peek().unwrap(), '"');

        self.consume();
        'outer: while let Some(peek) = self.peek() {
            self.consume();
            if peek == '"' {
                match self.peek() {
                    None => return Ok(self.tok(RawTokenKind::String)),
                    Some(peek) => match peek {
                        '"' => {
                            self.consume();
                            continue 'outer;
                        }
                        _ => return Ok(self.tok(RawTokenKind::String)),
                    },
                }
            }
        }
        Err(self.unexpected_end_of_file("before closing the current string literal"))
    }

    fn scan_simple_symbol(&mut self) -> LexerResult<RawToken> {
        debug_assert!(self.peek().is_some());
        debug_assert!(is_symbol_char(self.peek().unwrap()));

        while let Some(peek) = self.peek() {
            if peek.is_digit(10) || is_symbol_char(peek) {
                self.consume();
                continue;
            }
            if peek.is_whitespace() || peek == '(' || peek == ')' {
                return Ok(self.tok(RawTokenKind::SimpleSymbol));
            }
            return Err(self.unexpected_char(peek, "while scanning for a simple symbol"));
        }
        Ok(self.tok(RawTokenKind::SimpleSymbol))
    }

    fn scan_keyword(&mut self) -> LexerResult<RawToken> {
        debug_assert!(self.peek().is_some());
        debug_assert_eq!(self.peek().unwrap(), ':');

        self.consume();
        if self.peek().is_none() {
            return Err(self.unexpected_end_of_file("while scanning for keyword"));
        }
        let peek = self.peek().unwrap();
        if !(peek.is_digit(10) || is_symbol_char(peek)) {
            return Err(self.unexpected_char(peek, "while scanning for keyword"));
        }
        self.consume();
        while let Some(peek) = self.peek() {
            if !(peek.is_digit(10) || is_symbol_char(peek)) {
                break;
            }
            self.consume();
        }
        Ok(self.tok(RawTokenKind::Keyword))
    }

    fn scan_quoted_symbol(&mut self) -> LexerResult<RawToken> {
        debug_assert!(self.peek().is_some());
        debug_assert_eq!(self.peek().unwrap(), '|');

        self.consume();
        while let Some(peek) = self.peek() {
            self.consume();
            if peek == '\\' {
                return Err(self.unexpected_char('\\', "while scanning for quoted symbol"));
            }
            if peek == '|' {
                return Ok(self.tok(RawTokenKind::QuotedSymbol));
            }
        }
        Err(self.unexpected_end_of_file("while scanning for quoted symbol"))
    }

    pub fn next_token(&mut self) -> LexerResult<RawToken> {
        if self.error_occured {
            return Err(LexerError::previous_error_occured(self.loc));
        }
        if self.peek().is_none() {
            return Err(self.unexpected_end_of_file(None));
        }
        use self::RawTokenKind::*;
        match self.peek().unwrap() {
            c if c.is_whitespace() => self.scan_whitespace(),
            c if c.is_digit(10) => self.scan_numeral_or_decimal(),
            c if is_symbol_char(c) => self.scan_simple_symbol(),
            ';' => self.scan_comment(),
            ':' => self.scan_keyword(),
            '(' => Ok(self.consume().tok(OpenParen)),
            ')' => Ok(self.consume().tok(CloseParen)),
            '#' => self.scan_binary_or_hexdec_numeral(),
            '"' => self.scan_string_literal(),
            '|' => self.scan_quoted_symbol(),
            c => Err(self.unexpected_char(c, "while scanning for the start of a new token")),
        }
    }
}

fn is_symbol_punctuation(ch: char) -> bool {
    match ch {
        '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-' | '+' | '=' | '<' | '>' | '.'
        | '?' | '/' => true,
        _ => false,
    }
}

fn is_symbol_char(ch: char) -> bool {
    ch.is_ascii_alphabetic() || is_symbol_punctuation(ch)
}

impl<'c> Iterator for RawTokenIter<'c> {
    type Item = RawToken;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token().ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::LexerErrorKind;

    fn assert_input<I>(input: &str, expected_toks: I)
    where
        I: IntoIterator<Item = (RawTokenKind, (u32, u32))>,
    {
        let expected_toks = expected_toks
            .into_iter()
            .map(|(kind, (begin, end))| {
                RawToken::new(kind, Span::new(Loc::from(begin), Loc::from(end)))
            }).collect::<Vec<_>>();
        let actual_toks = raw_smtlib2_tokens(input).collect::<Vec<_>>();
        assert_eq!(actual_toks.len(), expected_toks.len());
        for (actual, expected) in actual_toks.into_iter().zip(expected_toks.into_iter()) {
            assert_eq!(actual, expected);
        }
    }

    type RawResult = ::std::result::Result<RawTokenKind, LexerErrorKind>;

    fn assert_raw_input<I>(input: &str, expected_toks: I)
    where
        I: IntoIterator<Item = (RawResult, (u32, u32))>,
    {
        let expected_toks = expected_toks.into_iter().map(|(raw, (begin, end))| {
            let loc = Span::new(Loc::from(begin), Loc::from(end));
            raw.map(|tok| RawToken::new(tok, loc))
                .map_err(|err| LexerError::new(err, loc))
        });
        let mut actual_toks = raw_smtlib2_tokens(input);
        for expected in expected_toks {
            let actual = actual_toks.next_token().map_err(|mut err| {
                err.clear_context();
                err
            });
            assert_eq!(actual, expected)
        }
    }

    #[test]
    fn ret_errors_after_encountering_one() {
        assert_raw_input(
            "\0",
            vec![
                (Err(LexerErrorKind::UnexpectedCharacter('\0')), (0, 0)),
                (Err(LexerErrorKind::PreviousErrorOccured), (0, 0)),
            ],
        );
    }

    mod comment {
        use super::*;

        #[test]
        fn single_line() {
            assert_input(
                "; this is a comment",
                vec![(RawTokenKind::Comment, (0, 18))],
            );
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
                    (RawTokenKind::Comment, (0, 12)),
                    (RawTokenKind::Comment, (13, 26)),
                    (RawTokenKind::Comment, (27, 38)),
                ],
            );
        }

        #[test]
        fn multiple_semi_colons() {
            assert_input(";;;;;", vec![(RawTokenKind::Comment, (0, 4))]);
        }

        #[test]
        fn empty_lines() {
            assert_input(
                ";\n;\n;",
                vec![
                    (RawTokenKind::Comment, (0, 1)),
                    (RawTokenKind::Comment, (2, 3)),
                    (RawTokenKind::Comment, (4, 4)),
                ],
            );
        }
    }

    mod whitespace {
        use super::*;

        #[test]
        fn any() {
            assert_input(" \t\n\r", vec![(RawTokenKind::Whitespace, (0, 3))]);
        }
    }

    mod paren {
        use super::*;

        #[test]
        fn open() {
            assert_input("(", vec![(RawTokenKind::OpenParen, (0, 0))]);
        }

        #[test]
        fn close() {
            assert_input(")", vec![(RawTokenKind::CloseParen, (0, 0))]);
        }

        #[test]
        fn open_close() {
            assert_input(
                "()",
                vec![
                    (RawTokenKind::OpenParen, (0, 0)),
                    (RawTokenKind::CloseParen, (1, 1)),
                ],
            );
        }

        #[test]
        fn nested() {
            assert_input(
                "(())",
                vec![
                    (RawTokenKind::OpenParen, (0, 0)),
                    (RawTokenKind::OpenParen, (1, 1)),
                    (RawTokenKind::CloseParen, (2, 2)),
                    (RawTokenKind::CloseParen, (3, 3)),
                ],
            );
        }
    }

    mod numeral {
        use super::*;

        #[test]
        fn single_zero() {
            assert_input("0", vec![(RawTokenKind::Numeral, (0, 0))]);
        }

        #[test]
        fn multiple_zeros() {
            assert_input("000", vec![(RawTokenKind::Numeral, (0, 2))]);
        }

        #[test]
        fn simple() {
            assert_input("123456789", vec![(RawTokenKind::Numeral, (0, 8))]);
        }
    }

    mod decimal {
        use super::*;

        #[test]
        fn zero_dot_zero() {
            assert_input("0.0", vec![(RawTokenKind::Decimal, (0, 2))])
        }

        #[test]
        fn multiple_zero_dot_zero() {
            assert_input("00.0", vec![(RawTokenKind::Decimal, (0, 3))])
        }

        #[test]
        fn simple() {
            assert_input("12345.67890", vec![(RawTokenKind::Decimal, (0, 10))])
        }

        #[test]
        fn non_zero_start() {
            assert_input("7.77", vec![(RawTokenKind::Decimal, (0, 3))])
        }

        #[test]
        fn zero_missing_after_dot_err() {
            assert_raw_input(
                "0.",
                vec![(Err(LexerErrorKind::UnexpectedEndOfFile), (0, 1))],
            )
        }

        #[test]
        fn one_missing_after_dot_err() {
            assert_raw_input(
                "1.",
                vec![(Err(LexerErrorKind::UnexpectedEndOfFile), (0, 1))],
            );
        }

        #[test]
        fn double_dot_err() {
            assert_raw_input(
                "1..2",
                vec![(Err(LexerErrorKind::UnexpectedCharacter('.')), (0, 2))],
            );
        }
    }

    mod hexdec_numeral {
        use super::*;

        #[test]
        fn zero() {
            assert_input("#x0", vec![(RawTokenKind::Numeral, (0, 2))])
        }

        #[test]
        fn whole_range_upper_case() {
            assert_input("#xFEDCBA9876543210", vec![(RawTokenKind::Numeral, (0, 17))])
        }

        #[test]
        fn whole_range_lower_case() {
            assert_input("#xfedcba9876543210", vec![(RawTokenKind::Numeral, (0, 17))])
        }

        #[test]
        fn empty_after_x_err() {
            assert_raw_input(
                "#x",
                vec![(Err(LexerErrorKind::UnexpectedEndOfFile), (0, 1))],
            );
        }

        #[test]
        fn out_of_bounds_digit_err() {
            assert_raw_input(
                "#xABFG",
                vec![(Err(LexerErrorKind::UnexpectedCharacter('G')), (0, 5))],
            );
        }
    }

    mod binary_numeral {
        use super::*;

        #[test]
        fn zero() {
            assert_input("#b0", vec![(RawTokenKind::Numeral, (0, 2))])
        }

        #[test]
        fn whole_range_upper_case() {
            assert_input("#b01", vec![(RawTokenKind::Numeral, (0, 3))])
        }

        #[test]
        fn long() {
            assert_input(
                "#b01101101010111001",
                vec![(RawTokenKind::Numeral, (0, 18))],
            )
        }

        #[test]
        fn empty_after_x_err() {
            assert_raw_input(
                "#b",
                vec![(Err(LexerErrorKind::UnexpectedEndOfFile), (0, 1))],
            );
        }

        #[test]
        fn out_of_bounds_digit_err() {
            assert_raw_input(
                "#b012",
                vec![(Err(LexerErrorKind::UnexpectedCharacter('2')), (0, 4))],
            );
        }
    }

    mod string_literal {
        use super::*;

        #[test]
        fn empty() {
            assert_input(r#""""#, vec![(RawTokenKind::String, (0, 1))])
        }

        #[test]
        fn single_char() {
            assert_input(r#""a""#, vec![(RawTokenKind::String, (0, 2))])
        }

        #[test]
        fn escaped_quote() {
            assert_input(r#""""""#, vec![(RawTokenKind::String, (0, 3))])
        }

        #[test]
        fn new_line() {
            assert_input(
                indoc!(
                    "\"first
                 second\""
                ),
                vec![(RawTokenKind::String, (0, 13))],
            )
        }

        #[test]
        fn seperating_whitespace() {
            assert_input(
                "\"this is a string literal\"",
                vec![(RawTokenKind::String, (0, 25))],
            )
        }

        #[test]
        fn ignore_default_escapes() {
            assert_input(r#""\n\r\t\\""#, vec![(RawTokenKind::String, (0, 9))])
        }

        #[test]
        fn unexpected_end_of_file() {
            assert_raw_input(
                r#""not terminated correctly"#,
                vec![(Err(LexerErrorKind::UnexpectedEndOfFile), (0, 24))],
            );
        }
    }

    mod simple_symbol {
        use super::*;

        #[test]
        fn unexpected_colon() {
            assert_raw_input(
                "hello:world",
                vec![(Err(LexerErrorKind::UnexpectedCharacter(':')), (0, 5))],
            );
        }

        #[test]
        fn before_close_paren() {
            assert_input(
                "hello)",
                vec![
                    (RawTokenKind::SimpleSymbol, (0, 4)),
                    (RawTokenKind::CloseParen, (5, 5)),
                ],
            );
        }

        #[test]
        fn separated_by_whitespace() {
            assert_input(
                "hello world",
                vec![
                    (RawTokenKind::SimpleSymbol, (0, 4)),
                    (RawTokenKind::Whitespace, (5, 5)),
                    (RawTokenKind::SimpleSymbol, (6, 10)),
                ],
            );
        }

        #[test]
        fn single_punctuation() {
            fn assert_single_punctuation(punctuation: &str) {
                assert_input(punctuation, vec![(RawTokenKind::SimpleSymbol, (0, 0))]);
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
            assert_input("<=", vec![(RawTokenKind::SimpleSymbol, (0, 1))]);
            assert_input("x", vec![(RawTokenKind::SimpleSymbol, (0, 0))]);
            assert_input("plus", vec![(RawTokenKind::SimpleSymbol, (0, 3))]);
            assert_input("**", vec![(RawTokenKind::SimpleSymbol, (0, 1))]);
            assert_input("<sas", vec![(RawTokenKind::SimpleSymbol, (0, 3))]);
            assert_input("<adf>", vec![(RawTokenKind::SimpleSymbol, (0, 4))]);
            assert_input("abc77", vec![(RawTokenKind::SimpleSymbol, (0, 4))]);
            assert_input("*$s&6", vec![(RawTokenKind::SimpleSymbol, (0, 4))]);
            assert_input(".kkk", vec![(RawTokenKind::SimpleSymbol, (0, 3))]);
            assert_input(".8", vec![(RawTokenKind::SimpleSymbol, (0, 1))]);
            assert_input("+34", vec![(RawTokenKind::SimpleSymbol, (0, 2))]);
            assert_input("-32", vec![(RawTokenKind::SimpleSymbol, (0, 2))]);
            assert_input("SMTLib2.0", vec![(RawTokenKind::SimpleSymbol, (0, 8))]);
            assert_input(
                "this_is-unfortunate",
                vec![(RawTokenKind::SimpleSymbol, (0, 18))],
            );
        }
    }

    mod keyword {
        use super::*;

        #[test]
        fn empty() {
            assert_raw_input(
                ":",
                vec![(Err(LexerErrorKind::UnexpectedEndOfFile), (0, 0))],
            );
        }

        #[test]
        fn selection() {
            assert_input(":date", vec![(RawTokenKind::Keyword, (0, 4))]);
            assert_input(":a2", vec![(RawTokenKind::Keyword, (0, 2))]);
            assert_input(":foo-bar", vec![(RawTokenKind::Keyword, (0, 7))]);
            assert_input(":<=", vec![(RawTokenKind::Keyword, (0, 2))]);
            assert_input(":42", vec![(RawTokenKind::Keyword, (0, 2))]);
            assert_input(":-56", vec![(RawTokenKind::Keyword, (0, 3))]);
            assert_input(":->", vec![(RawTokenKind::Keyword, (0, 2))]);
        }
    }

    mod quoted_symbol {
        use super::*;

        #[test]
        fn empty() {
            assert_input("||", vec![(RawTokenKind::QuotedSymbol, (0, 1))]);
        }

        #[test]
        fn single_alpha() {
            assert_input("|a|", vec![(RawTokenKind::QuotedSymbol, (0, 2))]);
        }

        #[test]
        fn backslash_err() {
            assert_raw_input(
                r#"|\|"#,
                vec![(Err(LexerErrorKind::UnexpectedCharacter('\\')), (0, 2))],
            );
        }

        #[test]
        fn missing_ending_pipe() {
            assert_raw_input(
                "|hello",
                vec![(Err(LexerErrorKind::UnexpectedEndOfFile), (0, 5))],
            );
        }

        #[test]
        fn simple_sentence() {
            assert_input(
                "|this is a quoted symbol|",
                vec![(RawTokenKind::QuotedSymbol, (0, 24))],
            );
        }

        #[test]
        fn with_line_break() {
            assert_input(
                indoc!(
                    "|also with
                     line break|"
                ),
                vec![(RawTokenKind::QuotedSymbol, (0, 21))],
            )
        }

        #[test]
        fn with_quote() {
            assert_input(
                r#"| " can occure, too|"#,
                vec![(RawTokenKind::QuotedSymbol, (0, 19))],
            );
        }

        #[test]
        fn many_punctuations() {
            // Note: '´' requires two bytes.
            assert_input(
                r##"|af klj ^*0 asfe2 (&*)&(#^$>> >?" ´]]984|"##,
                vec![(RawTokenKind::QuotedSymbol, (0, 41))],
            );
            assert_input(
                r##"|Löwe 老虎 Léopard|"##,
                vec![(RawTokenKind::QuotedSymbol, (0, 22))],
            );
        }
    }
}
