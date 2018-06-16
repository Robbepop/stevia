use lexer::{TokenKind, LexerError};
use commands::{ResponseError};

pub type ParseResult<T> = ::std::result::Result<T, ParseError>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParseErrorKind {
    LexerError(LexerError),
    ResponseError(ResponseError),
    UnexpectedTokenKind{
        found: TokenKind,
        expected: Option<TokenKind>
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParseError {
    kind: ParseErrorKind,
    context: Option<String>,
}

impl From<LexerError> for ParseError {
    fn from(lexer_error: LexerError) -> Self {
        Self::new(ParseErrorKind::LexerError(lexer_error))
    }
}

impl From<ResponseError> for ParseError {
    fn from(response_error: ResponseError) -> Self {
        Self::new(ParseErrorKind::ResponseError(response_error))
    }
}

impl ParseError {
    pub(self) fn new(kind: ParseErrorKind) -> Self {
        Self{ kind, context: None }
    }

    pub fn context_msg<S>(self, msg: S) -> Self
    where
        S: Into<String>
    {
        let mut this = self;
        this.context = Some(msg.into());
        this
    }

    pub fn unexpected_token_kind<T>(found_kind: TokenKind, expected_kind: T) -> Self
    where
        T: Into<Option<TokenKind>>
    {
        Self::new(ParseErrorKind::UnexpectedTokenKind{
            found: found_kind,
            expected: expected_kind.into()
        })
    }
}
