use lexer::{
    LexerError,
    TokenKind,
};
use solver::{
    Command,
    CommandResponseError,
    ResponseError,
};

pub type ParseResult<T> = ::std::result::Result<T, ParseError>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParseErrorKind {
    LexerError(LexerError),
    ResponseError(CommandResponseError),
    UnexpectedTokenKind {
        found: TokenKind,
        expected: Option<TokenKind>,
    },
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

impl From<CommandResponseError> for ParseError {
    fn from(response_error: CommandResponseError) -> Self {
        Self::new(ParseErrorKind::ResponseError(response_error))
    }
}

impl ParseError {
    pub(self) fn new(kind: ParseErrorKind) -> Self {
        Self {
            kind,
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

    pub fn unexpected_token_kind<T>(found_kind: TokenKind, expected_kind: T) -> Self
    where
        T: Into<Option<TokenKind>>,
    {
        Self::new(ParseErrorKind::UnexpectedTokenKind {
            found: found_kind,
            expected: expected_kind.into(),
        })
    }

    pub fn bad_response(response: ResponseError, invoked_cmd: Command) -> Self {
        Self::from(CommandResponseError::new(response, invoked_cmd))
    }
}
