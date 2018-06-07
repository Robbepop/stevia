use lexer::{Span};

use std::{fmt, error, result};

pub type LexerResult<T> = result::Result<T, LexerError>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum LexerErrorKind {
    UnexpectedEndOfFile,
    UnexpectedCharacter(char),
    PreviousErrorOccured,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LexerError {
    kind: LexerErrorKind,
    span: Span,
    context: Option<String>,
}

impl LexerError {
    pub(crate) fn new(kind: LexerErrorKind, span: Span) -> Self {
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

    #[cfg(test)]
    pub fn clear_context(&mut self) {
        self.context = None;
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

    pub fn previous_error_occured(span: Span) -> Self {
        Self::new(LexerErrorKind::PreviousErrorOccured, span)
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
            ),
            PreviousErrorOccured => write!(
                f,
                "error c({}:{}): cannot continue lexing: previous error occured: {:?}",
                self.span.begin.to_u32(),
                self.span.end.to_u32(),
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
            PreviousErrorOccured => "previous error occured"
        }
    }
}
