//! Lexer for the SMTLib 2.6 standard
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

mod error;
mod raw_lexer;
mod simple_lexer;
mod repr;

pub use self::{
    error::{
        LexerError,
        LexerErrorKind,
        LexerResult
    },
    raw_lexer::{
        raw_smtlib2_tokens,
        RawTokenIter
    },
    simple_lexer::{
        
    },
    repr::{
        Loc,
        Span,
        RawTokenKind,
        RawToken
    }
};
