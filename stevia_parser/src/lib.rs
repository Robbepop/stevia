#[cfg_attr(test, macro_use)]
extern crate indoc;

#[macro_use]
extern crate lazy_static;

mod lexer;
mod parser;
mod commands;
pub mod solver;

pub use self::{
    lexer::{
        LexerError,
        LexerErrorKind,
        smtlib2_tokens,
        TokenIter,
        Loc,
        Span
    },
    parser::{
        parse_smtlib2,
        Parser,
        PropLitsIter,
        ParseResult,
        ParseErrorKind,
        ParseError
    },
    commands::{
        ResponseError,
        ResponseResult,
        OptionKindBase,
        OptionKind,
        LiteralBase,
        Literal,
        NumeralLitBase,
        DecimalLitBase,
        OutputChannelBase,
        OutputChannel,
        OptionAndValueBase,
        OptionAndValue,
        SetInfoKindBase,
        SetInfoKind,
        SMTLib2Solver,
        CategoryKind,
        StatusKind,
    }
};
