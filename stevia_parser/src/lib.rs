#[cfg_attr(test, macro_use)]
extern crate indoc;

#[macro_use]
extern crate lazy_static;

mod lexer;
mod parser;
mod commands;

pub use self::{
    lexer::{
        LexerError,
        LexerErrorKind,
        smtlib2_tokens,
        TokenIter,
        Loc,
        Span,
        Command
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
        OutputChannelBase,
        OutputChannel,
        OptionAndValueBase,
        OptionAndValue,
        SMTLib2Solver
    }
};
