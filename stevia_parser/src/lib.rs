#[cfg_attr(test, macro_use)]
extern crate indoc;

#[macro_use]
extern crate lazy_static;

extern crate either;

mod lexer;
mod parser;
// mod commands;
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
    solver::{
        ResponseError,
        ResponseResult,
        OptionKind,
        Literal,
        NumeralLit,
        DecimalLit,
        OutputChannel,
        OptionAndValue,
        InfoAndValue,
        SMTLib2Solver,
        ProblemCategory,
        ProblemStatus
    }
};
