#[cfg_attr(test, macro_use)]
extern crate indoc;

#[macro_use]
extern crate lazy_static;

extern crate either;

mod lexer;
mod parser;
mod solver;

pub use self::{
    lexer::{
        LexerError,
        LexerErrorKind,
        scan_smtlib2,
        TokenIter,
        Loc,
        Span
    },
    parser::{
        parse_smtlib2,
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
