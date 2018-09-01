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
        scan_smtlib2,
        LexerError,
        LexerErrorKind,
        Loc,
        Span,
        TokenIter,
    },
    parser::{
        parse_smtlib2,
        ParseError,
        ParseErrorKind,
        ParseResult,
        PropLitsIter,
    },
    solver::{
        DecimalLit,
        InfoAndValue,
        Literal,
        NumeralLit,
        OptionAndValue,
        OptionKind,
        OutputChannel,
        ProblemCategory,
        ProblemStatus,
        ResponseError,
        ResponseResult,
        SMTLib2Solver,
    },
};
