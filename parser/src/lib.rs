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
        parse_smtlib2_with_default_builder,
        ParseError,
        ParseErrorKind,
        ParseResult,
        PropLitsIter,
        Expr,
        SExpr,
        Atom,
        Symbol,
        Keyword,
        LiteralKind,
        Literal,
        Radix,
        Numeral,
        NumeralError,
        NumeralResult,
        Decimal,
        DecimalError,
        DecimalResult,
        ExprBuilder,
        DefaultExprBuilder,
        BuildError,
    },
    solver::{
        InfoAndValue,
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
