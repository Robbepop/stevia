mod parser;
mod error;

use self::{
    parser::{
        parse_smtlib2,
        Parser
    },
    error::{
        ParseResult,
        ParseErrorKind,
        ParseError
    }
};
