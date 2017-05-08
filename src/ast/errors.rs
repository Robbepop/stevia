
use ast::Type;

// use std::error::Error;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrorKind {
	TypeError{given: Type, expected: Type},
	TooFewChildren{given: usize, expected_min: usize}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AstError {

}

// impl ::std::error::Error for AstError { /* TODO */ }

pub type Result<T> = ::std::result::Result<T, AstError>;
