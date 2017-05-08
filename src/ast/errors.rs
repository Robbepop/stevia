
use ast::Type;

pub enum ErrorKind {
	TypeError{given: Type, expected: Type},
	TooFewChildren{given: usize, expected_min: usize}
}

pub struct AstError {

}

impl Error for AstError {

}

pub type Result<T> = Result<T, AstError>;
