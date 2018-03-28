use ast::prelude::*;

use std::result;
use std::error;
use std::fmt;

/// Module for exports of commonly used items of this module.
pub mod prelude {
	pub use super::{
        ExprError,
		ExprErrorKind,
		ExprResult
	};
}

/// A special `Result` type where the error part is always a `ExprError`.
pub type ExprResult<T> = result::Result<T, ExprError>;

/// The concrete type of a `ExprError`.
/// 
/// This also stores some additional helpful information about the specific error.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum ExprErrorKind {
	/// Errors that are caused by type violations.
	TypeError(TypeError),
	/// Error upon encountering an n-ary expression that was provided with too few child expressions.
    TooFewChildren{
		/// The minimum number of expected child expressions.
		expected_min: usize,
		/// The actual number of given child expressions.
		actual_num: usize,
		/// The expression that has too few child expressions.
		expr: AnyExpr
    }
}

/// An error that may be returned by expression checking procedures.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct ExprError {
	// The kind of this error.
    pub kind: ExprErrorKind
}

impl From<TypeError> for ExprError {
    fn from(type_error: TypeError) -> ExprError {
        ExprError::new(ExprErrorKind::TypeError(type_error))
    }
}

impl ExprError {
	/// Creates a new `ExprError` from the given `ExprErrorKind`.
	fn new(kind: ExprErrorKind) -> ExprError {
		ExprError{kind}
	}

	/// Returns a `ExprError` that indicates that the given expression has too few child expressions.
	pub fn too_few_children<E>(expected_min: usize, actual_num: usize, expr: E) -> ExprError
		where E: Into<AnyExpr>
	{
		// TODO 2018-03-26: debug assert `expr` for too few children (may panic)
		ExprError::new(ExprErrorKind::TooFewChildren{ expected_min, actual_num, expr: expr.into() })
	}
}

impl fmt::Display for ExprError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::ExprErrorKind::*;
		match &self.kind {
			TypeError(type_error) => {
                write!(f, "{}", type_error)
            }
			TooFewChildren{expected_min, actual_num, expr} => {
				write!(f, "Too few children for expression (= {:?}), found {:?} children but \
				           expected at least {:?}.",
				       expr, actual_num, expected_min)
			}
		}
	}
}

impl error::Error for ExprError {
	fn description(&self) -> &str {
		use self::ExprErrorKind::*;
		match &self.kind {
			TypeError(type_error) => {
                type_error.description()
            }
			TooFewChildren{..} => {
				"Too few children for expression"
			}
		}
	}
}
