use ast::prelude::*;

use std::result;
use std::error;
use std::fmt;

/// Module for exports of commonly used items of this module.
pub mod prelude {
	pub use super::{
        TypeError,
		TypeErrorKind,
		TypeResult
	};
}

/// A special `Result` type where the error part is always a `TypeError`.
pub type TypeResult<T> = result::Result<T, TypeError>;

/// The concrete type of a `TypeError`.
/// 
/// This also stores some additional helpful information about the specific error.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TypeErrorKind {
	/// Error upon encountering an unexpected type kind of an expression.
	UnexpectedTypeKind{
		/// The expected type kind.
		kind: TypeKind,
		/// The expression with the unexpected type kind.
		expr: AnyExpr
	},
	/// Error upon encountering an unexpected type of an expression.
	UnexpectedType{
		/// The expected type.
		ty: Type,
		/// The expression with the unexpected type.
		expr: AnyExpr
	},
	/// Error upon encountering two expressions with different types when the same type was expected.
    TypeMismatch{
		/// The left hand-side expression with an unequal type to the right hand-side expression.
		lhs: AnyExpr,
		/// The right hand-side expression with an unequal type to the left hand-side expression.
		rhs: AnyExpr
    }
}

/// An error that may be returned by type checking procedures.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct TypeError {
	// The concrete type of this error.
    pub kind: TypeErrorKind
}

impl TypeError {
	/// Creates a new `TypeError` from the given `TypeErrorKind`.
	fn new(kind: TypeErrorKind) -> TypeError {
		TypeError{kind}
	}

	/// Returns a `TypeError` that indicates an unexpected type kind for the given expression.
	pub fn unexpected_type_kind<E>(kind: TypeKind, expr: E) -> TypeError
		where E: Into<AnyExpr>
	{
		TypeError::new(TypeErrorKind::UnexpectedTypeKind{ kind, expr: expr.into() })
	}

	/// Returns a `TypeError` that indicates an unexpected type for the given expression.
	pub fn unexpected_type<T, E>(ty: T, expr: E) -> TypeError
		where T: Into<Type>,
		      E: Into<AnyExpr>
	{
		TypeError::new(TypeErrorKind::UnexpectedType{ ty: ty.into(), expr: expr.into() })
	}

	/// Returns a `TypeError` that indicates an unexpected type mismatch between the given `lhs` and `rhs` expressions.
	pub fn type_mismatch<L, R>(lhs: L, rhs: R) -> TypeError
		where L: Into<AnyExpr>,
		      R: Into<AnyExpr>
	{
		// TODO 2018-03-26: debug assert `lhs` and `rhs` for common type (may panic)
		TypeError::new(TypeErrorKind::TypeMismatch{ lhs: lhs.into(), rhs: rhs.into() })
	}
}

impl fmt::Display for TypeError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::TypeErrorKind::*;
		match &self.kind {
			UnexpectedTypeKind{kind, expr} => {
				write!(f, "Unexpected type kind (= {:?}) for expression (= {:?}), expected type kind: {:?}",
					expr.ty().kind(), expr, kind)
			}
			UnexpectedType{ty, expr} => {
				write!(f, "Unexpected type (= {:?}) for expression (= {:?}), expected type: {:?}",
					expr.ty(), expr, ty)
			}
			TypeMismatch{lhs, rhs} => {
				write!(f, "Unexpected type mismatch of left expression (= {:?}) of type (= {:?}) \
				           and right expression (= {:?}) of type (= {:?})",
				       lhs, lhs.ty(), rhs, rhs.ty())
			}
		}
	}
}

impl error::Error for TypeError {
	fn description(&self) -> &str {
		use self::TypeErrorKind::*;
		match self.kind {
			UnexpectedTypeKind{..} => {
				"Unexpected type kind for expression"
			}
			UnexpectedType{..} => {
				"Unexpected type for expression"
			}
			TypeMismatch{..} => {
				"Unexpected type mismatch for expressions"
			}
		}
	}
}
