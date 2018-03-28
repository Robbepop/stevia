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
	/// Error upon encountering a non-boolean type expression when boolean type was expected.
    ExpectedBoolType{
		/// The expression with the unexpected non-boolean type.
        expr: AnyExpr
    },
	/// Error upon encountering a non-bitvector type expression when bitvector type was expected.
    ExpectedBitvecType{
		/// The expression with the unexpected non-bitvector type.
        expr: AnyExpr
    },
	/// Error upon encountering an expression that is not of the given expected concrete bitvector type.
	/// 
	/// Note that the expression might be of bitvector type but still does not satisfy the concrete
	/// bitwidth of the expected bitvector type.
    ExpectedConcreteBitvecType{
		/// The expected concrete bitvector type.
        concrete: BitvecTy,
		/// The expression with the unexpected non concrete bitvector type.
        expr: AnyExpr
    },
	/// Error upon encountering a non-array type expression when array type was expected.
    ExpectedArrayType{
		/// The expression with the unexpected non-array type.
        expr: AnyExpr
    },
	/// Error upon encountering an expression that is not of the given expected concrete array type.
    ExpectedConcreteArrayType{
		/// The expected concrete array type.
        concrete: ArrayTy,
		/// The expression with the unexpected non concrete array type.
        expr: AnyExpr
    },
	/// Error upon encountering two expressions with different types when the same type was expected.
    ExpectedCommonType{
		/// The left hand-side expression with an unequal type to the right hand-side expression.
        lhs: AnyExpr,
		/// The right hand-side expression with an unequal type to the left hand-side expression.
        rhs: AnyExpr
    },
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

	/// Returns a `TypeError` that indicates an unexpected non-boolean type expression.
	pub fn expected_bool_type<E>(expr: E) -> TypeError
		where E: Into<AnyExpr>
	{
		// TODO 2018-03-26: debug assert `expr` for non-boolean type (may panic)
		TypeError::new(TypeErrorKind::ExpectedBoolType{ expr: expr.into() })
	}

	/// Returns a `TypeError` that indicates an unexpected non-bitvector type expression.
	pub fn expected_bitvec_type<E>(expr: E) -> TypeError
		where E: Into<AnyExpr>
	{
		// TODO 2018-03-26: debug assert `expr` for non-bitvector type (may panic)
		TypeError::new(TypeErrorKind::ExpectedBitvecType{ expr: expr.into() })
	}

	/// Returns a `TypeError` that indicates an unexpected non-concrete bitvector type expression.
	pub fn expected_concrete_bitvec_type<E>(bvty: BitvecTy, expr: E) -> TypeError
		where E: Into<AnyExpr>
	{
		// TODO 2018-03-26: debug assert `expr` for non-concrete bitvector type (may panic)
		TypeError::new(TypeErrorKind::ExpectedConcreteBitvecType{ concrete: bvty, expr: expr.into() })
	}

	/// Returns a `TypeError` that indicates an unexpected non-array type expression.
	pub fn expected_array_type<E>(expr: E) -> TypeError
		where E: Into<AnyExpr>
	{
		// TODO 2018-03-26: debug assert `expr` for non-array type (may panic)
		TypeError::new(TypeErrorKind::ExpectedArrayType{ expr: expr.into() })
	}

	/// Returns a `TypeError` that indicates an unexpected non-concrete array type expression.
	pub fn expected_concrete_array_type<E>(array_ty: ArrayTy, expr: E) -> TypeError
		where E: Into<AnyExpr>
	{
		// TODO 2018-03-26: debug assert `expr` for non-concrete array type (may panic)
		TypeError::new(TypeErrorKind::ExpectedConcreteArrayType{ concrete: array_ty, expr: expr.into() })
	}

	/// Returns a `TypeError` that indicates that the given `lhs` and `rhs` expressions
	/// are unexpectedly of non-equal types.
	pub fn expected_common_type<L, R>(lhs: L, rhs: R) -> TypeError
		where L: Into<AnyExpr>,
		      R: Into<AnyExpr>
	{
		// TODO 2018-03-26: debug assert `lhs` and `rhs` for common type (may panic)
		TypeError::new(TypeErrorKind::ExpectedCommonType{ lhs: lhs.into(), rhs: rhs.into() })
	}

	/// Returns a `TypeError` that indicates that the given expression has too few child expressions.
	/// 
	/// # Note
	/// 
	/// This mainly happens only for n-ary expressions that for example are created with too few
	/// child expressions or got removed too many child expressions due to bugs in the program's behaviour.
	pub fn too_few_children<E>(expected_min: usize, actual_num: usize, expr: E) -> TypeError
		where E: Into<AnyExpr>
	{
		// TODO 2018-03-26: debug assert `expr` for too few children (may panic)
		TypeError::new(TypeErrorKind::TooFewChildren{ expected_min, actual_num, expr: expr.into() })
	}
}

impl fmt::Display for TypeError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::TypeErrorKind::*;
		match &self.kind {
			ExpectedBoolType{expr} => {
				write!(f, "Expected a boolean type expression but \
				           found non-boolean type (= {:?}) expression (= {:?}) instead.",
				       expr.ty(), expr)
			}
			ExpectedBitvecType{expr} => {
				write!(f, "Expected a bitvector type expression but \
				           found non-bitvector type (= {:?}) expression (= {:?}) instead.",
				       expr.ty(), expr)
			}
			ExpectedConcreteBitvecType{concrete, expr} => {
				write!(f, "Expected concrete bitvector type (= {:?}) expression but \
				           found unequal type (= {:?}) expression (= {:?}) instead.",
				       concrete, expr.ty(), expr)
			}
			ExpectedArrayType{expr} => {
				write!(f, "Expected a array type expression but \
				           found non-array type (= {:?}) expression (= {:?}) instead.",
				       expr.ty(), expr)
			}
			ExpectedConcreteArrayType{concrete, expr} => {
				write!(f, "Expected concrete array type (= {:?}) expression but \
				           found unequal type (= {:?}) expression (= {:?}) instead.",
				       concrete, expr.ty(), expr)
			}
			ExpectedCommonType{lhs, rhs} => {
				write!(f, "Expected both expressions to be of the same type but \
				           found unequal lhs type (= {:?}) and rhs type (= {:?}) \
						   of lhs (= {:?}) and rhs (= {:?}) expressions.",
				       lhs.ty(), rhs.ty(), lhs, rhs)
			}
			TooFewChildren{expected_min, actual_num, expr} => {
				write!(f, "Expected expression to have a minimum of {} child expression but \
				           found {} child expressions for expression (= {:?}) instead.",
				       expected_min, actual_num, expr)
			}
		}
	}
}

impl error::Error for TypeError {
	fn description(&self) -> &str {
		use self::TypeErrorKind::*;
		match self.kind {
			ExpectedBoolType{..} => {
				"Expected a boolean type expression"
			}
			ExpectedBitvecType{..} => {
				"Expected a bitvector type expression"
			}
			ExpectedConcreteBitvecType{..} => {
				"Expected a concrete bitvector type expression"
			}
			ExpectedArrayType{..} => {
				"Expected an array type expression"
			}
			ExpectedConcreteArrayType{..} => {
				"Expected a concrete array type expression"
			}
			ExpectedCommonType{..} => {
				"Expected both expressions to be of the same type"
			}
			TooFewChildren{..} => {
				"Encountered expression with too few child expressions"
			}
		}
	}
}
