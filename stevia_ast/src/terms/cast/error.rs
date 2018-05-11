use crate::prelude::*;

use std::result;
use std::error;
use std::fmt;

/// Module for exports of commonly used items of this module.
pub mod prelude {
    pub use super::{
        CastError,
        CastErrorKind,
        CastResult
    };
}

/// A special `Result` type where the error part is always a `CastError`.
pub type CastResult<T> = result::Result<T, CastError>;

/// The concrete type of a `CastError`.
///
/// This also stores some additional helpful information about the specific error.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CastErrorKind {
    /// Error upon encountering lo-bits greater-than or equal-to hi-bits of extraction.
	ExtractLoGreaterEqualHi {
		/// The lo-bits that are greater-than or equal-to the hi-bits.
		lo: usize,
		/// The hi-bits that are accidentally less-than the lo-bits.
		hi: usize,
		/// The extract expression with invalid invariants.
		expr: expr::Extract,
	},
	/// Error upon encountering overflowing hi-bits.
	ExtractHiOverflow {
		/// The hi-bits that are greater-than the expressions bitwidth.
		hi: usize,
		/// The extract expression with invalid invariants.
		expr: expr::Extract,
	},
	/// Error upon encountering target bitvector type with invalid bitwidth for extend expression.
	ExtendToSmaller {
		/// The target bitvector type that invalidly has a smaller bitwidth than the
		/// source bitwidth of the given extend expression.
		target_ty: BitvecTy,
		/// The source bitvector type.
		source_ty: BitvecTy,
		/// The extend expression with invalid invariants.
		expr: AnyExtendExpr,
	}
}

/// An error that may be returned by expression checking procedures.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CastError {
	// The kind of this error.
	pub kind: CastErrorKind,
	/// The optional context of this error.
	///
	/// # Note
	///
	/// Used for additional information about the error.
	pub context: Option<String>,
}

impl CastError {
	pub fn context<C>(self, context: C) -> Self
	where
		C: Into<String>,
	{
		let mut this = self;
		this.context = Some(context.into());
		this
	}

	/// Creates a new `CastError` from the given `CastErrorKind`.
	fn new(kind: CastErrorKind) -> Self {
		CastError {
			kind,
			context: None,
		}
	}

	/// Returns an `CastError` that indicates that the `lo` part of an extract expression
	/// was incorrectly greater-than or equal-to the `hi` part.
	pub fn extract_lo_greater_equal_hi(extract: expr::Extract) -> Self {
		CastError::new(CastErrorKind::ExtractLoGreaterEqualHi {
			lo: extract.lo,
			hi: extract.hi,
			expr: extract,
		})
	}

	/// Returns an `CastError` that indicates that the `hi` part of an extract expression
	/// was incorrectly overflowing the bitwidth of the extract expression's child expression.
	pub fn extract_hi_overflow(extract: expr::Extract) -> Self {
		CastError::new(CastErrorKind::ExtractHiOverflow {
			hi: extract.hi,
			expr: extract,
		})
	}

	/// Returns an `CastError` that indicates that the target bitvector type has a bitwidth
	/// less-than the bitwidth of the child expression of the extend expression.
	pub fn extend_to_smaller<E>(source_ty: BitvecTy, extend_expr: E) -> Self
	where
		E: Into<AnyExtendExpr>
	{
		let extend_expr = extend_expr.into();
		CastError::new(CastErrorKind::ExtendToSmaller {
			target_ty: extend_expr.bitvec_ty(),
			source_ty,
			expr: extend_expr
		})
	}
}

impl fmt::Display for CastError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::CastErrorKind::*;
		match &self.kind {
			ExtractLoGreaterEqualHi { lo, hi, expr } => write!(
				f,
				"Encountered lo-bits (= {:?}) less-than or equal to hi-bits (= {:?}) in extract expression: {:?}",
				hi, lo, expr
			),
			ExtractHiOverflow { hi, expr } => write!(
				f,
				"Encountered bitwidth (= {:?}) overflowing hi-bits (= {:?}) in extract expression: {:?}",
				expr.bitvec_ty(), hi, expr
			),
			ExtendToSmaller { target_ty, source_ty, expr } => write!(
				f,
				"Encountered target bitwidth (= {:?}) that is smaller than the current bitwidth (= {:?}) of {:?} expression: {:?}",
				target_ty.width(), source_ty.width(), expr.kind().camel_name(), expr
			),
		}
	}
}

impl error::Error for CastError {
	fn description(&self) -> &str {
		use self::CastErrorKind::*;
		match &self.kind {
			ExtractLoGreaterEqualHi { .. } => {
				"Encountered extract expression with lo-bits less-than or equal to hi-bits"
			}
			ExtractHiOverflow { .. } => {
				"Encountered extract expression with bitwidth overflowing hi-bits"
			}
			ExtendToSmaller { .. } => {
				"Encountered extend expression with a target bitwidth that is smaller than the current bitwidth"
			}
		}
	}
}
