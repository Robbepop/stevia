use ast::prelude::*;

use std::result;
use std::error;
use std::fmt;

/// Module for exports of commonly used items of this module.
pub mod prelude {
	pub use super::{expect_matching_symbol_type, ExprError, ExprErrorKind, ExprResult};
}

/// A special `Result` type where the error part is always a `ExprError`.
pub type ExprResult<T> = result::Result<T, ExprError>;

/// The concrete type of a `ExprError`.
///
/// This also stores some additional helpful information about the specific error.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprErrorKind {
	/// Errors that are caused by type violations.
	TypeError(TypeError<AnyExpr>),
	/// Error upon encountering an n-ary expression that was provided with too few child expressions.
	TooFewChildren {
		/// The minimum number of expected child expressions.
		expected_min: usize,
		/// The actual number of given child expressions.
		actual_num: usize,
		/// The expression that has too few child expressions.
		expr: AnyExpr,
	},
	/// Error upon encountering type mismatch for the same symbol.
	UnmatchingSymbolTypes {
		/// The former associated type of the symbol.
		assoc_ty: Type,
		/// The to-be-associated type of the symbol.
		current_ty: Type,
		/// The symbol of the type mismatch.
		symbol: SymbolName,
	},
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
	/// Error upon encountering target bitvector type with invalid bitwidth for extend sign-expression.
	SignExtendToSmaller {
		/// The target bitvector type that invalidly has a smaller bitwidth than the
		/// source bitwidth of the given sign-extend expression.
		target_ty: BitvecTy,
		/// The source bitvector type.
		source_ty: BitvecTy,
		/// The sign-extend expression with invalid invariants.
		expr: expr::SignExtend,
	},
	/// Error upon encountering target bitvector type with invalid bitwidth for extend zero-expression.
	ZeroExtendToSmaller {
		/// The target bitvector type that invalidly has a smaller bitwidth than the
		/// source bitwidth of the given zero-extend expression.
		target_ty: BitvecTy,
		/// The source bitvector type.
		source_ty: BitvecTy,
		/// The zero-extend expression with invalid invariants.
		expr: expr::ZeroExtend,
	},
}

/// An error that may be returned by expression checking procedures.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExprError {
	// The kind of this error.
	pub kind: ExprErrorKind,
	/// The optional context of this error.
	///
	/// # Note
	///
	/// Used for additional information about the error.
	pub context: Option<String>,
}

impl From<TypeError<AnyExpr>> for ExprError {
	fn from(type_error: TypeError<AnyExpr>) -> Self {
		ExprError::new(ExprErrorKind::TypeError(type_error))
	}
}

impl ExprError {
	pub fn context<C>(self, context: C) -> Self
	where
		C: Into<String>,
	{
		let mut this = self;
		this.context = Some(context.into());
		this
	}

	/// Creates a new `ExprError` from the given `ExprErrorKind`.
	fn new(kind: ExprErrorKind) -> Self {
		ExprError {
			kind,
			context: None,
		}
	}

	/// Returns an `ExprError` that indicates that the given expression has too few child expressions.
	pub fn too_few_children<E>(expected_min: usize, actual_num: usize, expr: E) -> Self
	where
		E: Into<AnyExpr>,
	{
		let expr = expr.into();
		debug_assert!(expr.arity() < expected_min);
		debug_assert!(expr.arity() == actual_num);
		ExprError::new(ExprErrorKind::TooFewChildren {
			expected_min,
			actual_num,
			expr: expr,
		})
	}

	/// Returns an `ExprError` that indicates that two mismatching types were to be associated to the same symbol.
	pub fn unmatching_symbol_types<T1, T2, S>(assoc_ty: T1, current_ty: T2, symbol: S) -> Self
	where
		T1: Into<Type>,
		T2: Into<Type>,
		S: Into<SymbolName>,
	{
		let assoc_ty = assoc_ty.into();
		let current_ty = current_ty.into();
		debug_assert_ne!(assoc_ty, current_ty);
		ExprError::new(ExprErrorKind::UnmatchingSymbolTypes {
			assoc_ty: assoc_ty,
			current_ty: current_ty,
			symbol: symbol.into(),
		})
	}

	/// Returns an `ExprError` that indicates that the `lo` part of an extract expression
	/// was incorrectly greater-than or equal-to the `hi` part.
	pub fn extract_lo_greater_equal_hi(extract: expr::Extract) -> Self {
		ExprError::new(ExprErrorKind::ExtractLoGreaterEqualHi {
			lo: extract.lo,
			hi: extract.hi,
			expr: extract,
		})
	}

	/// Returns an `ExprError` that indicates that the `hi` part of an extract expression
	/// was incorrectly overflowing the bitwidth of the extract expression's child expression.
	pub fn extract_hi_overflow(extract: expr::Extract) -> Self {
		ExprError::new(ExprErrorKind::ExtractHiOverflow {
			hi: extract.hi,
			expr: extract,
		})
	}

	/// Returns an `ExprError` that indicates that the target bitvector type has a bitwidth
	/// less-than the bitwidth of the child expression of the sign-extend expression.
	pub fn sign_extend_to_smaller(source_ty: BitvecTy, extend: expr::SignExtend) -> Self {
		ExprError::new(ExprErrorKind::SignExtendToSmaller {
			target_ty: extend.bitvec_ty,
			source_ty: source_ty,
			expr: extend
		})
	}

	/// Returns an `ExprError` that indicates that the target bitvector type has a bitwidth
	/// less-than the bitwidth of the child expression of the zero-extend expression.
	pub fn zero_extend_to_smaller(source_ty: BitvecTy, extend: expr::ZeroExtend) -> Self {
		ExprError::new(ExprErrorKind::ZeroExtendToSmaller {
			target_ty: extend.bitvec_ty,
			source_ty: source_ty,
			expr: extend
		})
	}
}

impl fmt::Display for ExprError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::ExprErrorKind::*;
		match &self.kind {
			TypeError(type_error) => write!(f, "{}", type_error),
			TooFewChildren {
				expected_min,
				actual_num,
				expr,
			} => write!(
				f,
				"Too few children for expression (= {:?}), found {:?} children but \
				 expected at least {:?}.",
				expr, actual_num, expected_min
			),
			UnmatchingSymbolTypes {
				assoc_ty,
				current_ty,
				symbol,
			} => write!(
				f,
				"Unmatching associated type (= {:?}) and new type (= {:?}) for the same symbol (= {:?}).",
				assoc_ty, current_ty, symbol
			),
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
			SignExtendToSmaller { target_ty, source_ty, expr } => write!(
				f,
				"Encountered target bitwidth (= {:?}) that is smaller than the current bitwidth (= {:?}) of sign-extend expression: {:?}",
				target_ty.width(), source_ty.width(), expr
			),
			ZeroExtendToSmaller { target_ty, source_ty, expr } => write!(
				f,
				"Encountered target bitwidth (= {:?}) that is smaller than the current bitwidth (= {:?}) of zero-extend expression: {:?}",
				target_ty.width(), source_ty.width(), expr
			),
		}
	}
}

impl error::Error for ExprError {
	fn description(&self) -> &str {
		use self::ExprErrorKind::*;
		match &self.kind {
			TypeError(type_error) => type_error.description(),
			TooFewChildren { .. } => "Too few children for expression",
			UnmatchingSymbolTypes { .. } => "Unmatching types for the same symbol",
			ExtractLoGreaterEqualHi { .. } => {
				"Encountered extract expression with lo-bits less-than or equal to hi-bits"
			}
			ExtractHiOverflow { .. } => {
				"Encountered extract expression with bitwidth overflowing hi-bits"
			}
			SignExtendToSmaller { .. } => {
				"Encountered sign-extend expression with a target bitwidth that is smaller than the current bitwidth"
			}
			ZeroExtendToSmaller { .. } => {
				"Encountered zero-extend expression with a target bitwidth that is smaller than the current bitwidth"
			}
		}
	}
}

pub fn expect_matching_symbol_type<T1, T2, S>(
	assoc_ty: T1,
	current_ty: T2,
	symbol: S,
) -> ExprResult<()>
where
	T1: Into<Type>,
	T2: Into<Type>,
	S: Into<SymbolName>,
{
	let assoc_ty = assoc_ty.into();
	let current_ty = current_ty.into();
	if assoc_ty != current_ty {
		return Err(ExprError::unmatching_symbol_types(
			assoc_ty,
			current_ty,
			symbol.into(),
		));
	}
	Ok(())
}
