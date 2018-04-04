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
		}
	}
}

impl error::Error for ExprError {
	fn description(&self) -> &str {
		use self::ExprErrorKind::*;
		match &self.kind {
			TypeError(type_error) => type_error.description(),
			TooFewChildren { .. } => "Too few children for expression",
			UnmatchingSymbolTypes { .. } => "Unmatching types for the same symbol"
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
