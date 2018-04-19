use ast::prelude::*;

use std::error;
use std::fmt;
use std::result;

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
	/// Errors that are caused by cast violations.
	CastError(CastError),
	/// Errors that are caused by type violations.
	TypeError(TypeError<AnyExpr>),
	/// Errors that are caused by bitvector operations.
	BitvecError(BitvecError),
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
		symbol: NamedSymbolId,
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

impl From<CastError> for ExprError {
	fn from(cast_error: CastError) -> Self {
		ExprError::new(ExprErrorKind::CastError(cast_error))
	}
}

impl From<TypeError<AnyExpr>> for ExprError {
	fn from(type_error: TypeError<AnyExpr>) -> Self {
		ExprError::new(ExprErrorKind::TypeError(type_error))
	}
}

impl From<BitvecError> for ExprError {
	fn from(bitvec_error: BitvecError) -> Self {
		ExprError::new(ExprErrorKind::BitvecError(bitvec_error))
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
			expr,
		})
	}

	/// Returns an `ExprError` that indicates that two mismatching types were to be associated to the same symbol.
	pub fn unmatching_symbol_types<T1, T2>(
		assoc_ty: T1,
		current_ty: T2,
		symbol_id: NamedSymbolId,
	) -> Self
	where
		T1: Into<Type>,
		T2: Into<Type>,
	{
		let assoc_ty = assoc_ty.into();
		let current_ty = current_ty.into();
		debug_assert_ne!(assoc_ty, current_ty);
		ExprError::new(ExprErrorKind::UnmatchingSymbolTypes {
			assoc_ty,
			current_ty,
			symbol: symbol_id,
		})
	}
}

impl fmt::Display for ExprError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::ExprErrorKind::*;
		match &self.kind {
			CastError(cast_error) => cast_error.fmt(f),
			TypeError(type_error) => type_error.fmt(f),
			BitvecError(bitvec_error) => bitvec_error.fmt(f),
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
			CastError(cast_error) => cast_error.description(),
			TypeError(type_error) => type_error.description(),
			BitvecError(bitvec_error) => bitvec_error.description(),
			TooFewChildren { .. } => "Too few children for expression",
			UnmatchingSymbolTypes { .. } => "Unmatching types for the same symbol",
		}
	}
}

/// Asserts that the given expression is of the expected concrete type.
pub fn expect_concrete_ty<T, E>(expected_ty: T, expr: &E) -> ExprResult<()>
where
	T: Into<Type>,
	E: Into<AnyExpr> + Clone + HasType + fmt::Debug,
{
	let expected_ty = expected_ty.into();
	let actual_ty = expr.ty();
	if actual_ty != expected_ty {
		return Err(
			TypeError::unexpected_type(expected_ty, expr.clone().into()).context(format!(
				"Expected concrete type (= {:?}) for the expression: {:?}",
				expected_ty, expr
			)),
		).map_err(ExprError::from);
	}
	Ok(())
}

/// Asserts that all child expressions of the given expression are of the
/// given expected concrete type.
pub fn expect_concrete_ty_n<T, E>(expected_ty: T, expr: &E) -> ExprResult<()>
where
	T: Into<Type>,
	E: Into<AnyExpr> + Clone + Children + HasKind + fmt::Debug,
{
	let expected_ty = expected_ty.into();
	for (n, child) in expr.children().enumerate() {
		expect_concrete_ty(expected_ty, child).map_err(|e| {
			e.context(format!(
				"Expected concrete type (= {:?}) for the child expression at index {:?} of expression: {:?}.",
				expected_ty,
				n,
				expr.kind().camel_name()
			))
		})?;
	}
	Ok(())
}

/// Asserts that the given expression has at least the expected minimum number of child expressions.
pub fn expect_min_children<E>(expected_min_children_number: usize, expr: &E) -> ExprResult<()>
where
	E: Into<AnyExpr> + Clone + HasArity + HasKind,
{
	let actual_children_number = expr.arity();
	if actual_children_number < expected_min_children_number {
		return Err(ExprError::too_few_children(
			expected_min_children_number,
			actual_children_number,
			expr.clone(),
		).context(format!(
			"Expected at least 2 child expressions for the {} expression.",
			expr.kind().camel_name()
		)));
	}
	Ok(())
}

/// Asserts that the given named symbol ID has the same type as its context associated type.
pub fn expect_matching_symbol_type<T1, T2>(
	assoc_ty: T1,
	current_ty: T2,
	symbol_id: NamedSymbolId,
) -> ExprResult<()>
where
	T1: Into<Type>,
	T2: Into<Type>,
{
	let assoc_ty = assoc_ty.into();
	let current_ty = current_ty.into();
	if assoc_ty != current_ty {
		return Err(ExprError::unmatching_symbol_types(
			assoc_ty, current_ty, symbol_id,
		));
	}
	Ok(())
}
