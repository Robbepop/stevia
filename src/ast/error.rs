use ast::prelude::*;

use std::error;
use std::fmt;
use std::result;

/// Module for exports of commonly used items of this module.
pub mod prelude {
	pub use super::{expect_matching_symbol_type, ExprError, ExprErrorKind, ExprResult};
}

/// An error context providing metadata context error information.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorContext {
	Msg(String),
	Entity {
		description: String,
		entity: ErrorContextEntity,
	},
}

/// An error context entity providing further queryable information
/// about the associated error.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorContextEntity {
	Expr(AnyExpr),
}

impl<S> From<S> for ErrorContext
where
	S: Into<String>,
{
	fn from(message: S) -> Self {
		ErrorContext::msg(message)
	}
}

impl ErrorContext {
	/// Constructs a new message error context.
	pub fn msg<S>(message: S) -> Self
	where
		S: Into<String>,
	{
		ErrorContext::Msg(message.into())
	}

	/// Constructs a new expression entity error context with
	/// the given description and expression.
	pub fn expr<S, E>(description: S, expr: E) -> Self
	where
		S: Into<String>,
		E: Into<AnyExpr>,
	{
		ErrorContext::Entity {
			description: description.into(),
			entity: ErrorContextEntity::Expr(expr.into()),
		}
	}
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
	TypeError(TypeError),
	/// Errors that are caused by bitvector operations.
	BitvecError(BitvecError),
	/// Error upon encountering an n-ary expression that was provided with too few child expressions.
	TooFewChildren {
		/// The minimum number of expected child expressions.
		expected_min: usize,
		/// The actual number of given child expressions.
		actual_num: usize,
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
	pub context: Vec<ErrorContext>,
}

impl From<CastError> for ExprError {
	fn from(cast_error: CastError) -> Self {
		ExprError::new(ExprErrorKind::CastError(cast_error))
	}
}

impl From<TypeError> for ExprError {
	fn from(type_error: TypeError) -> Self {
		ExprError::new(ExprErrorKind::TypeError(type_error))
	}
}

impl From<BitvecError> for ExprError {
	fn from(bitvec_error: BitvecError) -> Self {
		ExprError::new(ExprErrorKind::BitvecError(bitvec_error))
	}
}

impl ExprError {
	/// Creates a new `ExprError` from the given `ExprErrorKind`.
	fn new(kind: ExprErrorKind) -> Self {
		ExprError {
			kind,
			context: vec![],
		}
	}

	/// Pushes a new stringly error context to the context stack.
	pub fn context<S>(self, context: S) -> Self
	where
		S: Into<String>,
	{
		let mut this = self;
		this.context.push(ErrorContext::msg(context));
		this
	}

	/// Pushes a new stringly error context to the context stack.
	pub fn context_msg<S>(self, message: S) -> Self
	where
		S: Into<String>,
	{
		let mut this = self;
		this.context.push(ErrorContext::msg(message));
		this
	}

	/// Pushes a new expression error context to the context stack.
	pub fn context_expr<S, E>(self, description: S, entity: E) -> Self
	where
		S: Into<String>,
		E: Into<AnyExpr>
	{
		let mut this = self;
		this.context.push(ErrorContext::expr(description, entity));
		this
	}

	/// Returns an `ExprError` that indicates that the given expression has too few child expressions.
	pub fn too_few_children(expected_min: usize, actual_num: usize) -> Self {
		debug_assert!(expected_min > actual_num);
		ExprError::new(ExprErrorKind::TooFewChildren {
			expected_min,
			actual_num,
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
			} => write!(
				f,
				"Expected at least {:?} child expressions but found only {:?}.",
				actual_num, expected_min
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
		return Err(TypeError::unexpected_type(expected_ty, expr.clone().into()))
			.map_err(ExprError::from)
			.map_err(|e| {
				e.context_msg(format!(
					"Expected concrete type (= {:?}) for the expression: {:?}",
					expected_ty, expr
				))
			})
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
		expect_concrete_ty(expected_ty, child)
			.map_err(|e| {
				e.context_msg(format!(
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
	E: HasArity,
{
	let actual_children_number = expr.arity();
	if actual_children_number < expected_min_children_number {
		return Err(ExprError::too_few_children(
			expected_min_children_number,
			actual_children_number,
		).context_msg(format!(
			"Expected at least {:?} child expressions but found only {:?}.",
			expected_min_children_number, actual_children_number
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
