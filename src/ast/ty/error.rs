use ast::prelude::*;

use std::error;
use std::fmt;
use std::result;

/// A special `Result` type where the error part is always a `TypeError`.
pub type TypeResult<T, H> = result::Result<T, TypeError<H>>;

/// A special `Result` type where the error part is always a type error.
pub type TypeResult2<T> = result::Result<T, TypeError2>;

/// The kind of a type error.
///
/// This also stores some additional information about the concrete error.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeErrorKind2 {
	/// Error upon encountering an unexpected kind of type.
	UnexpectedTypeKind {
		expected_kind: TypeKind,
		found_ty: Type,
	},
	/// Error upon encountering an unexpected type.
	UnexpectedType { expected_ty: Type, found_ty: Type },
	/// Error upon encountering an unexpected type mismatch.
	TypeMismatch { lhs: Type, rhs: Type },
}

/// An error that may be returned by type checking procedures.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeError2 {
	/// The kind of this type error.
	pub kind: TypeErrorKind2,
}

impl TypeError2 {
	/// Creates a new `TypeError` from the given `TypeErrorKind`.
	fn new(kind: TypeErrorKind2) -> Self {
		Self { kind }
	}

	/// Returns a `TypeError` that indicates an unexpected type kind for the given expression.
	pub fn unexpected_type_kind<T>(expected_kind: TypeKind, found_ty: T) -> Self
	where
		T: HasType,
	{
		debug_assert!(expected_kind != found_ty.ty().kind(),
			"`TypeError::unexpected_type_kind` constructor was called with invalid arguments.");
		Self::new(TypeErrorKind2::UnexpectedTypeKind {
			expected_kind,
			found_ty: found_ty.ty(),
		})
	}

	/// Returns a `TypeError` that indicates an unexpected type for the given expression.
	pub fn unexpected_type<T1, T2>(expected_ty: T1, found_ty: T2) -> Self
	where
		T1: HasType,
		T2: HasType
	{
		debug_assert!(expected_ty.ty() != found_ty.ty(),
			"`TypeError::unexpected_type` constructor was called with invalid arguments.");
		Self::new(TypeErrorKind2::UnexpectedType {
			expected_ty: expected_ty.ty(),
			found_ty: found_ty.ty()
		})
	}

	/// Returns a `TypeError` that indicates an unexpected type mismatch between
	/// the given `lhs` and `rhs` expressions.
	pub fn type_mismatch<T1, T2>(lhs: T1, rhs: T2) -> Self
	where
		T1: HasType,
		T2: HasType
	{
		debug_assert!(rhs.ty() != lhs.ty(),
			"`TypeError::type_mismatch` constructor was called with invalid arguments.");
		Self::new(TypeErrorKind2::TypeMismatch { lhs: lhs.ty(), rhs: rhs.ty() })
	}
}

impl fmt::Display for TypeError2 {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::TypeErrorKind2::*;
		match &self.kind {
			UnexpectedTypeKind { expected_kind, found_ty } => write!(
				f,
				"Encountered (= {:?}) type of (= {:?}) kind while expecting {:?} type kind.",
				found_ty,
				found_ty.kind(),
				expected_kind,
			),
			UnexpectedType { expected_ty, found_ty } => write!(
				f,
				"Encountered {:?} type while expecting {:?} type.",
				found_ty,
				expected_ty
			),
			TypeMismatch { lhs, rhs } => write!(
				f,
				"Encountered unexpected type mismatch between right hand-side (= {:?}) \
				 and left hand-side (= {:?}).",
				lhs.ty(),
				rhs.ty()
			),
		}
	}
}

impl error::Error for TypeError2 {
	fn description(&self) -> &str {
		use self::TypeErrorKind2::*;
		match self.kind {
			UnexpectedTypeKind { .. } => "Unexpected type kind for expression",
			UnexpectedType { .. } => "Unexpected type for expression",
			TypeMismatch { .. } => "Unexpected type mismatch for expressions",
		}
	}
}

/// The concrete type of a `TypeError`.
///
/// This also stores some additional helpful information about the specific error.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeErrorKind<T>
where
	T: HasType + fmt::Debug,
{
	/// Error upon iterator yielding no element for n-ary type checking.
	UnexpectedEmptyIter,
	/// Error upon encountering an unexpected type kind of an expression.
	UnexpectedTypeKind {
		/// The expected type kind.
		kind: TypeKind,
		/// The expression with the unexpected type kind.
		expr: T,
	},
	/// Error upon encountering an unexpected type of an expression.
	UnexpectedType {
		/// The expected type.
		ty: Type,
		/// The expression with the unexpected type.
		expr: T,
	},
	/// Error upon encountering two expressions with different types when the same type was expected.
	TypeMismatch {
		/// The left hand-side expression with an unequal type to the right hand-side expression.
		lhs: T,
		/// The right hand-side expression with an unequal type to the left hand-side expression.
		rhs: T,
	},
}

/// An error that may be returned by type checking procedures.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeError<T>
where
	T: HasType + fmt::Debug,
{
	// The concrete type of this error.
	pub kind: TypeErrorKind<T>,
	// Optional context for this error.
	pub context: Option<String>,
}

impl<T> TypeError<T>
where
	T: HasType + fmt::Debug,
{
	/// Adds a context string for additional information about the error.
	pub fn context<S>(self, context: S) -> Self
	where
		S: Into<String>,
	{
		let mut this = self;
		this.context = Some(context.into());
		this
	}

	/// Creates a new `TypeError` from the given `TypeErrorKind`.
	fn new(kind: TypeErrorKind<T>) -> Self {
		TypeError {
			kind,
			context: None,
		}
	}

	pub fn unexpected_empty_iter() -> Self {
		TypeError::new(TypeErrorKind::UnexpectedEmptyIter)
	}

	/// Returns a `TypeError` that indicates an unexpected type kind for the given expression.
	pub fn unexpected_type_kind(kind: TypeKind, typed: T) -> Self {
		TypeError::new(TypeErrorKind::UnexpectedTypeKind { kind, expr: typed })
	}

	/// Returns a `TypeError` that indicates an unexpected type for the given expression.
	pub fn unexpected_type<H>(ty: H, typed: T) -> Self
	where
		H: Into<Type>,
	{
		TypeError::new(TypeErrorKind::UnexpectedType {
			ty: ty.into(),
			expr: typed,
		})
	}

	/// Returns a `TypeError` that indicates an unexpected type mismatch between the given `lhs` and `rhs` expressions.
	pub fn type_mismatch(lhs: T, rhs: T) -> Self {
		// TODO 2018-03-26: debug assert `lhs` and `rhs` for common type (may panic)
		TypeError::new(TypeErrorKind::TypeMismatch { lhs, rhs })
	}
}

impl<T> fmt::Display for TypeError<T>
where
	T: HasType + fmt::Debug,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::TypeErrorKind::*;
		match &self.kind {
			UnexpectedEmptyIter => write!(
				f,
				"Unexpected empty iterator for n-ary type checking procedure. Context: {:?}",
				self.context
			),
			UnexpectedTypeKind { kind, expr } => write!(
				f,
				"Unexpected type kind (= {:?}) for expression (= {:?}), expected type kind: {:?} Context: {:?}",
				expr.ty().kind(),
				expr,
				kind,
				self.context
			),
			UnexpectedType { ty, expr } => write!(
				f,
				"Unexpected type (= {:?}) for expression (= {:?}), expected type: {:?} Context: {:?}",
				expr.ty(),
				expr,
				ty,
				self.context
			),
			TypeMismatch { lhs, rhs } => write!(
				f,
				"Unexpected type mismatch of left expression (= {:?}) of type (= {:?}) \
				 and right expression (= {:?}) of type (= {:?}). Context: {:?}",
				lhs,
				lhs.ty(),
				rhs,
				rhs.ty(),
				self.context
			),
		}
	}
}

impl<T> error::Error for TypeError<T>
where
	T: HasType + fmt::Debug,
{
	fn description(&self) -> &str {
		use self::TypeErrorKind::*;
		match self.kind {
			UnexpectedEmptyIter => "Unexpected empty iterator",
			UnexpectedTypeKind { .. } => "Unexpected type kind for expression",
			UnexpectedType { .. } => "Unexpected type for expression",
			TypeMismatch { .. } => "Unexpected type mismatch for expressions",
		}
	}
}
