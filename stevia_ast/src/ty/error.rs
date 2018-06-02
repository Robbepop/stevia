use crate::prelude::*;

use std::error;
use std::fmt;
use std::result;

/// A special `Result` type where the error part is always a type error.
pub type TypeResult<T> = result::Result<T, TypeError>;

/// The kind of a type error.
///
/// This also stores some additional information about the concrete error.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeErrorKind {
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
pub struct TypeError {
	/// The kind of this type error.
	pub kind: TypeErrorKind,
}

impl TypeError {
	/// Creates a new `TypeError` from the given `TypeErrorKind`.
	fn new(kind: TypeErrorKind) -> Self {
		Self { kind }
	}

	/// Returns a `TypeError` that indicates an unexpected type kind for the given expression.
	pub fn unexpected_type_kind<T>(expected_kind: TypeKind, found_ty: T) -> Self
	where
		T: HasType,
	{
		debug_assert!(expected_kind != found_ty.ty().kind(),
			"`TypeError::unexpected_type_kind` constructor was called with invalid arguments.");
		Self::new(TypeErrorKind::UnexpectedTypeKind {
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
		Self::new(TypeErrorKind::UnexpectedType {
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
		Self::new(TypeErrorKind::TypeMismatch { lhs: lhs.ty(), rhs: rhs.ty() })
	}
}

impl fmt::Display for TypeError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::TypeErrorKind::*;
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

impl error::Error for TypeError {
	fn description(&self) -> &str {
		use self::TypeErrorKind::*;
		match self.kind {
			UnexpectedTypeKind { .. } => "Unexpected type kind for expression",
			UnexpectedType { .. } => "Unexpected type for expression",
			TypeMismatch { .. } => "Unexpected type mismatch for expressions",
		}
	}
}
