use apint::BitWidth;

/// Module for exports of commonly used items of this module.
pub mod prelude {
	pub use super::{
		HasType,
		Type,
		have_common_ty,
		common_ty
	};
}

/// All types that have a `Type` or represent a `Type` should
/// implement this trait.
pub trait HasType {
    /// Returns the `Type` of `self`.
    fn ty(&self) -> Type;
}

/// A type of an expression.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Type {
	/// Boolean type.
	Bool,
	/// Bitvector type with the given bit-width.
	BitVec(BitWidth),
	/// Array type with the given index-width and value-width.
	Array(ArrayTy)
}

impl Type {
	/// Returns a `Bool` type.
	#[inline]
	pub fn bool() -> Type {
		Type::Bool
	}

	/// Returns a `BitVec` type with the given bit width.
	#[inline]
	pub fn bitvec(width: BitWidth) -> Type {
		Type::BitVec(width)
	}

	/// Returns an `Array` type with the given index bit width and
	/// value bit width.
	#[inline]
	pub fn array(index_width: BitWidth, value_width: BitWidth) -> Type {
		Type::Array(ArrayTy{index_width, value_width})
	}
}

impl HasType for Type {
	/// Returns `self`.
	fn ty(&self) -> Type {
		*self
	}
}

/// The `Array` type.
/// 
/// Arrays have an associated bit width for their index type and
/// a bit width for their associated value type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ArrayTy {
		/// The bit width of the index type.
	index_width: BitWidth,
		/// The bit width of the value type.
	value_width: BitWidth
}

impl HasType for ArrayTy {
	/// Returns a `Type` that represents `self`.
	fn ty(&self) -> Type {
		Type::Array(*self)
	}
}

/// Returns `true` if the `Type`s of `lhs` and `rhs` are equal.
/// 
/// # Note
/// 
/// - `BitVec` types are equal if their `BitWidth`s are equal.
/// - `Array` types are equal if their index-width and value-width are equal.
pub fn have_common_ty<T1, T2>(lhs: &T1, rhs: &T2) -> bool
	where T1: HasType,
	      T2: HasType
{
	common_ty(lhs, rhs).is_some()
}

/// Returns the common type of the given `lhs` and `rhs` typed instances
/// if it exists.
/// 
/// # Note
/// 
/// - `BitVec` types are equal if their `BitWidth`s are equal.
/// - `Array` types are equal if their index-width and value-width are equal.
pub fn common_ty<T1, T2>(lhs: &T1, rhs: &T2) -> Option<Type>
	where T1: HasType,
	      T2: HasType
{
	use self::Type::*;
    match (lhs.ty(), rhs.ty()) {
		(Bool, Bool) => {
			return Some(Bool)
		}
		(BitVec(w1), BitVec(w2)) => if w1 == w2 {
			return Some(BitVec(w1))
		}
		(Array(a1), Array(a2)) => if a1 == a2 {
			return Some(Array(a1))
		}
		_ => ()
	}
	return None
}
