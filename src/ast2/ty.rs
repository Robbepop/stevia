use ast2::{BitWidth};
use apint;

/// Module for exports of commonly used items of this module.
pub mod prelude {
	pub use super::{
		ArrayTy,
		BitvecTy,
		HasType,
		Type,
		TypeKind,
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
	Bitvec(BitvecTy),
	/// Array type with the given index-width and value-width.
	Array(ArrayTy)
}

/// The kind of a type.
/// 
/// This unifies all bitvector types and all array types
/// without respecting their bit widths.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TypeKind {
	/// The boolean type kind.
	Bool,
	/// The bitvector type kind.
	Bitvec,
	/// The array type kind.
	Array
}

impl From<Type> for TypeKind {
	/// Converts a `Type` into its associated `TypeKind`.
	fn from(ty: Type) -> TypeKind {
		match ty {
			Type::Bool => TypeKind::Bool,
			Type::Bitvec(_) => TypeKind::Bitvec,
			Type::Array(..) => TypeKind::Array
		}
	}
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
		Type::Bitvec(BitvecTy(width))
	}

	/// Returns an `Array` type with the given index bit width and
	/// value bit width.
	#[inline]
	pub fn array(index_ty: BitvecTy, value_ty: BitvecTy) -> Type {
		Type::Array(ArrayTy{index_ty, value_ty})
	}

	/// Returns the `TypeKind` of this `Type`.
	#[inline]
	pub fn kind(self) -> TypeKind {
		self.into()
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
	/// The index bitvec type.
	index_ty: BitvecTy,
	/// The value bitvec type.
	value_ty: BitvecTy
}

impl ArrayTy {
	/// Returns the index bit width of this array type.
	pub fn index_width(self) -> BitWidth { self.index_ty.width() }
	/// Returns the value bit width of this array type.
	pub fn value_width(self) -> BitWidth { self.value_ty.width() }
	/// Returns the index bit width of this array type.
	pub fn index_ty(self) -> BitvecTy { self.index_ty }
	/// Returns the value bit width of this array type.
	pub fn value_ty(self) -> BitvecTy { self.value_ty }
}

impl HasType for ArrayTy {
	/// Returns a `Type` that represents `self`.
	fn ty(&self) -> Type {
		Type::Array(*self)
	}
}

impl From<ArrayTy> for Type {
	fn from(array_ty: ArrayTy) -> Type {
		Type::Array(array_ty)
	}
}


/// The `Bitvec` type.
/// 
/// Bitvec have an associated bit width for their respective value.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitvecTy(BitWidth);

impl BitvecTy {
	/// Returns a `BitvecTy` representing bitvector with a bit width of 1 bit.
	pub fn w1() -> BitvecTy {
		BitvecTy(BitWidth::w1())
	}
	/// Returns a `BitvecTy` representing bitvector with a bit width of 8 bit.
	pub fn w8() -> BitvecTy {
		BitvecTy(BitWidth::w8())
	}

	/// Returns a `BitvecTy` representing bitvector with a bit width of 16 bit.
	pub fn w16() -> BitvecTy {
		BitvecTy(BitWidth::w16())
	}

	/// Returns a `BitvecTy` representing bitvector with a bit width of 32 bit.
	pub fn w32() -> BitvecTy {
		BitvecTy(BitWidth::w32())
	}

	/// Returns a `BitvecTy` representing bitvector with a bit width of 64 bit.
	pub fn w64() -> BitvecTy {
		BitvecTy(BitWidth::w64())
	}
}

impl From<usize> for BitvecTy {
    /// Converts the `usize` to a `BitvecTy`.
    /// 
    /// # Panics
    /// 
    /// - If the given value is equal to 0.
    fn from(val: usize) -> BitvecTy {
        BitvecTy(BitWidth::from(val))
    }
}

impl From<BitWidth> for BitvecTy {
    /// Converts the `BitWidth` from `apint` crate to a `BitvecTy`.
    fn from(width: BitWidth) -> BitvecTy {
        BitvecTy(width)
    }
}

impl From<apint::BitWidth> for BitvecTy {
    /// Converts the `BitWidth` from `apint` crate to a `BitvecTy`.
    fn from(width: apint::BitWidth) -> BitvecTy {
        BitvecTy::from(width.to_usize())
    }
}

impl BitvecTy {
    /// Returns the bit width as `usize`.
    #[inline]
    pub fn width(self) -> BitWidth {
        self.0
    }
}

impl HasType for BitvecTy {
    /// Converts this `BitvecTy` to its associated `Type`.
    #[inline]
    fn ty(&self) -> Type {
        Type::Bitvec(*self)
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
		(Bitvec(w1), Bitvec(w2)) => if w1 == w2 {
			return Some(Bitvec(w1))
		}
		(Array(a1), Array(a2)) => if a1 == a2 {
			return Some(Array(a1))
		}
		_ => ()
	}
	None
}
