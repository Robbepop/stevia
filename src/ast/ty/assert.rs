use ast::prelude::*;

/// Module for exports of commonly used items of this module.
pub mod prelude {
	pub use super::{
		have_common_ty,
		common_ty
	};
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
