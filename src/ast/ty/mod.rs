mod base;
mod assert;
mod error;

/// Module for exports of commonly used items of this module.
pub mod prelude {
    pub use super::*;
}

pub use self::{
	base::{
		Type,
		ArrayTy,
		BitvecTy,
		HasType,
		TypeKind
	},
	error::{
		TypeError,
		TypeErrorKind,
		TypeResult,
		TypeError2,
		TypeErrorKind2,
		TypeResult2
	},
	assert::{
		expect_common_ty,
		expect_array_ty,
		expect_bitvec_ty,
		expect_type,
		expect_common_bitvec_ty,
		expect_common_bitvec_ty_n
	}
};
