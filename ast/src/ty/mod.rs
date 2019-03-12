//! Types and utilities arround types.

mod base;
mod assert;
mod error;

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
		TypeResult
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
