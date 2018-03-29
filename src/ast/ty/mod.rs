mod base;
mod assert;
mod error;
// mod type_check;

pub mod prelude {
    pub use super::{
		ArrayTy,
		BitvecTy,
		HasType,
		Type,
		TypeKind,
		TypeError,
		TypeErrorKind,
		TypeResult,
		have_common_ty,
		common_ty,
		expect_common_ty,
		expect_array_ty,
		expect_bitvec_ty,
		expect_concrete_bitvec_ty,
		expect_common_bitvec_ty,
		expect_common_bitvec_ty_n
    };
}

pub use self::base::prelude::*;
pub use self::assert::prelude::*;
pub use self::error::prelude::*;
// pub use self::type_check::prelude::*;
