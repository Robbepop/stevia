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
		have_common_ty,
		common_ty,
        TypeError,
		TypeErrorKind
    };
}

pub use self::base::prelude::*;
pub use self::assert::prelude::*;
pub use self::error::prelude::*;
// pub use self::type_check::prelude::*;
