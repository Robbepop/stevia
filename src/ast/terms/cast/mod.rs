mod concat;
mod extract;
mod extend;
mod error;

pub mod prelude {
    pub use super::{
        Concat,
        Extract,
        SignExtend,
        ZeroExtend,
        CastError,
        CastErrorKind,
        CastResult,
    };
}

pub use self::concat::prelude::*;
pub use self::extract::prelude::*;
pub use self::extend::prelude::*;
pub use self::error::prelude::*;
