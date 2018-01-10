mod concat;
mod extract;
mod sext;
mod zext;

pub mod prelude {
    pub use super::{
        Concat,
        Extract,
        SignExtend,
        ZeroExtend
    };
}

pub use self::concat::prelude::*;
pub use self::extract::prelude::*;
pub use self::sext::prelude::*;
pub use self::zext::prelude::*;
