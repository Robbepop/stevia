mod sge;
mod sgt;
mod sle;
mod slt;
mod uge;
mod ugt;
mod ule;
mod ult;

pub mod prelude {
    pub use super::{
        SignedGreaterEquals,
        SignedGreaterThan,
        SignedLessEquals,
        SignedLessThan,
        UnsignedGreaterEquals,
        UnsignedGreaterThan,
        UnsignedLessEquals,
        UnsignedLessThan
    };
}

pub use self::sge::prelude::*;
pub use self::sgt::prelude::*;
pub use self::sle::prelude::*;
pub use self::slt::prelude::*;
pub use self::uge::prelude::*;
pub use self::ugt::prelude::*;
pub use self::ule::prelude::*;
pub use self::ult::prelude::*;
