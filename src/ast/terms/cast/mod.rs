mod concat;
mod extract;
mod extend;

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
pub use self::extend::prelude::*;
