mod concat;
mod extract;
mod ext;

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
pub use self::ext::prelude::*;
