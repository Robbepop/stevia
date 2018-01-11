mod equals;
mod read;
mod write;

pub mod prelude {
    pub use super::{
        ArrayEquals,
        ArrayRead,
        ArrayWrite,
    };
}

pub use self::read::prelude::*;
pub use self::write::prelude::*;
pub use self::equals::prelude::*;
