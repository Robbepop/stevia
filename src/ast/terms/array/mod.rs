mod read;
mod write;

pub mod prelude {
    pub use super::{
        ArrayRead,
        ArrayReadChildren,
        ArrayWrite,
    };
}

pub use self::read::prelude::*;
pub use self::write::prelude::*;
