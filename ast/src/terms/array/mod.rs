mod read;
mod write;

pub mod prelude {
    pub use super::{
        ArrayRead,
        ArrayReadChildren,
        ArrayWrite,
        ArrayWriteChildren,
    };
}

pub use self::read::{
    ArrayRead,
    ArrayReadChildren,
};
pub use self::write::{
    ArrayWrite,
    ArrayWriteChildren,
};
