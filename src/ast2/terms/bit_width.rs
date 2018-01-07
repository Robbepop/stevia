use ast2::prelude::*;

use apint;

pub mod prelude {
    pub use super::{
        BitWidth
    };
}

/// Represents a bit width of term expressions.
/// 
/// This is similar and based on the `BitWidth` of the apint crate.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitWidth(apint::BitWidth);

impl From<apint::BitWidth> for BitWidth {
    /// Converts the `BitWidth` from `apint` crate to the local `BitWidth`.
    fn from(width: apint::BitWidth) -> BitWidth {
        BitWidth(width)
    }
}

impl BitWidth {
    /// Returns the `usize` representation of `self`.
    #[inline]
    pub fn to_usize(self) -> usize {
        self.0.to_usize()
    }
}

impl HasType for BitWidth {
    /// Converts this `BitWidth` to its associated `Type`.
    #[inline]
    fn ty(&self) -> Type {
        Type::Bitvec(*self)
    }
}
