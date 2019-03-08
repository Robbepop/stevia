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

impl BitWidth {
	/// Returns a `BitWidth` with a bit width of 1 bit.
	pub fn w1() -> BitWidth {
		BitWidth(apint::BitWidth::w1())
	}
	/// Returns a `BitWidth` with a bit width of 8 bit.
	pub fn w8() -> BitWidth {
		BitWidth(apint::BitWidth::w8())
	}

	/// Returns a `BitWidth` with a bit width of 16 bit.
	pub fn w16() -> BitWidth {
		BitWidth(apint::BitWidth::w16())
	}

	/// Returns a `BitWidth` with a bit width of 32 bit.
	pub fn w32() -> BitWidth {
		BitWidth(apint::BitWidth::w32())
	}

	/// Returns a `BitWidth` with a bit width of 64 bit.
	pub fn w64() -> BitWidth {
		BitWidth(apint::BitWidth::w64())
	}

    /// Returns the raw `ApInt` bitwidth of this bit width.
    pub fn raw_width(self) -> apint::BitWidth {
        self.0
    }
}

impl From<usize> for BitWidth {
    /// Converts the `usize` to a `BitWidth`.
    /// 
    /// # Panics
    /// 
    /// - If the given value is equal to 0.
    fn from(val: usize) -> BitWidth {
        BitWidth(apint::BitWidth::from(val))
    }
}

impl From<apint::BitWidth> for BitWidth {
    /// Converts the `BitWidth` from `apint` crate to the local `BitWidth`.
    fn from(width: apint::BitWidth) -> BitWidth {
        BitWidth(width)
    }
}

impl BitWidth {
    /// Returns the number of bits representing `self`.
    #[inline]
    pub fn len_bits(self) -> usize {
        self.0.to_usize()
    }
}
