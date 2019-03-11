use apint::Width as RawWidth;
use crate::{
	BitvecResult,
	BitvecError,
	BitWidth,
};

/// Represents a bitvector in the sense of the SMT theory of bitvectors.
///
/// These are used to represent constant bitvector values.
/// This struct mainly wraps an underlying bitvector implementation
/// and provides an appropriate interface for SMT-like bitvectors.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Bitvec(apint::ApInt);

impl Bitvec {
    /// Creates a new `Bitvec` for the given bit width with a value of zero.
    pub fn zero(width: BitWidth) -> Bitvec {
        let val = apint::ApInt::zero(width.raw_width());
        Bitvec::from(val)
    }

    /// Creates a new `Bitvec` for the given bit width with a value of one.
    pub fn one(width: BitWidth) -> Bitvec {
        let val = apint::ApInt::one(width.raw_width());
        Bitvec::from(val)
    }

    /// Creates a new `Bitvec` for the given bit width with a value that has all bits set.
    pub fn all_set(width: BitWidth) -> Bitvec {
        let val = apint::ApInt::all_set(width.raw_width());
        Bitvec::from(val)
    }

	/// Creates a new `Bitvec` that represents the maximum unsigned value for the given bit width.
	pub fn umax(width: BitWidth) -> Bitvec {
        Bitvec::from(
			apint::ApInt::unsigned_max_value(width.raw_width())
		)
	}

	/// Creates a new `Bitvec` that represents the maximum signed value for the given bit width.
	pub fn smax(width: BitWidth) -> Bitvec {
        Bitvec::from(
			apint::ApInt::signed_max_value(width.raw_width())
		)
	}

	/// Creates a new `Bitvec` that represents the minimum unsigned value for the given bit width.
	pub fn umin(width: BitWidth) -> Bitvec {
        Bitvec::from(
			apint::ApInt::unsigned_min_value(width.raw_width())
		)
	}

	/// Creates a new `Bitvec` that represents the minimum signed value for the given bit width.
	pub fn smin(width: BitWidth) -> Bitvec {
        Bitvec::from(
			apint::ApInt::signed_min_value(width.raw_width())
		)
	}
}

impl From<apint::ApInt> for Bitvec {
    fn from(val: apint::ApInt) -> Self {
        Bitvec(val)
    }
}

macro_rules! gen_from_impls_for {
    ($($type:ty);+) => {
        $(
            impl From<$type> for Bitvec {
                fn from(val: $type) -> Self {
                    Bitvec(apint::ApInt::from(val))
                }
            }
        )+
    }
}
gen_from_impls_for!(bool; i8; u8; i16; u16; i32; u32; i64; u64; i128; u128);

impl Bitvec {
    /// Returns a shared borrow to the internal `ApInt`.
    fn raw_val(&self) -> &apint::ApInt {
        &self.0
    }

    /// Returns a mutable borrow to the internal `ApInt`.
    fn raw_val_mut(&mut self) -> &mut apint::ApInt {
        &mut self.0
    }

    /// Consumes `self` and returns internal `ApInt`.
    fn into_raw_val(self) -> apint::ApInt {
        self.0
    }

    /// Returns the number of bits representing the bit width of this bitvector.
    pub fn len_bits(&self) -> usize {
        self.width().len_bits()
    }

    /// Returns the bit width of this bitvector.
    pub fn width(&self) -> BitWidth {
        BitWidth::from(self.0.width())
    }
}

impl Bitvec {
	/// Returns `true` if `self` is even.
	pub fn is_even(&self) -> bool {
		self.raw_val().is_even()
	}

	/// Returns `true` if `self` is odd.
	pub fn is_odd(&self) -> bool {
		self.raw_val().is_odd()
	}

    /// Returns `true` if `self` is zero.
	///
	/// # Note
	///
	/// This is equal to calling `is_all_unset` or `is_umin`.
    pub fn is_zero(&self) -> bool {
        self.is_all_unset()
    }

    /// Returns `true` if `self` is one.
    pub fn is_one(&self) -> bool {
        self.raw_val().is_one()
    }

	/// Returns `true` if `self` is equal to the signed representation of minus one (`-1`).
	///
	/// # Note
	///
	/// This is equal to calling `is_all_set`.
	pub fn is_minus_one(&self) -> bool {
		self.is_all_set()
	}

	/// Returns `true` if all bits in `self` are set to `1`.
	pub fn is_all_set(&self) -> bool {
		self.raw_val().is_all_set()
	}

	/// Returns `true` if all bits in `self` are set to `0`.
	///
	/// # Note
	///
	/// This is equal to calling `is_zero` or `is_umin`.
	pub fn is_all_unset(&self) -> bool {
		self.raw_val().is_all_unset()
	}

	/// Returns `true` if `self` is equal to the unsigned maximum value.
	///
	/// # Note
	///
	/// This is equal to calling `is_all_set` or `is_minus_one`.
	pub fn is_umax(&self) -> bool {
		self.is_all_set()
	}

	/// Returns `true` if `self` is equal to the unsigned minimum value.
	///
	/// # Note
	///
	/// This is equal to calling `is_zero` or `is_all_unset`.
	pub fn is_umin(&self) -> bool {
		self.is_zero()
	}

	/// Returns `true` if `self` is equal to the signed maximum value.
	///
	/// # Internal
	///
	/// This operation could be made more efficient if it was supported by `apint`.
	pub fn is_smax(&self) -> bool {
		self.raw_val().sign_bit() == apint::Bit::Unset
			&& self.raw_val().count_ones() == self.width().len_bits() - 1
	}

	/// Returns `true` if `self` is equal to the signed minimum value.
	///
	/// # Internal
	///
	/// This operation could be made more efficient if it was supported by `apint`.
	pub fn is_smin(&self) -> bool {
		self.raw_val().sign_bit() == apint::Bit::Set
			&& self.raw_val().count_ones() == 1
	}
}

fn forward_mut_impl<T, F>(entity: T, op: F) -> T
where
    F: Fn(&mut T) -> (),
{
    let mut this = entity;
    op(&mut this);
    this
}

fn try_forward_bin_mut_impl<L, R, F>(entity: L, rhs: R, op: F) -> BitvecResult<L>
where
    F: Fn(&mut L, R) -> BitvecResult<()>,
{
    let mut this = entity;
    op(&mut this, rhs)?;
    Ok(this)
}

impl Bitvec {
    /// Returns `self` with bits flipped.
    pub fn bvnot(self) -> Self {
        forward_mut_impl(self, Bitvec::bvnot_mut)
    }

    /// Flips bits of `self` inplace.
    pub fn bvnot_mut(&mut self) {
        self.raw_val_mut().bitnot()
    }

    /// Computes the bitwise and of `self` and `rhs` and returns the result.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvand(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::bvand_mut)
    }

    /// Bit-and assigns `self` to `rhs`.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvand_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_bitand_assign(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Computes the bitwise or of `self` and `rhs` and returns the result.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvor(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::bvor_mut)
    }

    /// Bit-or assigns `self` to `rhs`.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvor_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_bitor_assign(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Computes the bitwise exclusive or (XOR) of `self` and `rhs` and returns the result.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvxor(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::bvxor_mut)
    }

    /// Bit-xor assigns `self` to `rhs`.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvxor_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_bitxor_assign(rhs.raw_val())
            .map_err(BitvecError::from)
    }
}

impl Bitvec {
    /// Computes the signed greater-equals comparison between both given bitvectors.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvsge(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val()
            .checked_sge(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Computes the signed greater-than comparison between both given bitvectors.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvsgt(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val()
            .checked_sgt(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Computes the signed less-equals comparison between both given bitvectors.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvsle(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val()
            .checked_sle(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Computes the signed less-than comparison between both given bitvectors.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvslt(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val()
            .checked_slt(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Computes the unsigned greater-equals comparison between both given bitvectors.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvuge(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val()
            .checked_uge(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Computes the unsigned greater-than comparison between both given bitvectors.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvugt(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val()
            .checked_ugt(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Computes the unsigned less-equals comparison between both given bitvectors.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvule(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val()
            .checked_ule(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Computes the unsigned less-than comparison between both given bitvectors.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvult(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val()
            .checked_ult(rhs.raw_val())
            .map_err(BitvecError::from)
    }
}

impl Bitvec {
    /// Returns negated `self`.
    pub fn bvneg(self) -> Self {
        forward_mut_impl(self, Bitvec::bvneg_mut)
    }

    /// Negates `self` inplace.
    pub fn bvneg_mut(&mut self) {
        self.raw_val_mut().negate()
    }

    /// Adds `rhs` to `self` and returns the result.
    ///
    /// # Errors
    ///
    /// If the bit width of the given bitvectors do not match.
    pub fn bvadd(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::bvadd_mut)
    }

    /// Add assigns `self` to `rhs`.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvadd_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_add_assign(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Subtracts `rhs` from `self` and returns the result.
    ///
    /// # Errors
    ///
    /// If the bit width of the given bitvectors do not match.
    pub fn bvsub(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::bvsub_mut)
    }

    /// Subtract assigns `self` to `rhs`.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvsub_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_sub_assign(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Multiplies `rhs` with `self` and returns the result.
    ///
    /// # Errors
    ///
    /// If the bit width of the given bitvectors do not match.
    pub fn bvmul(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::bvmul_mut)
    }

    /// Multiply assigns `self` to `rhs`.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvmul_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_mul_assign(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Divides signed `rhs` with `self` and returns the result.
    ///
    /// # Errors
    ///
    /// If the bit width of the given bitvectors do not match.
    pub fn bvsdiv(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::bvsdiv_mut)
    }

    /// Signed-divide assigns `self` to `rhs`.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvsdiv_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_sdiv_assign(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Divides unsigned `rhs` with `self` and returns the result.
    ///
    /// # Errors
    ///
    /// If the bit width of the given bitvectors do not match.
    pub fn bvudiv(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::bvudiv_mut)
    }

    /// Unsigned-divide assigns `self` to `rhs`.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvudiv_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_udiv_assign(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Returns the signed remainder: `self % rhs`
    ///
    /// # Errors
    ///
    /// If the bit width of the given bitvectors do not match.
    pub fn bvsrem(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::bvsrem_mut)
    }

    /// Signed-remainder assigns `self` to `rhs`.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvsrem_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_srem_assign(rhs.raw_val())
            .map_err(BitvecError::from)
    }

    /// Returns the unsigned remainder: `self % rhs`
    ///
    /// # Errors
    ///
    /// If the bit width of the given bitvectors do not match.
    pub fn bvurem(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::bvurem_mut)
    }

    /// Unsigned-remainder assigns `self` to `rhs`.
    ///
    /// # Errors
    ///
    /// If the bit widths of the given bitvectors do not match.
    pub fn bvurem_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_urem_assign(rhs.raw_val())
            .map_err(BitvecError::from)
    }
}

impl Bitvec {
    /// Zero-extends `self` to the target bitwidth and returns the result.
    ///
    /// # Errors
    ///
    /// If the given target width is invalid for this operation and `self`.
    pub fn zero_extend(self, target_width: BitWidth) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_zero_extend(target_width.raw_width())
            .map(Bitvec::from)
            .map_err(BitvecError::from)
    }

    /// Sign-extends `self` to the target bitwidth and returns the result.
    ///
    /// # Errors
    ///
    /// If the given target width is invalid for this operation and `self`.
    pub fn sign_extend(self, target_width: BitWidth) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_sign_extend(target_width.raw_width())
            .map(Bitvec::from)
            .map_err(BitvecError::from)
    }

    /// Concatenates `self` and `rhs` and returns the result.
    ///
    /// # Note
    ///
    /// The lower-bits of the resulting bitvector are represented
    /// by `rhs` while the upper bits are represented by `self`.
    pub fn concat(self, rhs: &Bitvec) -> Self {
        let target_width = BitWidth::from(self.width().len_bits() + rhs.width().len_bits());
        self.zero_extend(target_width)
            .and_then(|v| v.bvshl(rhs.width().len_bits()))
            .and_then(|v| {
                let rhs = rhs.clone().zero_extend(target_width).unwrap();
                v.bvor(&rhs)
            })
            .map(Bitvec::from)
            .unwrap()
    }

    /// Extracts the bits in the closed range of `[lo, hi]` of `self` and returns the result.
    ///
    /// # Errors
    ///
    /// If `lo` and `hi` are invalid bit bounds.
    pub fn extract(self, lo: usize, hi: usize) -> BitvecResult<Self> {
        if lo >= hi {
            return Err(BitvecError::invalid_extract_lo_hi_bounds(lo, hi, self));
        }
        let target_width = BitWidth::from(hi - lo);
        self.bvlshr(lo)
            .and_then(|v| {
                v.into_raw_val()
                    .into_truncate(target_width.raw_width())
                    .map_err(BitvecError::from)
            })
            .map(Bitvec::from)
            .map_err(BitvecError::from)
    }
}

impl Bitvec {
    /// Left-shifts `self` by the given `shamt` amount of bits.
    ///
    /// # Errors
    ///
    /// If the given shift amount is invalid.
    pub fn bvshl(self, shamt: usize) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, shamt, Bitvec::bvshl_mut)
    }

    /// Left-shift assigns `self` to `rhs`.
    ///
    /// # Errors
    ///
    /// If the given shift amount is invalid.
    pub fn bvshl_mut(&mut self, shamt: usize) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_shl_assign(shamt)
            .map_err(BitvecError::from)
    }

    /// Arithmetically right-shifts `self` by the given `shamt` amount of bits.
    ///
    /// # Errors
    ///
    /// If the given shift amount is invalid.
    pub fn bvashr(self, shamt: usize) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, shamt, Bitvec::bvashr_mut)
    }

    /// Arithmetically right-shift assigns `self` to `rhs`.
    ///
    /// # Errors
    ///
    /// If the given shift amount is invalid.
    pub fn bvashr_mut(&mut self, shamt: usize) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_ashr_assign(shamt)
            .map_err(BitvecError::from)
    }

    /// Logically right-shifts `self` by the given `shamt` amount of bits.
    ///
    /// # Errors
    ///
    /// If the given shift amount is invalid.
    pub fn bvlshr(self, shamt: usize) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, shamt, Bitvec::bvlshr_mut)
    }

    /// Logically right-shift assigns `self` to `rhs`.
    ///
    /// # Errors
    ///
    /// If the given shift amount is invalid.
    pub fn bvlshr_mut(&mut self, shamt: usize) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_lshr_assign(shamt)
            .map_err(BitvecError::from)
    }
}

impl Bitvec {
    /// Tries to convert `self` into `bool`.
    ///
    /// # Errors
    ///
    /// If the value of `self` is out of bounds for the result.
    pub fn to_bool(&self) -> BitvecResult<bool> {
        self.raw_val().try_to_bool().map_err(BitvecError::from)
    }

    /// Tries to convert `self` into `u32`.
    ///
    /// # Errors
    ///
    /// If the value of `self` is out of bounds for the result.
    pub fn to_u32(&self) -> BitvecResult<u32> {
        self.raw_val().try_to_u32().map_err(BitvecError::from)
    }

    /// Tries to convert `self` into `i32`.
    ///
    /// # Errors
    ///
    /// If the value of `self` is out of bounds for the result.
    pub fn to_i32(&self) -> BitvecResult<i32> {
        self.raw_val().try_to_i32().map_err(BitvecError::from)
    }

    /// Tries to convert `self` into `u64`.
    ///
    /// # Errors
    ///
    /// If the value of `self` is out of bounds for the result.
    pub fn to_u64(&self) -> BitvecResult<u64> {
        self.raw_val().try_to_u64().map_err(BitvecError::from)
    }

    /// Tries to convert `self` into `i64`.
    ///
    /// # Errors
    ///
    /// If the value of `self` is out of bounds for the result.
    pub fn to_i64(&self) -> BitvecResult<i64> {
        self.raw_val().try_to_i64().map_err(BitvecError::from)
    }
}
