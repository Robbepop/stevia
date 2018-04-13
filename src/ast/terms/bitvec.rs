use ast::prelude::*;

use apint;
use apint::Width;

use std::result;

/// Represents a bitvector in the sense of the SMT theory of bitvectors.
/// 
/// These are used to represent constant bitvector values.
/// This struct mainly wraps an underlying bitvector implementation
/// and provides an appropriate interface for SMT-like bitvectors.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Bitvec(apint::ApInt);

/// The result type for bitvector operations.
pub type BitvecResult<T> = result::Result<T, BitvecError>;

/// The error type for bitvector operations.
pub type BitvecError = apint::Error;

impl HasType for Bitvec {
    fn ty(&self) -> Type {
        Type::from(self.bitvec_ty())
    }
}

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

    /// Returns the concrete bitvector type of this bitvector.
    pub fn bitvec_ty(&self) -> BitvecTy {
        BitvecTy::from(self.width())
    }
}

impl Bitvec {
    /// Returns `true` if `self` is zero.
    pub fn is_zero(&self) -> bool {
        self.raw_val().is_zero()
    }

    /// Returns `true` if `self` is one.
    pub fn is_one(&self) -> bool {
        self.raw_val().is_one()
    }
}

impl Bitvec {
    /// Returns bit-negated `self`.
    pub fn bitnot(self) -> Self {
        let mut this = self;
        this.raw_val_mut().bitnot();
        this
    }

    /// Computes the bitwise and of `self` and `rhs` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn bitand(self, rhs: &Bitvec) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_checked_bitand(rhs.raw_val())
            .map(Bitvec::from)
    }

    /// Computes the bitwise or of `self` and `rhs` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn bitor(self, rhs: &Bitvec) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_checked_bitor(rhs.raw_val())
            .map(Bitvec::from)
    }

    /// Computes the bitwise exclusive or (XOR) of `self` and `rhs` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn bitxor(self, rhs: &Bitvec) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_checked_bitxor(rhs.raw_val())
            .map(Bitvec::from)
    }
}

impl Bitvec {
    /// Computes the signed greater-equals comparison between both given bitvectors.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn sge(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val().checked_sge(rhs.raw_val())
    }

    /// Computes the signed greater-than comparison between both given bitvectors.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn sgt(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val().checked_sgt(rhs.raw_val())
    }

    /// Computes the signed less-equals comparison between both given bitvectors.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn sle(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val().checked_sle(rhs.raw_val())
    }

    /// Computes the signed less-than comparison between both given bitvectors.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn slt(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val().checked_slt(rhs.raw_val())
    }

    /// Computes the unsigned greater-equals comparison between both given bitvectors.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn uge(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val().checked_uge(rhs.raw_val())
    }

    /// Computes the unsigned greater-than comparison between both given bitvectors.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn ugt(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val().checked_ugt(rhs.raw_val())
    }

    /// Computes the unsigned less-equals comparison between both given bitvectors.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn ule(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val().checked_ule(rhs.raw_val())
    }

    /// Computes the unsigned less-than comparison between both given bitvectors.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn ult(&self, rhs: &Bitvec) -> BitvecResult<bool> {
        self.raw_val().checked_ult(rhs.raw_val())
    }
}

impl Bitvec {
    /// Returns negated `self`.
    pub fn neg(self) -> Self {
        self.into_raw_val()
            .into_negate()
            .into()
    }

    /// Adds `rhs` to `self` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn add(self, rhs: &Bitvec) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_checked_add(rhs.raw_val())
            .map(Bitvec::from)
    }

    /// Subtracts `rhs` from `self` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn sub(self, rhs: &Bitvec) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_checked_sub(rhs.raw_val())
            .map(Bitvec::from)
    }

    /// Multiplies `rhs` with `self` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn mul(self, rhs: &Bitvec) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_checked_mul(rhs.raw_val())
            .map(Bitvec::from)
    }

    /// Divides signed `rhs` with `self` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn sdiv(self, rhs: &Bitvec) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_checked_sdiv(rhs.raw_val())
            .map(Bitvec::from)
    }

    /// Divides unsigned `rhs` with `self` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn udiv(self, rhs: &Bitvec) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_checked_udiv(rhs.raw_val())
            .map(Bitvec::from)
    }

    /// Returns the signed remainder: `self % rhs`
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn srem(self, rhs: &Bitvec) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_checked_srem(rhs.raw_val())
            .map(Bitvec::from)
    }

    /// Returns the unsigned remainder: `self % rhs`
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn urem(self, rhs: &Bitvec) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_checked_urem(rhs.raw_val())
            .map(Bitvec::from)
    }
}

impl Bitvec {
    /// Zero-extends `self` to the target bitwidth and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the given target width is invalid for this operation and `self`.
    pub fn zext(self, target_width: BitWidth) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_zero_extend(target_width.raw_width())
            .map(Bitvec::from)
    }

    /// Sign-extends `self` to the target bitwidth and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the given target width is invalid for this operation and `self`.
    pub fn sext(self, target_width: BitWidth) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_sign_extend(target_width.raw_width())
            .map(Bitvec::from)
    }

    /// Concatenates `self` and `rhs` and returns the result.
    /// 
    /// # Note
    /// 
    /// The lower-bits of the resulting bitvector are represented
    /// by `rhs` while the upper bits are represented by `self`.
    pub fn concat(self, rhs: &Bitvec) -> Self {
        let target_width = BitWidth::from(
            self.width().len_bits() +
            rhs.width().len_bits());
        self.zext(target_width)
            .and_then(|v| v.shl(rhs.width().len_bits()))
            .and_then(|v| {
                let rhs = rhs.clone()
                             .zext(target_width)
                             .unwrap();
                v.bitor(&rhs)
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
            unimplemented!() // TODO: create concrete BitvecError and BitvecResult wrapping ApIntError
        }
        let target_width = BitWidth::from(hi - lo);
        self.lshr(lo)
            .and_then(|v| v.into_raw_val().into_truncate(target_width.raw_width()))
            .map(Bitvec::from)
    }
}

impl Bitvec {
    /// Left-shifts `self` by the given `shamt` amount of bits.
    /// 
    /// # Errors
    /// 
    /// If the given shift amount is invalid.
    pub fn shl(self, shamt: usize) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_checked_shl(shamt)
            .map(Bitvec::from)
    }

    /// Arithmetically right-shifts `self` by the given `shamt` amount of bits.
    /// 
    /// # Errors
    /// 
    /// If the given shift amount is invalid.
    pub fn ashr(self, shamt: usize) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_checked_ashr(shamt)
            .map(Bitvec::from)
    }

    /// Logically right-shifts `self` by the given `shamt` amount of bits.
    /// 
    /// # Errors
    /// 
    /// If the given shift amount is invalid.
    pub fn lshr(self, shamt: usize) -> BitvecResult<Self> {
        self.into_raw_val()
            .into_checked_lshr(shamt)
            .map(Bitvec::from)
    }
}

impl Bitvec {
    /// Tries to convert `self` into `bool`.
    /// 
    /// # Errors
    /// 
    /// If the value of `self` is out of bounds for the result.
    pub fn to_bool(&self) -> BitvecResult<bool> {
        self.raw_val().try_to_bool()
    }

    /// Tries to convert `self` into `u32`.
    /// 
    /// # Errors
    /// 
    /// If the value of `self` is out of bounds for the result.
    pub fn to_u32(&self) -> BitvecResult<u32> {
        self.raw_val().try_to_u32()
    }

    /// Tries to convert `self` into `i32`.
    /// 
    /// # Errors
    /// 
    /// If the value of `self` is out of bounds for the result.
    pub fn to_i32(&self) -> BitvecResult<i32> {
        self.raw_val().try_to_i32()
    }

    /// Tries to convert `self` into `u64`.
    /// 
    /// # Errors
    /// 
    /// If the value of `self` is out of bounds for the result.
    pub fn to_u64(&self) -> BitvecResult<u64> {
        self.raw_val().try_to_u64()
    }

    /// Tries to convert `self` into `i64`.
    /// 
    /// # Errors
    /// 
    /// If the value of `self` is out of bounds for the result.
    pub fn to_i64(&self) -> BitvecResult<i64> {
        self.raw_val().try_to_i64()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod zero {
        use super::*;

        #[test]
        fn zero1() {
            assert_eq!(Bitvec::zero(BitWidth::w1()), Bitvec::from(false))
        }

        #[test]
        fn zero32() {
            assert_eq!(Bitvec::zero(BitWidth::w32()), Bitvec::from(0_u32))
        }
    }

    mod one {
        use super::*;

        #[test]
        fn one_1() {
            assert_eq!(Bitvec::one(BitWidth::w1()), Bitvec::from(true))
        }

        #[test]
        fn one_32() {
            assert_eq!(Bitvec::one(BitWidth::w32()), Bitvec::from(1_u32))
        }
    }

    mod all_set {
        use super::*;

        #[test]
        fn all_set_1() {
            assert_eq!(Bitvec::all_set(BitWidth::w1()), Bitvec::from(true))
        }

        #[test]
        fn all_set_32() {
            assert_eq!(Bitvec::all_set(BitWidth::w32()), Bitvec::from(0x_FFFF_FFFF_u32))
        }
    }

    mod len_bits {
        use super::*;

        #[test]
        fn w1() {
            assert_eq!(Bitvec::from(true).len_bits(), 1)
        }

        #[test]
        fn w32() {
            assert_eq!(Bitvec::from(42_u32).len_bits(), 32)
        }
    }

    mod width {
        use super::*;

        #[test]
        fn w1() {
            assert_eq!(Bitvec::from(true).width(), BitWidth::w1())
        }

        #[test]
        fn w32() {
            assert_eq!(Bitvec::from(42_u32).width(), BitWidth::w32())
        }
    }

    mod bitvec_ty {
        use super::*;

        #[test]
        fn w1() {
            assert_eq!(Bitvec::from(true).bitvec_ty(), BitvecTy::w1())
        }

        #[test]
        fn w32() {
            assert_eq!(Bitvec::from(42_u32).bitvec_ty(), BitvecTy::w32())
        }
    }

    mod ty {
        use super::*;

        #[test]
        fn w1() {
            assert_eq!(Bitvec::from(true).ty(), Type::from(BitvecTy::w1()))
        }

        #[test]
        fn w32() {
            assert_eq!(Bitvec::from(42_u32).ty(), Type::from(BitvecTy::w32()))
        }
    }

    mod shl {
        use super::*;

        #[test]
        fn simple() {
            assert_eq!(
                Bitvec::from(0x_ABCD_9876_u32).shl(16),
                Ok(Bitvec::from(0x_9876_0000_u32))
            )
        }

        #[test]
        fn from_1_to_2() {
            assert_eq!(
                Bitvec::from(1u16).shl(1),
                Ok(Bitvec::from(2u16))
            )
        }

        #[test]
        fn shift_by_zero() {
            assert_eq!(
                Bitvec::from(42_u32).shl(0),
                Ok(Bitvec::from(42_u32))
            )
        }

        #[test]
        fn shift_overflow() {
            assert!(Bitvec::from(1337_u32).shl(32).is_err());
            assert!(Bitvec::from(1337_u32).shl(1337).is_err())
        }

        #[test]
        fn shift_near_overflow() {
            assert_eq!(
                Bitvec::from(1_u32).shl(31),
                Ok(Bitvec::from(0x8000_0000_u32))
            )
        }
    }

    mod ashr {
        use super::*;

        #[test]
        fn pos_simple() {
            assert_eq!(
                Bitvec::from(0x_0123_4567_u32).ashr(16),
                Ok(Bitvec::from(0x_0000_0123_u32))
            )
        }

        #[test]
        fn neg_simple() {
            assert_eq!(
                Bitvec::from(0x_FEDC_BA98_u32).ashr(16),
                Ok(Bitvec::from(0x_FFFF_FEDC_u32))
            )
        }

        #[test]
        fn shift_by_zero() {
            assert_eq!(
                Bitvec::from(42_u32).ashr(0),
                Ok(Bitvec::from(42_u32))
            )
        }

        #[test]
        fn shift_overflow() {
            assert!(Bitvec::from(1337_u32).ashr(32).is_err());
            assert!(Bitvec::from(1337_u32).ashr(1337).is_err())
        }

        #[test]
        fn neg_shift_near_overflow() {
            assert_eq!(
                Bitvec::from(0x8000_0000_u32).ashr(31),
                Ok(Bitvec::from(0x_FFFF_FFFF_u32))
            )
        }

        #[test]
        fn pos_shift_near_overflow() {
            assert_eq!(
                Bitvec::from(0x7FFF_FFFF_u32).ashr(30),
                Ok(Bitvec::from(1_u32))
            )
        }
    }

    mod lshr {
        use super::*;

        #[test]
        fn simple() {
            assert_eq!(
                Bitvec::from(0x_FEDC_BA98_u32).lshr(16),
                Ok(Bitvec::from(0x_0000_FEDC_u32))
            )
        }

        #[test]
        fn shift_by_zero() {
            assert_eq!(
                Bitvec::from(42_u32).lshr(0),
                Ok(Bitvec::from(42_u32))
            )
        }

        #[test]
        fn shift_overflow() {
            assert!(Bitvec::from(1337_u32).lshr(32).is_err());
            assert!(Bitvec::from(1337_u32).lshr(1337).is_err())
        }

        #[test]
        fn shift_near_overflow() {
            assert_eq!(
                Bitvec::from(0x8000_0000_u32).lshr(31),
                Ok(Bitvec::from(0x_0000_0001_u32))
            )
        }
    }

    mod zext {
        use super::*;

        #[test]
        fn from_1_to_32() {
            assert_eq!(
                Bitvec::from(false).zext(BitWidth::w32()),
                Ok(Bitvec::from(0_u32))
            );
            assert_eq!(
                Bitvec::from(true).zext(BitWidth::w32()),
                Ok(Bitvec::from(1_u32))
            )
        }

        #[test]
        fn from_16_to_32() {
            assert_eq!(
                Bitvec::from(0x_ABCD_u16).zext(BitWidth::w32()),
                Ok(Bitvec::from(0x_ABCD_u32))
            )
        }

        #[test]
        fn eq_width() {
            assert_eq!(
                Bitvec::from(0x_0123_u16).zext(BitWidth::w16()),
                Ok(Bitvec::from(0x_0123_u16))
            )
        }

        #[test]
        fn neg16_to_32() {
            assert_eq!(
                Bitvec::from(0x_8042_u16).zext(BitWidth::w32()),
                Ok(Bitvec::from(0x_8042_u32))
            )
        }

        #[test]
        fn invalid_target_width() {
            assert!(Bitvec::from(42_u16).zext(BitWidth::from(15)).is_err());
            assert!(Bitvec::from(42_u32).zext(BitWidth::w16()).is_err())
        }
    }

    mod sext {
        use super::*;

        #[test]
        fn from_1_to_32() {
            assert_eq!(
                Bitvec::from(false).sext(BitWidth::w32()),
                Ok(Bitvec::from(0_u32))
            );
            assert_eq!(
                Bitvec::from(true).sext(BitWidth::w32()),
                Ok(Bitvec::from(0x_FFFF_FFFF_u32))
            )
        }

        #[test]
        fn from_16_to_32() {
            assert_eq!(
                Bitvec::from(0x_0123_u16).sext(BitWidth::w32()),
                Ok(Bitvec::from(0x_0123_u32))
            )
        }

        #[test]
        fn eq_width() {
            assert_eq!(
                Bitvec::from(0x_ABCD_u16).sext(BitWidth::w16()),
                Ok(Bitvec::from(0x_ABCD_u16))
            )
        }

        #[test]
        fn neg16_to_32() {
            assert_eq!(
                Bitvec::from(0x_8042_u16).sext(BitWidth::w32()),
                Ok(Bitvec::from(0x_FFFF_8042_u32))
            )
        }

        #[test]
        fn invalid_target_width() {
            assert!(Bitvec::from(42_u16).sext(BitWidth::from(15)).is_err());
            assert!(Bitvec::from(42_u32).sext(BitWidth::w16()).is_err())
        }
    }

    mod extract {
        use super::*;

        #[test]
        fn single_bit() {
            assert_eq!(
                Bitvec::from(0b_0110_1001_u8).extract(0, 1),
                Ok(Bitvec::from(true))
            );
            assert_eq!(
                Bitvec::from(0b_0110_1010_u8).extract(0, 1),
                Ok(Bitvec::from(false))
            );
        }

        #[test]
        fn lower_half() {
            assert_eq!(
                Bitvec::from(0x_ABCD_u16).extract(0, 8),
                Ok(Bitvec::from(0x_CD_u8))
            );
        }

        #[test]
        fn upper_half() {
            assert_eq!(
                Bitvec::from(0x_ABCD_u16).extract(8, 16),
                Ok(Bitvec::from(0x_AB_u8))
            );
        }

        #[test]
        fn full_range() {
            assert_eq!(
                Bitvec::from(0x_ABCD_u16).extract(0, 16),
                Ok(Bitvec::from(0x_ABCD_u16))
            );
        }

        #[test]
        #[ignore]
        fn err_eq_lo_hi() {
            // TODO: create concrete BitvecError and BitvecResult wrapping ApIntError
            assert!(Bitvec::from(1337_u16).extract(1, 1).is_err())
        }

        #[test]
        #[ignore]
        fn err_lo_lt_hi() {
            // TODO: create concrete BitvecError and BitvecResult wrapping ApIntError
            assert!(Bitvec::from(42_u16).extract(2, 1).is_err())
        }
    }

    mod concat {
        use super::*;

        #[test]
        fn u32_to_u64() {
            let lhs = Bitvec::from(0x_1234_5678_u32);
            let rhs = Bitvec::from(0x_ABCD_7543_u32);
            let expected = Bitvec::from(0x_1234_5678_ABCD_7543_u64);
            assert_eq!(lhs.concat(&rhs), expected);
        }

        #[test]
        fn u16_to_u32() {
            let lhs = Bitvec::from(0x_ABCD_u16);
            let rhs = Bitvec::from(0x_EF01_u16);
            let expected = Bitvec::from(0x_ABCD_EF01_u32);
            assert_eq!(lhs.concat(&rhs), expected);
        }
    }

    mod to_bool {
        use super::*;

        #[test]
        fn from_1_to_true() {
            let one = Bitvec::one(BitWidth::w32());
            assert_eq!(one.to_bool(), Ok(true));
        }

        #[test]
        fn from_0_to_false() {
            let zero = Bitvec::zero(BitWidth::w32());
            assert_eq!(zero.to_bool(), Ok(false));
        }

        #[test]
        fn failure() {
            let out_of_bounds = Bitvec::from(42_u32);
            assert!(out_of_bounds.to_bool().is_err());
        }
    }

    mod to_u32 {
        use super::*;

        #[test]
        fn zero64_to_zero32() {
            assert_eq!(Bitvec::from(0_u64).to_u32(), Ok(0))
        }

        #[test]
        fn one_eq_width() {
            assert_eq!(Bitvec::one(BitWidth::w32()).to_u32(), Ok(1));
        }

        #[test]
        fn simple_eq_width() {
            assert_eq!(Bitvec::from(42_i32).to_u32(), Ok(42));
        }

        #[test]
        fn simple_lt_width() {
            assert_eq!(Bitvec::from(1337_u64).to_u32(), Ok(1337))
        }

        #[test]
        fn minus_one_to_max() {
            use std::u32;
            assert_eq!(Bitvec::from(-1_i32).to_u32(), Ok(u32::MAX));
        }

        #[test]
        fn out_of_bounds() {
            use std::u32;
            assert!(Bitvec::from(u32::MAX as u64 + 1_u64).to_u32().is_err())
        }
    }

    mod to_i32 {
        use super::*;

        #[test]
        fn zero64_to_zero32() {
            assert_eq!(Bitvec::from(0_u64).to_i32(), Ok(0))
        }

        #[test]
        fn one_eq_width() {
            assert_eq!(Bitvec::one(BitWidth::w32()).to_i32(), Ok(1));
        }

        #[test]
        fn simple_eq_width() {
            assert_eq!(Bitvec::from(42_i32).to_i32(), Ok(42));
        }

        #[test]
        fn simple_lt_width() {
            assert_eq!(Bitvec::from(1337_u64).to_i32(), Ok(1337))
        }

        #[test]
        fn minus_one() {
            assert_eq!(Bitvec::from(-1_i32).to_i32(), Ok(-1));
        }

        #[test]
        fn out_of_bounds() {
            use std::u32;
            assert!(Bitvec::from(u32::MAX as u64 + 1_u64).to_i32().is_err())
        }
    }

    mod to_u64 {
        use super::*;

        #[test]
        fn zero128_to_zero64() {
            assert_eq!(Bitvec::from(0_u128).to_u64(), Ok(0))
        }

        #[test]
        fn one_eq_width() {
            assert_eq!(Bitvec::one(BitWidth::w64()).to_u64(), Ok(1));
        }

        #[test]
        fn simple_eq_width() {
            assert_eq!(Bitvec::from(42_i64).to_u64(), Ok(42));
        }

        #[test]
        fn simple_lt_width() {
            assert_eq!(Bitvec::from(1337_u128).to_u64(), Ok(1337))
        }

        #[test]
        fn minus_one_to_max() {
            use std::u64;
            assert_eq!(Bitvec::from(-1_i64).to_u64(), Ok(u64::MAX));
        }

        #[test]
        fn out_of_bounds() {
            use std::u64;
            assert!(Bitvec::from(u64::MAX as u128 + 1_u128).to_u64().is_err())
        }
    }

    mod to_i64 {
        use super::*;

        #[test]
        fn zero128_to_zero64() {
            assert_eq!(Bitvec::from(0_u64).to_i64(), Ok(0))
        }

        #[test]
        fn one_eq_width() {
            assert_eq!(Bitvec::one(BitWidth::w64()).to_i64(), Ok(1));
        }

        #[test]
        fn simple_eq_width() {
            assert_eq!(Bitvec::from(42_i64).to_i64(), Ok(42));
        }

        #[test]
        fn simple_lt_width() {
            assert_eq!(Bitvec::from(1337_u128).to_i64(), Ok(1337))
        }

        #[test]
        fn minus_one() {
            assert_eq!(Bitvec::from(-1_i64).to_i64(), Ok(-1));
        }

        #[test]
        fn out_of_bounds() {
            use std::u64;
            assert!(Bitvec::from(u64::MAX as u128 + 1_u128).to_i64().is_err())
        }
    }

}
