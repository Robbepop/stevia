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

    /// Returns `true` if all bits of `self` are set.
    pub fn is_all_set(&self) -> bool {
        self.raw_val().is_all_set()
    }

    /// Returns `true` if all bits of `self` are unset.
    pub fn is_all_unset(&self) -> bool {
        self.raw_val().is_zero()
    }
}

fn forward_mut_impl<T, F>(entity: T, op: F) -> T
where
    F: Fn(&mut T) -> ()
{
    let mut this = entity;
    op(&mut this);
    this
}

fn try_forward_bin_mut_impl<L, R, F>(entity: L, rhs: R, op: F) -> BitvecResult<L>
where
    F: Fn(&mut L, R) -> BitvecResult<()>
{
    let mut this = entity;
    op(&mut this, rhs)?;
    Ok(this)
}

impl Bitvec {
    /// Returns `self` with bits flipped.
    pub fn bitnot(self) -> Self {
        forward_mut_impl(self, Bitvec::bitnot_mut)
    }

    /// Flips bits of `self` inplace.
    pub fn bitnot_mut(&mut self) {
        self.raw_val_mut().bitnot()
    }

    /// Computes the bitwise and of `self` and `rhs` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn bitand(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::bitand_mut)
    }

    /// Bit-and assigns `self` to `rhs`.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn bitand_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_bitand_assign(rhs.raw_val())
    }

    /// Computes the bitwise or of `self` and `rhs` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn bitor(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::bitor_mut)
    }

    /// Bit-or assigns `self` to `rhs`.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn bitor_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_bitor_assign(rhs.raw_val())
    }

    /// Computes the bitwise exclusive or (XOR) of `self` and `rhs` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn bitxor(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::bitxor_mut)
    }

    /// Bit-xor assigns `self` to `rhs`.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn bitxor_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_bitxor_assign(rhs.raw_val())
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
        forward_mut_impl(self, Bitvec::negate_mut)
    }

    /// Negates `self` inplace.
    pub fn negate_mut(&mut self) {
        self.raw_val_mut().negate()
    }

    /// Adds `rhs` to `self` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn add(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::add_mut)
    }

    /// Add assigns `self` to `rhs`.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn add_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_add_assign(rhs.raw_val())
    }

    /// Subtracts `rhs` from `self` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn sub(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::sub_mut)
    }

    /// Subtract assigns `self` to `rhs`.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn sub_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_sub_assign(rhs.raw_val())
    }

    /// Multiplies `rhs` with `self` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn mul(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::mul_mut)
    }

    /// Multiply assigns `self` to `rhs`.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn mul_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_mul_assign(rhs.raw_val())
    }

    /// Divides signed `rhs` with `self` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn sdiv(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::sdiv_mut)
    }

    /// Signed-divide assigns `self` to `rhs`.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn sdiv_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_sdiv_assign(rhs.raw_val())
    }

    /// Divides unsigned `rhs` with `self` and returns the result.
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn udiv(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::udiv_mut)
    }

    /// Unsigned-divide assigns `self` to `rhs`.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn udiv_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_udiv_assign(rhs.raw_val())
    }

    /// Returns the signed remainder: `self % rhs`
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn srem(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::srem_mut)
    }

    /// Signed-remainder assigns `self` to `rhs`.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn srem_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_srem_assign(rhs.raw_val())
    }

    /// Returns the unsigned remainder: `self % rhs`
    /// 
    /// # Errors
    /// 
    /// If the bit width of the given bitvectors do not match.
    pub fn urem(self, rhs: &Bitvec) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, rhs, Bitvec::urem_mut)
    }

    /// Unsigned-remainder assigns `self` to `rhs`.
    /// 
    /// # Errors
    /// 
    /// If the bit widths of the given bitvectors do not match.
    pub fn urem_mut(&mut self, rhs: &Bitvec) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_urem_assign(rhs.raw_val())
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
        try_forward_bin_mut_impl(self, shamt, Bitvec::shl_mut)
    }

    /// Left-shift assigns `self` to `rhs`.
    /// 
    /// # Errors
    /// 
    /// If the given shift amount is invalid.
    pub fn shl_mut(&mut self, shamt: usize) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_shl_assign(shamt)
    }

    /// Arithmetically right-shifts `self` by the given `shamt` amount of bits.
    /// 
    /// # Errors
    /// 
    /// If the given shift amount is invalid.
    pub fn ashr(self, shamt: usize) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, shamt, Bitvec::ashr_mut)
    }

    /// Arithmetically right-shift assigns `self` to `rhs`.
    /// 
    /// # Errors
    /// 
    /// If the given shift amount is invalid.
    pub fn ashr_mut(&mut self, shamt: usize) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_ashr_assign(shamt)
    }

    /// Logically right-shifts `self` by the given `shamt` amount of bits.
    /// 
    /// # Errors
    /// 
    /// If the given shift amount is invalid.
    pub fn lshr(self, shamt: usize) -> BitvecResult<Self> {
        try_forward_bin_mut_impl(self, shamt, Bitvec::lshr_mut)
    }

    /// Logically right-shift assigns `self` to `rhs`.
    /// 
    /// # Errors
    /// 
    /// If the given shift amount is invalid.
    pub fn lshr_mut(&mut self, shamt: usize) -> BitvecResult<()> {
        self.raw_val_mut()
            .checked_lshr_assign(shamt)
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

    mod is_zero {
        use super::*;

        #[test]
        fn success() {
            assert!(Bitvec::zero(BitWidth::w32()).is_zero());
        }

        #[test]
        fn failure() {
            assert!(!Bitvec::one(BitWidth::w32()).is_zero());
        }
    }

    mod is_one {
        use super::*;

        #[test]
        fn success() {
            assert!(Bitvec::one(BitWidth::w32()).is_one());
        }

        #[test]
        fn failure() {
            assert!(!Bitvec::zero(BitWidth::w32()).is_one());
        }
    }

    mod is_all_set {
        use super::*;

        #[test]
        fn success() {
            assert!(Bitvec::from(true).is_all_set());
            assert!(Bitvec::all_set(BitWidth::w32()).is_all_set());
        }

        #[test]
        fn failure() {
            assert!(!Bitvec::from(false).is_all_set());
            assert!(!Bitvec::zero(BitWidth::w32()).is_all_set());
            assert!(!Bitvec::one(BitWidth::w32()).is_all_set())
        }
    }

    mod is_all_unset {
        use super::*;

        #[test]
        fn success() {
            assert!(Bitvec::from(false).is_all_unset());
            assert!(Bitvec::zero(BitWidth::w32()).is_all_unset());
        }

        #[test]
        fn failure() {
            assert!(!Bitvec::from(true).is_all_unset());
            assert!(!Bitvec::all_set(BitWidth::w32()).is_all_unset());
            assert!(!Bitvec::one(BitWidth::w32()).is_all_unset())
        }
    }

    mod bitnot {
        use super::*;

        #[test]
        fn w1() {
            assert_eq!(Bitvec::from(false).bitnot(), Bitvec::from(true));
            assert_eq!(Bitvec::from(true).bitnot(), Bitvec::from(false))
        }

        #[test]
        fn simple() {
            let fst = 0b_1010_0101_0110_1001_u16;
            let snd = 0b_0101_1010_1001_0110_u16;
            assert_eq!(
                Bitvec::from(fst).bitnot(),
                Bitvec::from(snd)
            );
            assert_eq!(
                Bitvec::from(snd).bitnot(),
                Bitvec::from(fst)
            )
        }

        #[test]
        fn zero_to_all_set() {
            assert_eq!(
                Bitvec::all_set(BitWidth::w32()).bitnot(),
                Bitvec::zero(BitWidth::w32())
            );
            assert_eq!(
                Bitvec::zero(BitWidth::w32()).bitnot(),
                Bitvec::all_set(BitWidth::w32())
            )
        }

        #[test]
        fn involution() {
            assert_eq!(Bitvec::from(42_u32).bitnot().bitnot(), Bitvec::from(42_u32))
        }
    }

    mod bitand {
        use super::*;

        #[test]
        fn w1() {
            fn test_with(lhs: bool, rhs: bool, result: bool) {
                assert_eq!(
                    Bitvec::from(lhs).bitand(&Bitvec::from(rhs)), Ok(Bitvec::from(result))
                )
            }
            test_with(false, false, false);
            test_with(false,  true, false);
            test_with( true, false, false);
            test_with( true,  true,  true);
        }

        #[test]
        fn simple() {
            assert_eq!(
                   Bitvec::from(0b_0101_1010_1001_0110_u16).bitand(&
                   Bitvec::from(0b_0011_1100_0101_1010_u16)),
                Ok(Bitvec::from(0b_0001_1000_0001_0010_u16))
            )
        }

        #[test]
        fn with_zero() {
            assert_eq!(
                Bitvec::from(1337_u32).bitand(&Bitvec::zero(BitWidth::w32())),
                Ok(Bitvec::zero(BitWidth::w32()))
            )
        }

        #[test]
        fn with_all_set() {
            assert_eq!(
                Bitvec::from(1337_u32).bitand(&Bitvec::all_set(BitWidth::w32())),
                Ok(Bitvec::from(1337_u32))
            )
        }

        #[test]
        fn failure() {
            assert!(Bitvec::from(42_u32).bitand(&Bitvec::from(1337_u64)).is_err())
        }
    }

    mod bitor {
        use super::*;

        #[test]
        fn w1() {
            fn test_with(lhs: bool, rhs: bool, result: bool) {
                assert_eq!(
                    Bitvec::from(lhs).bitor(&Bitvec::from(rhs)), Ok(Bitvec::from(result))
                )
            }
            test_with(false, false, false);
            test_with(false,  true,  true);
            test_with( true, false,  true);
            test_with( true,  true,  true);
        }

        #[test]
        fn simple() {
            assert_eq!(
                   Bitvec::from(0b_0101_1010_1001_0110_u16).bitor(&
                   Bitvec::from(0b_0011_1100_0101_1010_u16)),
                Ok(Bitvec::from(0b_0111_1110_1101_1110_u16))
            )
        }

        #[test]
        fn with_zero() {
            assert_eq!(
                Bitvec::from(1337_u32).bitor(&Bitvec::zero(BitWidth::w32())),
                Ok(Bitvec::from(1337_u32))
            )
        }

        #[test]
        fn with_all_set() {
            assert_eq!(
                Bitvec::from(1337_u32).bitor(&Bitvec::all_set(BitWidth::w32())),
                Ok(Bitvec::all_set(BitWidth::w32()))
            )
        }

        #[test]
        fn failure() {
            assert!(Bitvec::from(42_u32).bitor(&Bitvec::from(1337_u64)).is_err())
        }
    }

    mod bitxor {
        use super::*;

        #[test]
        fn w1() {
            fn test_with(lhs: bool, rhs: bool, result: bool) {
                assert_eq!(
                    Bitvec::from(lhs).bitxor(&Bitvec::from(rhs)), Ok(Bitvec::from(result))
                )
            }
            test_with(false, false, false);
            test_with(false,  true,  true);
            test_with( true, false,  true);
            test_with( true,  true, false);
        }

        #[test]
        fn simple() {
            assert_eq!(
                   Bitvec::from(0b_0101_1010_1001_0110_u16).bitxor(&
                   Bitvec::from(0b_0011_1100_0101_1010_u16)),
                Ok(Bitvec::from(0b_0110_0110_1100_1100_u16))
            )
        }

        #[test]
        fn with_zero() {
            assert_eq!(
                Bitvec::from(1337_u32).bitxor(&Bitvec::zero(BitWidth::w32())),
                Ok(Bitvec::from(1337_u32))
            )
        }

        #[test]
        fn all_set_eq_bitnot() {
            assert_eq!(
                Bitvec::from(1337_u32).bitxor(&Bitvec::all_set(BitWidth::w32())),
                Ok(Bitvec::from(1337_u32).bitnot())
            )
        }

        #[test]
        fn failure() {
            assert!(Bitvec::from(42_u32).bitxor(&Bitvec::from(1337_u64)).is_err())
        }
    }

    mod cmp {
        use super::*;

        fn invalid_cmp<L, R>(lhs: L, rhs: R)
        where
            L: Into<Bitvec> + Ord + Copy,
            R: Into<Bitvec> + Ord + Copy
        {
            assert!(rhs.into().sge(&lhs.into()).is_err());
            assert!(rhs.into().sgt(&lhs.into()).is_err());
            assert!(rhs.into().sle(&lhs.into()).is_err());
            assert!(rhs.into().slt(&lhs.into()).is_err());
            assert!(rhs.into().uge(&lhs.into()).is_err());
            assert!(rhs.into().ugt(&lhs.into()).is_err());
            assert!(rhs.into().ule(&lhs.into()).is_err());
            assert!(rhs.into().ult(&lhs.into()).is_err());
        }

        fn symmetric_invalid_cmp<L, R>(rhs: L, lhs: R)
        where
            L: Into<Bitvec> + Ord + Copy,
            R: Into<Bitvec> + Ord + Copy
        {
            invalid_cmp(lhs, rhs);
            invalid_cmp(rhs, lhs);
        }

        mod signed {
            use super::*;

            fn valid_cmp<T>(lhs: T, rhs: T)
            where
                T: Into<Bitvec> + Ord + Copy
            {
                assert_eq!(lhs.into().sge(&rhs.into()), Ok(lhs >= rhs));
                assert_eq!(lhs.into().sgt(&rhs.into()), Ok(lhs >  rhs));
                assert_eq!(lhs.into().sle(&rhs.into()), Ok(lhs <= rhs));
                assert_eq!(lhs.into().slt(&rhs.into()), Ok(lhs <  rhs));
            }

            fn symmetric_valid_cmp<T>(lhs: T, rhs: T)
            where
                T: Into<Bitvec> + Ord + Copy
            {
                valid_cmp(lhs, rhs);
                valid_cmp(rhs, lhs)
            }

            #[test]
            fn zero_one() {
                valid_cmp(0_i32, 0_i32);
                symmetric_valid_cmp(0_i32, 1_i32);
                valid_cmp(1_i32, 1_i32)
            }

            #[test]
            fn neg_and_pos() {
                symmetric_valid_cmp(42_i32, 1337_i32);
                symmetric_valid_cmp(42_i32, -1337_i32);
                symmetric_valid_cmp(-42_i32, 1337_i32);
                symmetric_valid_cmp(-42_i32, -1337_i32);
            }

            #[test]
            fn min_max() {
                use std::i32;
                symmetric_valid_cmp(i32::MIN, i32::MAX)
            }

            #[test]
            fn cmp_eq() {
                valid_cmp(42_i32, 42_i32);
                valid_cmp(1337_i32, 1337_i32);
            }

            #[test]
            fn failure() {
                symmetric_invalid_cmp(0_i32, 0_i64);
                symmetric_invalid_cmp(1_i32, 1_i64);
                symmetric_invalid_cmp(42_i32, 1337_i64);
                symmetric_invalid_cmp(42_i64, 1337_i32);
            }
        }

        mod unsigned {
            use super::*;

            fn valid_cmp<T>(lhs: T, rhs: T)
            where
                T: Into<Bitvec> + Ord + Copy
            {
                assert_eq!(lhs.into().uge(&rhs.into()), Ok(lhs >= rhs));
                assert_eq!(lhs.into().ugt(&rhs.into()), Ok(lhs >  rhs));
                assert_eq!(lhs.into().ule(&rhs.into()), Ok(lhs <= rhs));
                assert_eq!(lhs.into().ult(&rhs.into()), Ok(lhs <  rhs));
            }

            fn symmetric_valid_cmp<T>(lhs: T, rhs: T)
            where
                T: Into<Bitvec> + Ord + Copy
            {
                valid_cmp(lhs, rhs);
                valid_cmp(rhs, lhs)
            }

            #[test]
            fn w1() {
                symmetric_valid_cmp(false, true);
            }

            #[test]
            fn zero_one() {
                valid_cmp(0_u32, 0_u32);
                symmetric_valid_cmp(0_u32, 1_u32);
                valid_cmp(1_u32, 1_u32)
            }

            #[test]
            fn min_max() {
                use std::u32;
                symmetric_valid_cmp(u32::MIN, u32::MAX)
            }

            #[test]
            fn cmp_eq() {
                valid_cmp(42_u32, 42_u32);
                valid_cmp(1337_u32, 1337_u32);
            }

            #[test]
            fn failure() {
                symmetric_invalid_cmp(0_u32, 0_u64);
                symmetric_invalid_cmp(1_u32, 1_u64);
                symmetric_invalid_cmp(42_u32, 1337_u64);
                symmetric_invalid_cmp(42_u64, 1337_u32);
            }
        }
    }

    mod neg {
        use super::*;

        #[test]
        fn w1() {
            assert_eq!(Bitvec::from(false).neg(), Bitvec::from(false));
            assert_eq!(Bitvec::from(true).neg(), Bitvec::from(true))
        }

        #[test]
        fn simple() {
            assert_eq!(
                Bitvec::from(42_i32).neg(),
                Bitvec::from(-42_i32)
            );
            assert_eq!(
                Bitvec::from(-42_i32).neg(),
                Bitvec::from(42_i32)
            )
        }

        #[test]
        fn zero_to_zero() {
            assert_eq!(
                Bitvec::zero(BitWidth::w32()).neg(),
                Bitvec::zero(BitWidth::w32())
            )
        }

        #[test]
        fn min_to_min() {
            use std::i32;
            assert_eq!(
                Bitvec::from(i32::MIN).neg(),
                Bitvec::from(i32::MIN)
            )
        }

        #[test]
        fn involution() {
            assert_eq!(Bitvec::from(42_i32).neg().neg(), Bitvec::from(42_i32));
            assert_eq!(Bitvec::from(-1337_i32).neg().neg(), Bitvec::from(-1337_i32))
        }
    }

    mod add {
        use super::*;
        use std::ops::Add;

        fn valid_add<T>(lhs: T, rhs: T)
        where
            T: Into<Bitvec> + Add + Copy,
            Bitvec: From<<T as Add>::Output>
        {
            assert_eq!(lhs.into().add(&rhs.into()), Ok(Bitvec::from(lhs + rhs)));
        }

        fn symmetric_valid_add<T>(lhs: T, rhs: T)
        where
            T: Into<Bitvec> + Add + Copy,
            Bitvec: From<<T as Add>::Output>
        {
            valid_add(lhs, rhs);
            valid_add(rhs, lhs)
        }

        #[test]
        fn w1() {
            assert_eq!(Bitvec::from(false).add(&Bitvec::from(false)), Ok(Bitvec::from(false)));
            assert_eq!(Bitvec::from(false).add(&Bitvec::from( true)), Ok(Bitvec::from( true)));
            assert_eq!(Bitvec::from( true).add(&Bitvec::from(false)), Ok(Bitvec::from( true)));
            assert_eq!(Bitvec::from( true).add(&Bitvec::from( true)), Ok(Bitvec::from(false)));
        }

        #[test]
        fn both_zero() {
            valid_add(0_i32, 0_i32)
        }

        #[test]
        fn one_zero() {
            symmetric_valid_add(42_i32, 0_i32);
            symmetric_valid_add(1337_i32, 0_i32);
            symmetric_valid_add(5_i32, 0_i32)
        }

        #[test]
        fn pos_neg() {
            symmetric_valid_add( 42_i32,  5_i32);
            symmetric_valid_add(-42_i32,  5_i32);
            symmetric_valid_add( 42_i32, -5_i32);
            symmetric_valid_add(-42_i32, -5_i32)
        }

        #[test]
        fn eq_zero() {
            symmetric_valid_add(-42_i32, 42_i32)
        }

        #[test]
        fn fail() {
            assert!(Bitvec::from(42_i32).add(&Bitvec::from(1337_i64)).is_err());
        }
    }

    mod sub {
        use super::*;
        use std::ops::Sub;

        fn valid_sub<T>(lhs: T, rhs: T)
        where
            T: Into<Bitvec> + Sub + Copy,
            Bitvec: From<<T as Sub>::Output>
        {
            assert_eq!(lhs.into().sub(&rhs.into()), Ok(Bitvec::from(lhs - rhs)));
        }

        #[test]
        fn w1() {
            assert_eq!(Bitvec::from(false).sub(&Bitvec::from(false)), Ok(Bitvec::from(false)));
            assert_eq!(Bitvec::from(false).sub(&Bitvec::from( true)), Ok(Bitvec::from( true)));
            assert_eq!(Bitvec::from( true).sub(&Bitvec::from(false)), Ok(Bitvec::from( true)));
            assert_eq!(Bitvec::from( true).sub(&Bitvec::from( true)), Ok(Bitvec::from(false)));
        }

        #[test]
        fn both_zero() {
            valid_sub(0_i32, 0_i32)
        }

        #[test]
        fn one_zero() {
            valid_sub(  42_i32,    0_i32);
            valid_sub(   0_i32,   42_i32);
            valid_sub(1337_i32,    0_i32);
            valid_sub(   0_i32, 1337_i32);
            valid_sub(   5_i32,    0_i32);
            valid_sub(   0_i32,    5_i32)
        }

        #[test]
        fn pos_neg() {
            valid_sub( 42_i32,  5_i32);
            valid_sub( 42_i32, -5_i32);
            valid_sub(-42_i32,  5_i32);
            valid_sub(-42_i32, -5_i32)
        }

        #[test]
        fn eq_zero() {
            valid_sub(123_i32, 123_i32)
        }

        #[test]
        fn fail() {
            assert!(Bitvec::from(42_i32).sub(&Bitvec::from(1337_i64)).is_err());
        }
    }

    mod mul {
        use super::*;
        use std::ops::Mul;

        fn valid_mul<T>(lhs: T, rhs: T)
        where
            T: Into<Bitvec> + Mul + Copy,
            Bitvec: From<<T as Mul>::Output>
        {
            assert_eq!(lhs.into().mul(&rhs.into()), Ok(Bitvec::from(lhs * rhs)));
        }

        fn symmetric_valid_mul<T>(lhs: T, rhs: T)
        where
            T: Into<Bitvec> + Mul + Copy,
            Bitvec: From<<T as Mul>::Output>
        {
            valid_mul(lhs, rhs);
            valid_mul(rhs, lhs)
        }

        #[test]
        fn w1() {
            assert_eq!(Bitvec::from(false).mul(&Bitvec::from(false)), Ok(Bitvec::from(false)));
            assert_eq!(Bitvec::from(false).mul(&Bitvec::from( true)), Ok(Bitvec::from(false)));
            assert_eq!(Bitvec::from( true).mul(&Bitvec::from(false)), Ok(Bitvec::from(false)));
            assert_eq!(Bitvec::from( true).mul(&Bitvec::from( true)), Ok(Bitvec::from( true)));
        }

        #[test]
        fn both_zero() {
            valid_mul(0_i32, 0_i32)
        }

        #[test]
        fn one_zero() {
            symmetric_valid_mul(  42_i32,    0_i32);
            symmetric_valid_mul(1337_i32,    0_i32);
            symmetric_valid_mul(   5_i32,    0_i32);
        }

        #[test]
        fn one_one() {
            symmetric_valid_mul(  42_i32,    1_i32);
            symmetric_valid_mul(1337_i32,    1_i32);
            symmetric_valid_mul(   5_i32,    1_i32);
        }

        #[test]
        fn pos_neg() {
            symmetric_valid_mul( 42_i32,  5_i32);
            symmetric_valid_mul( 42_i32, -5_i32);
            symmetric_valid_mul(-42_i32,  5_i32);
            symmetric_valid_mul(-42_i32, -5_i32)
        }

        #[test]
        fn fail() {
            assert!(Bitvec::from(42_i32).mul(&Bitvec::from(1337_i64)).is_err());
        }
    }

    mod div {
        use super::*;
        use std::ops::Div;

        mod signed {
            use super::*;

            fn valid_div<T>(lhs: T, rhs: T)
            where
                T: Into<Bitvec> + Div + Copy,
                Bitvec: From<<T as Div>::Output>
            {
                assert_eq!(lhs.into().sdiv(&rhs.into()), Ok(Bitvec::from(lhs / rhs)));
            }

            fn symmetric_valid_div<T>(lhs: T, rhs: T)
            where
                T: Into<Bitvec> + Div + Copy,
                Bitvec: From<<T as Div>::Output>
            {
                valid_div(lhs, rhs);
                valid_div(rhs, lhs)
            }

            #[test]
            fn simple() {
                symmetric_valid_div(42_i32, 5_i32);
                symmetric_valid_div(1337_i32, 42_i32);
                symmetric_valid_div(12_i32, 4_i32)
            }

            #[test]
            fn pos_neg() {
                symmetric_valid_div( 12_i32, -3_i32);
                symmetric_valid_div(-12_i32,  3_i32);
                symmetric_valid_div(-12_i32, -3_i32)
            }

            #[test]
            fn rhs_is_one() {
                valid_div(  42_i32, 1_i32);
                valid_div(1337_i32, 1_i32);
                valid_div(   5_i32, 1_i32);
                valid_div(   1_i32, 1_i32);
                valid_div(   0_i32, 1_i32)
            }

            #[test]
            fn lhs_is_one() {
                valid_div(1_i32,   42_i32);
                valid_div(1_i32, 1337_i32);
                valid_div(1_i32,    5_i32)
            }
        }

        mod unsigned {
            use super::*;

            fn valid_div<T>(lhs: T, rhs: T)
            where
                T: Into<Bitvec> + Div + Copy,
                Bitvec: From<<T as Div>::Output>
            {
                assert_eq!(lhs.into().udiv(&rhs.into()), Ok(Bitvec::from(lhs / rhs)));
            }

            fn symmetric_valid_div<T>(lhs: T, rhs: T)
            where
                T: Into<Bitvec> + Div + Copy,
                Bitvec: From<<T as Div>::Output>
            {
                valid_div(lhs, rhs);
                valid_div(rhs, lhs)
            }

            #[test]
            fn simple() {
                symmetric_valid_div(42_i32, 5_i32);
                symmetric_valid_div(1337_i32, 42_i32);
                symmetric_valid_div(12_i32, 4_i32)
            }

            #[test]
            fn rhs_is_one() {
                valid_div(  42_i32, 1_i32);
                valid_div(1337_i32, 1_i32);
                valid_div(   5_i32, 1_i32);
                valid_div(   1_i32, 1_i32);
                valid_div(   0_i32, 1_i32)
            }

            #[test]
            fn lhs_is_one() {
                valid_div(1_i32,   42_i32);
                valid_div(1_i32, 1337_i32);
                valid_div(1_i32,    5_i32)
            }
        }

        #[test]
        fn div_by_zero() {
            fn test_div_by_zero(lhs: i32) {
                assert!(Bitvec::from(lhs).sdiv(&Bitvec::from(0_i32)).is_err());
                assert!(Bitvec::from(lhs).udiv(&Bitvec::from(0_i32)).is_err());
            }
            test_div_by_zero(1337);
            test_div_by_zero(42);
            test_div_by_zero(5);
            test_div_by_zero(0)
        }

        #[test]
        fn fail_width() {
            assert!(Bitvec::from(42_i32).sdiv(&Bitvec::from(1337_i64)).is_err());
            assert!(Bitvec::from(42_i32).udiv(&Bitvec::from(1337_i64)).is_err());
        }
    }

    mod rem {
        use super::*;
        use std::ops::Rem;

        mod signed {
            use super::*;

            fn valid_rem<T>(lhs: T, rhs: T)
            where
                T: Into<Bitvec> + Rem + Copy,
                Bitvec: From<<T as Rem>::Output>
            {
                assert_eq!(lhs.into().srem(&rhs.into()), Ok(Bitvec::from(lhs % rhs)));
            }

            fn symmetric_valid_rem<T>(lhs: T, rhs: T)
            where
                T: Into<Bitvec> + Rem + Copy,
                Bitvec: From<<T as Rem>::Output>
            {
                valid_rem(lhs, rhs);
                valid_rem(rhs, lhs)
            }

            #[test]
            fn simple() {
                symmetric_valid_rem(42_i32, 5_i32);
                symmetric_valid_rem(1337_i32, 42_i32);
                symmetric_valid_rem(12_i32, 4_i32)
            }

            #[test]
            fn pos_neg() {
                symmetric_valid_rem( 12_i32, -3_i32);
                symmetric_valid_rem(-12_i32,  3_i32);
                symmetric_valid_rem(-12_i32, -3_i32)
            }

            #[test]
            fn rhs_is_one() {
                valid_rem(  42_i32, 1_i32);
                valid_rem(1337_i32, 1_i32);
                valid_rem(   5_i32, 1_i32);
                valid_rem(   1_i32, 1_i32);
                valid_rem(   0_i32, 1_i32)
            }

            #[test]
            fn lhs_is_one() {
                valid_rem(1_i32,   42_i32);
                valid_rem(1_i32, 1337_i32);
                valid_rem(1_i32,    5_i32)
            }
        }

        mod unsigned {
            use super::*;

            fn valid_rem<T>(lhs: T, rhs: T)
            where
                T: Into<Bitvec> + Rem + Copy,
                Bitvec: From<<T as Rem>::Output>
            {
                assert_eq!(lhs.into().urem(&rhs.into()), Ok(Bitvec::from(lhs % rhs)));
            }

            fn symmetric_valid_rem<T>(lhs: T, rhs: T)
            where
                T: Into<Bitvec> + Rem + Copy,
                Bitvec: From<<T as Rem>::Output>
            {
                valid_rem(lhs, rhs);
                valid_rem(rhs, lhs)
            }

            #[test]
            fn simple() {
                symmetric_valid_rem(42_i32, 5_i32);
                symmetric_valid_rem(1337_i32, 42_i32);
                symmetric_valid_rem(12_i32, 4_i32)
            }

            #[test]
            fn rhs_is_one() {
                valid_rem(  42_i32, 1_i32);
                valid_rem(1337_i32, 1_i32);
                valid_rem(   5_i32, 1_i32);
                valid_rem(   1_i32, 1_i32);
                valid_rem(   0_i32, 1_i32)
            }

            #[test]
            fn lhs_is_one() {
                valid_rem(1_i32,   42_i32);
                valid_rem(1_i32, 1337_i32);
                valid_rem(1_i32,    5_i32)
            }
        }

        #[test]
        fn div_by_zero() {
            fn test_div_by_zero(lhs: i32) {
                assert!(Bitvec::from(lhs).srem(&Bitvec::from(0_i32)).is_err());
                assert!(Bitvec::from(lhs).urem(&Bitvec::from(0_i32)).is_err());
            }
            test_div_by_zero(1337);
            test_div_by_zero(42);
            test_div_by_zero(5);
            test_div_by_zero(0)
        }

        #[test]
        fn fail_width() {
            assert!(Bitvec::from(42_i32).srem(&Bitvec::from(1337_i64)).is_err());
            assert!(Bitvec::from(42_i32).urem(&Bitvec::from(1337_i64)).is_err());
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
