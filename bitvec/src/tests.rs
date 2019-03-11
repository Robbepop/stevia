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
		assert_eq!(
			Bitvec::all_set(BitWidth::w32()),
			Bitvec::from(0x_FFFF_FFFF_u32)
		)
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

mod is_even {
	use super::*;

	#[test]
	fn success() {
		assert!(Bitvec::from(false).is_even());
		assert!(Bitvec::zero(BitWidth::w32()).is_even());
		assert!(Bitvec::from(42_i32).is_even());
	}

	#[test]
	fn failure() {
		assert!(!Bitvec::from(true).is_even());
		assert!(!Bitvec::one(BitWidth::w32()).is_even());
		assert!(!Bitvec::from(1337_i32).is_even());
	}
}

mod is_odd {
	use super::*;

	#[test]
	fn success() {
		assert!(Bitvec::from(true).is_odd());
		assert!(Bitvec::one(BitWidth::w32()).is_odd());
		assert!(Bitvec::from(1337_i32).is_odd());
	}

	#[test]
	fn failure() {
		assert!(!Bitvec::from(false).is_odd());
		assert!(!Bitvec::zero(BitWidth::w32()).is_odd());
		assert!(!Bitvec::from(42_i32).is_odd());
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

mod is_umax {
	use super::*;

	#[test]
	fn success() {
		assert!(Bitvec::from(true).is_umax());
		assert!(Bitvec::all_set(BitWidth::w32()).is_umax());
	}

	#[test]
	fn failure() {
		assert!(!Bitvec::from(false).is_umax());
		assert!(!Bitvec::zero(BitWidth::w32()).is_umax());
		assert!(!Bitvec::one(BitWidth::w32()).is_umax())
	}
}

mod is_umin {
	use super::*;

	#[test]
	fn success() {
		assert!(Bitvec::from(false).is_umin());
		assert!(Bitvec::zero(BitWidth::w32()).is_umin());
	}

	#[test]
	fn failure() {
		assert!(!Bitvec::from(true).is_umin());
		assert!(!Bitvec::all_set(BitWidth::w32()).is_umin());
		assert!(!Bitvec::one(BitWidth::w32()).is_umin())
	}
}

mod is_smax {
	use super::*;

	#[test]
	fn success() {
		assert!(Bitvec::from(false).is_smax());
		assert!(Bitvec::from(std::i32::MAX).is_smax());
	}

	#[test]
	fn failure() {
		assert!(!Bitvec::from(true).is_smax());
		assert!(!Bitvec::from(std::i32::MAX - 1).is_smax());
		assert!(!Bitvec::one(BitWidth::w32()).is_smax())
	}
}

mod is_smin {
	use super::*;

	#[test]
	fn success() {
		assert!(Bitvec::from(true).is_smin());
		assert!(Bitvec::from(std::i32::MIN).is_smin());
	}

	#[test]
	fn failure() {
		assert!(!Bitvec::from(false).is_smin());
		assert!(!Bitvec::from(std::i32::MIN + 1).is_smin());
		assert!(!Bitvec::zero(BitWidth::w32()).is_smin());
		assert!(!Bitvec::one(BitWidth::w32()).is_smin());
	}
}

mod bitnot {
	use super::*;

	#[test]
	fn w1() {
		assert_eq!(Bitvec::from(false).bvnot(), Bitvec::from(true));
		assert_eq!(Bitvec::from(true).bvnot(), Bitvec::from(false))
	}

	#[test]
	fn simple() {
		let fst = 0b_1010_0101_0110_1001_u16;
		let snd = 0b_0101_1010_1001_0110_u16;
		assert_eq!(Bitvec::from(fst).bvnot(), Bitvec::from(snd));
		assert_eq!(Bitvec::from(snd).bvnot(), Bitvec::from(fst))
	}

	#[test]
	fn zero_to_all_set() {
		assert_eq!(
			Bitvec::all_set(BitWidth::w32()).bvnot(),
			Bitvec::zero(BitWidth::w32())
		);
		assert_eq!(
			Bitvec::zero(BitWidth::w32()).bvnot(),
			Bitvec::all_set(BitWidth::w32())
		)
	}

	#[test]
	fn involution() {
		assert_eq!(Bitvec::from(42_u32).bvnot().bvnot(), Bitvec::from(42_u32))
	}
}

mod bitand {
	use super::*;

	#[test]
	fn w1() {
		fn test_with(lhs: bool, rhs: bool, result: bool) {
			assert_eq!(
				Bitvec::from(lhs).bvand(&Bitvec::from(rhs)),
				Ok(Bitvec::from(result))
			)
		}
		test_with(false, false, false);
		test_with(false, true, false);
		test_with(true, false, false);
		test_with(true, true, true);
	}

	#[test]
	fn simple() {
		assert_eq!(
			Bitvec::from(0b_0101_1010_1001_0110_u16)
				.bvand(&Bitvec::from(0b_0011_1100_0101_1010_u16)),
			Ok(Bitvec::from(0b_0001_1000_0001_0010_u16))
		)
	}

	#[test]
	fn with_zero() {
		assert_eq!(
			Bitvec::from(1337_u32).bvand(&Bitvec::zero(BitWidth::w32())),
			Ok(Bitvec::zero(BitWidth::w32()))
		)
	}

	#[test]
	fn with_all_set() {
		assert_eq!(
			Bitvec::from(1337_u32).bvand(&Bitvec::all_set(BitWidth::w32())),
			Ok(Bitvec::from(1337_u32))
		)
	}

	#[test]
	fn failure() {
		assert!(
			Bitvec::from(42_u32)
				.bvand(&Bitvec::from(1337_u64))
				.is_err()
		)
	}
}

mod bitor {
	use super::*;

	#[test]
	fn w1() {
		fn test_with(lhs: bool, rhs: bool, result: bool) {
			assert_eq!(
				Bitvec::from(lhs).bvor(&Bitvec::from(rhs)),
				Ok(Bitvec::from(result))
			)
		}
		test_with(false, false, false);
		test_with(false, true, true);
		test_with(true, false, true);
		test_with(true, true, true);
	}

	#[test]
	fn simple() {
		assert_eq!(
			Bitvec::from(0b_0101_1010_1001_0110_u16)
				.bvor(&Bitvec::from(0b_0011_1100_0101_1010_u16)),
			Ok(Bitvec::from(0b_0111_1110_1101_1110_u16))
		)
	}

	#[test]
	fn with_zero() {
		assert_eq!(
			Bitvec::from(1337_u32).bvor(&Bitvec::zero(BitWidth::w32())),
			Ok(Bitvec::from(1337_u32))
		)
	}

	#[test]
	fn with_all_set() {
		assert_eq!(
			Bitvec::from(1337_u32).bvor(&Bitvec::all_set(BitWidth::w32())),
			Ok(Bitvec::all_set(BitWidth::w32()))
		)
	}

	#[test]
	fn failure() {
		assert!(Bitvec::from(42_u32).bvor(&Bitvec::from(1337_u64)).is_err())
	}
}

mod bitxor {
	use super::*;

	#[test]
	fn w1() {
		fn test_with(lhs: bool, rhs: bool, result: bool) {
			assert_eq!(
				Bitvec::from(lhs).bvxor(&Bitvec::from(rhs)),
				Ok(Bitvec::from(result))
			)
		}
		test_with(false, false, false);
		test_with(false, true, true);
		test_with(true, false, true);
		test_with(true, true, false);
	}

	#[test]
	fn simple() {
		assert_eq!(
			Bitvec::from(0b_0101_1010_1001_0110_u16)
				.bvxor(&Bitvec::from(0b_0011_1100_0101_1010_u16)),
			Ok(Bitvec::from(0b_0110_0110_1100_1100_u16))
		)
	}

	#[test]
	fn with_zero() {
		assert_eq!(
			Bitvec::from(1337_u32).bvxor(&Bitvec::zero(BitWidth::w32())),
			Ok(Bitvec::from(1337_u32))
		)
	}

	#[test]
	fn all_set_eq_bitnot() {
		assert_eq!(
			Bitvec::from(1337_u32).bvxor(&Bitvec::all_set(BitWidth::w32())),
			Ok(Bitvec::from(1337_u32).bvnot())
		)
	}

	#[test]
	fn failure() {
		assert!(
			Bitvec::from(42_u32)
				.bvxor(&Bitvec::from(1337_u64))
				.is_err()
		)
	}
}

mod cmp {
	use super::*;

	fn invalid_cmp<L, R>(lhs: L, rhs: R)
	where
		L: Into<Bitvec> + Ord + Copy,
		R: Into<Bitvec> + Ord + Copy,
	{
		assert!(rhs.into().bvsge(&lhs.into()).is_err());
		assert!(rhs.into().bvsgt(&lhs.into()).is_err());
		assert!(rhs.into().bvsle(&lhs.into()).is_err());
		assert!(rhs.into().bvslt(&lhs.into()).is_err());
		assert!(rhs.into().bvuge(&lhs.into()).is_err());
		assert!(rhs.into().bvugt(&lhs.into()).is_err());
		assert!(rhs.into().bvule(&lhs.into()).is_err());
		assert!(rhs.into().bvult(&lhs.into()).is_err());
	}

	fn symmetric_invalid_cmp<L, R>(rhs: L, lhs: R)
	where
		L: Into<Bitvec> + Ord + Copy,
		R: Into<Bitvec> + Ord + Copy,
	{
		invalid_cmp(lhs, rhs);
		invalid_cmp(rhs, lhs);
	}

	mod signed {
		use super::*;

		fn valid_cmp<T>(lhs: T, rhs: T)
		where
			T: Into<Bitvec> + Ord + Copy,
		{
			assert_eq!(lhs.into().bvsge(&rhs.into()), Ok(lhs >= rhs));
			assert_eq!(lhs.into().bvsgt(&rhs.into()), Ok(lhs > rhs));
			assert_eq!(lhs.into().bvsle(&rhs.into()), Ok(lhs <= rhs));
			assert_eq!(lhs.into().bvslt(&rhs.into()), Ok(lhs < rhs));
		}

		fn symmetric_valid_cmp<T>(lhs: T, rhs: T)
		where
			T: Into<Bitvec> + Ord + Copy,
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
			T: Into<Bitvec> + Ord + Copy,
		{
			assert_eq!(lhs.into().bvuge(&rhs.into()), Ok(lhs >= rhs));
			assert_eq!(lhs.into().bvugt(&rhs.into()), Ok(lhs > rhs));
			assert_eq!(lhs.into().bvule(&rhs.into()), Ok(lhs <= rhs));
			assert_eq!(lhs.into().bvult(&rhs.into()), Ok(lhs < rhs));
		}

		fn symmetric_valid_cmp<T>(lhs: T, rhs: T)
		where
			T: Into<Bitvec> + Ord + Copy,
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
		assert_eq!(Bitvec::from(false).bvneg(), Bitvec::from(false));
		assert_eq!(Bitvec::from(true).bvneg(), Bitvec::from(true))
	}

	#[test]
	fn simple() {
		assert_eq!(Bitvec::from(42_i32).bvneg(), Bitvec::from(-42_i32));
		assert_eq!(Bitvec::from(-42_i32).bvneg(), Bitvec::from(42_i32))
	}

	#[test]
	fn zero_to_zero() {
		assert_eq!(
			Bitvec::zero(BitWidth::w32()).bvneg(),
			Bitvec::zero(BitWidth::w32())
		)
	}

	#[test]
	fn min_to_min() {
		use std::i32;
		assert_eq!(Bitvec::from(i32::MIN).bvneg(), Bitvec::from(i32::MIN))
	}

	#[test]
	fn involution() {
		assert_eq!(Bitvec::from(42_i32).bvneg().bvneg(), Bitvec::from(42_i32));
		assert_eq!(Bitvec::from(-1337_i32).bvneg().bvneg(), Bitvec::from(-1337_i32))
	}
}

mod add {
	use super::*;
	use std::ops::Add;

	fn valid_add<T>(lhs: T, rhs: T)
	where
		T: Into<Bitvec> + Add + Copy,
		Bitvec: From<<T as Add>::Output>,
	{
		assert_eq!(lhs.into().bvadd(&rhs.into()), Ok(Bitvec::from(lhs + rhs)));
	}

	fn symmetric_valid_add<T>(lhs: T, rhs: T)
	where
		T: Into<Bitvec> + Add + Copy,
		Bitvec: From<<T as Add>::Output>,
	{
		valid_add(lhs, rhs);
		valid_add(rhs, lhs)
	}

	#[test]
	fn w1() {
		assert_eq!(
			Bitvec::from(false).bvadd(&Bitvec::from(false)),
			Ok(Bitvec::from(false))
		);
		assert_eq!(
			Bitvec::from(false).bvadd(&Bitvec::from(true)),
			Ok(Bitvec::from(true))
		);
		assert_eq!(
			Bitvec::from(true).bvadd(&Bitvec::from(false)),
			Ok(Bitvec::from(true))
		);
		assert_eq!(
			Bitvec::from(true).bvadd(&Bitvec::from(true)),
			Ok(Bitvec::from(false))
		);
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
		symmetric_valid_add(42_i32, 5_i32);
		symmetric_valid_add(-42_i32, 5_i32);
		symmetric_valid_add(42_i32, -5_i32);
		symmetric_valid_add(-42_i32, -5_i32)
	}

	#[test]
	fn eq_zero() {
		symmetric_valid_add(-42_i32, 42_i32)
	}

	#[test]
	fn fail() {
		assert!(Bitvec::from(42_i32).bvadd(&Bitvec::from(1337_i64)).is_err());
	}
}

mod sub {
	use super::*;
	use std::ops::Sub;

	fn valid_sub<T>(lhs: T, rhs: T)
	where
		T: Into<Bitvec> + Sub + Copy,
		Bitvec: From<<T as Sub>::Output>,
	{
		assert_eq!(lhs.into().bvsub(&rhs.into()), Ok(Bitvec::from(lhs - rhs)));
	}

	#[test]
	fn w1() {
		assert_eq!(
			Bitvec::from(false).bvsub(&Bitvec::from(false)),
			Ok(Bitvec::from(false))
		);
		assert_eq!(
			Bitvec::from(false).bvsub(&Bitvec::from(true)),
			Ok(Bitvec::from(true))
		);
		assert_eq!(
			Bitvec::from(true).bvsub(&Bitvec::from(false)),
			Ok(Bitvec::from(true))
		);
		assert_eq!(
			Bitvec::from(true).bvsub(&Bitvec::from(true)),
			Ok(Bitvec::from(false))
		);
	}

	#[test]
	fn both_zero() {
		valid_sub(0_i32, 0_i32)
	}

	#[test]
	fn one_zero() {
		valid_sub(42_i32, 0_i32);
		valid_sub(0_i32, 42_i32);
		valid_sub(1337_i32, 0_i32);
		valid_sub(0_i32, 1337_i32);
		valid_sub(5_i32, 0_i32);
		valid_sub(0_i32, 5_i32)
	}

	#[test]
	fn pos_neg() {
		valid_sub(42_i32, 5_i32);
		valid_sub(42_i32, -5_i32);
		valid_sub(-42_i32, 5_i32);
		valid_sub(-42_i32, -5_i32)
	}

	#[test]
	fn eq_zero() {
		valid_sub(123_i32, 123_i32)
	}

	#[test]
	fn fail() {
		assert!(Bitvec::from(42_i32).bvsub(&Bitvec::from(1337_i64)).is_err());
	}
}

mod mul {
	use super::*;
	use std::ops::Mul;

	fn valid_mul<T>(lhs: T, rhs: T)
	where
		T: Into<Bitvec> + Mul + Copy,
		Bitvec: From<<T as Mul>::Output>,
	{
		assert_eq!(lhs.into().bvmul(&rhs.into()), Ok(Bitvec::from(lhs * rhs)));
	}

	fn symmetric_valid_mul<T>(lhs: T, rhs: T)
	where
		T: Into<Bitvec> + Mul + Copy,
		Bitvec: From<<T as Mul>::Output>,
	{
		valid_mul(lhs, rhs);
		valid_mul(rhs, lhs)
	}

	#[test]
	fn w1() {
		assert_eq!(
			Bitvec::from(false).bvmul(&Bitvec::from(false)),
			Ok(Bitvec::from(false))
		);
		assert_eq!(
			Bitvec::from(false).bvmul(&Bitvec::from(true)),
			Ok(Bitvec::from(false))
		);
		assert_eq!(
			Bitvec::from(true).bvmul(&Bitvec::from(false)),
			Ok(Bitvec::from(false))
		);
		assert_eq!(
			Bitvec::from(true).bvmul(&Bitvec::from(true)),
			Ok(Bitvec::from(true))
		);
	}

	#[test]
	fn both_zero() {
		valid_mul(0_i32, 0_i32)
	}

	#[test]
	fn one_zero() {
		symmetric_valid_mul(42_i32, 0_i32);
		symmetric_valid_mul(1337_i32, 0_i32);
		symmetric_valid_mul(5_i32, 0_i32);
	}

	#[test]
	fn one_one() {
		symmetric_valid_mul(42_i32, 1_i32);
		symmetric_valid_mul(1337_i32, 1_i32);
		symmetric_valid_mul(5_i32, 1_i32);
	}

	#[test]
	fn pos_neg() {
		symmetric_valid_mul(42_i32, 5_i32);
		symmetric_valid_mul(42_i32, -5_i32);
		symmetric_valid_mul(-42_i32, 5_i32);
		symmetric_valid_mul(-42_i32, -5_i32)
	}

	#[test]
	fn fail() {
		assert!(Bitvec::from(42_i32).bvmul(&Bitvec::from(1337_i64)).is_err());
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
			Bitvec: From<<T as Div>::Output>,
		{
			assert_eq!(lhs.into().bvsdiv(&rhs.into()), Ok(Bitvec::from(lhs / rhs)));
		}

		fn symmetric_valid_div<T>(lhs: T, rhs: T)
		where
			T: Into<Bitvec> + Div + Copy,
			Bitvec: From<<T as Div>::Output>,
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
			symmetric_valid_div(12_i32, -3_i32);
			symmetric_valid_div(-12_i32, 3_i32);
			symmetric_valid_div(-12_i32, -3_i32)
		}

		#[test]
		fn rhs_is_one() {
			valid_div(42_i32, 1_i32);
			valid_div(1337_i32, 1_i32);
			valid_div(5_i32, 1_i32);
			valid_div(1_i32, 1_i32);
			valid_div(0_i32, 1_i32)
		}

		#[test]
		fn lhs_is_one() {
			valid_div(1_i32, 42_i32);
			valid_div(1_i32, 1337_i32);
			valid_div(1_i32, 5_i32)
		}
	}

	mod unsigned {
		use super::*;

		fn valid_div<T>(lhs: T, rhs: T)
		where
			T: Into<Bitvec> + Div + Copy,
			Bitvec: From<<T as Div>::Output>,
		{
			assert_eq!(lhs.into().bvudiv(&rhs.into()), Ok(Bitvec::from(lhs / rhs)));
		}

		fn symmetric_valid_div<T>(lhs: T, rhs: T)
		where
			T: Into<Bitvec> + Div + Copy,
			Bitvec: From<<T as Div>::Output>,
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
			valid_div(42_i32, 1_i32);
			valid_div(1337_i32, 1_i32);
			valid_div(5_i32, 1_i32);
			valid_div(1_i32, 1_i32);
			valid_div(0_i32, 1_i32)
		}

		#[test]
		fn lhs_is_one() {
			valid_div(1_i32, 42_i32);
			valid_div(1_i32, 1337_i32);
			valid_div(1_i32, 5_i32)
		}
	}

	#[test]
	fn div_by_zero() {
		fn test_div_by_zero(lhs: i32) {
			assert!(Bitvec::from(lhs).bvsdiv(&Bitvec::from(0_i32)).is_err());
			assert!(Bitvec::from(lhs).bvudiv(&Bitvec::from(0_i32)).is_err());
		}
		test_div_by_zero(1337);
		test_div_by_zero(42);
		test_div_by_zero(5);
		test_div_by_zero(0)
	}

	#[test]
	fn fail_width() {
		assert!(Bitvec::from(42_i32).bvsdiv(&Bitvec::from(1337_i64)).is_err());
		assert!(Bitvec::from(42_i32).bvudiv(&Bitvec::from(1337_i64)).is_err());
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
			Bitvec: From<<T as Rem>::Output>,
		{
			assert_eq!(lhs.into().bvsrem(&rhs.into()), Ok(Bitvec::from(lhs % rhs)));
		}

		fn symmetric_valid_rem<T>(lhs: T, rhs: T)
		where
			T: Into<Bitvec> + Rem + Copy,
			Bitvec: From<<T as Rem>::Output>,
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
			symmetric_valid_rem(12_i32, -3_i32);
			symmetric_valid_rem(-12_i32, 3_i32);
			symmetric_valid_rem(-12_i32, -3_i32)
		}

		#[test]
		fn rhs_is_one() {
			valid_rem(42_i32, 1_i32);
			valid_rem(1337_i32, 1_i32);
			valid_rem(5_i32, 1_i32);
			valid_rem(1_i32, 1_i32);
			valid_rem(0_i32, 1_i32)
		}

		#[test]
		fn lhs_is_one() {
			valid_rem(1_i32, 42_i32);
			valid_rem(1_i32, 1337_i32);
			valid_rem(1_i32, 5_i32)
		}
	}

	mod unsigned {
		use super::*;

		fn valid_rem<T>(lhs: T, rhs: T)
		where
			T: Into<Bitvec> + Rem + Copy,
			Bitvec: From<<T as Rem>::Output>,
		{
			assert_eq!(lhs.into().bvurem(&rhs.into()), Ok(Bitvec::from(lhs % rhs)));
		}

		fn symmetric_valid_rem<T>(lhs: T, rhs: T)
		where
			T: Into<Bitvec> + Rem + Copy,
			Bitvec: From<<T as Rem>::Output>,
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
			valid_rem(42_i32, 1_i32);
			valid_rem(1337_i32, 1_i32);
			valid_rem(5_i32, 1_i32);
			valid_rem(1_i32, 1_i32);
			valid_rem(0_i32, 1_i32)
		}

		#[test]
		fn lhs_is_one() {
			valid_rem(1_i32, 42_i32);
			valid_rem(1_i32, 1337_i32);
			valid_rem(1_i32, 5_i32)
		}
	}

	#[test]
	fn div_by_zero() {
		fn test_div_by_zero(lhs: i32) {
			assert!(Bitvec::from(lhs).bvsrem(&Bitvec::from(0_i32)).is_err());
			assert!(Bitvec::from(lhs).bvurem(&Bitvec::from(0_i32)).is_err());
		}
		test_div_by_zero(1337);
		test_div_by_zero(42);
		test_div_by_zero(5);
		test_div_by_zero(0)
	}

	#[test]
	fn fail_width() {
		assert!(Bitvec::from(42_i32).bvsrem(&Bitvec::from(1337_i64)).is_err());
		assert!(Bitvec::from(42_i32).bvurem(&Bitvec::from(1337_i64)).is_err());
	}
}

mod shl {
	use super::*;

	#[test]
	fn simple() {
		assert_eq!(
			Bitvec::from(0x_ABCD_9876_u32).bvshl(16),
			Ok(Bitvec::from(0x_9876_0000_u32))
		)
	}

	#[test]
	fn from_1_to_2() {
		assert_eq!(Bitvec::from(1u16).bvshl(1), Ok(Bitvec::from(2u16)))
	}

	#[test]
	fn shift_by_zero() {
		assert_eq!(Bitvec::from(42_u32).bvshl(0), Ok(Bitvec::from(42_u32)))
	}

	#[test]
	fn shift_overflow() {
		assert!(Bitvec::from(1337_u32).bvshl(32).is_err());
		assert!(Bitvec::from(1337_u32).bvshl(1337).is_err())
	}

	#[test]
	fn shift_near_overflow() {
		assert_eq!(
			Bitvec::from(1_u32).bvshl(31),
			Ok(Bitvec::from(0x8000_0000_u32))
		)
	}
}

mod ashr {
	use super::*;

	#[test]
	fn pos_simple() {
		assert_eq!(
			Bitvec::from(0x_0123_4567_u32).bvashr(16),
			Ok(Bitvec::from(0x_0000_0123_u32))
		)
	}

	#[test]
	fn neg_simple() {
		assert_eq!(
			Bitvec::from(0x_FEDC_BA98_u32).bvashr(16),
			Ok(Bitvec::from(0x_FFFF_FEDC_u32))
		)
	}

	#[test]
	fn shift_by_zero() {
		assert_eq!(Bitvec::from(42_u32).bvashr(0), Ok(Bitvec::from(42_u32)))
	}

	#[test]
	fn shift_overflow() {
		assert!(Bitvec::from(1337_u32).bvashr(32).is_err());
		assert!(Bitvec::from(1337_u32).bvashr(1337).is_err())
	}

	#[test]
	fn neg_shift_near_overflow() {
		assert_eq!(
			Bitvec::from(0x8000_0000_u32).bvashr(31),
			Ok(Bitvec::from(0x_FFFF_FFFF_u32))
		)
	}

	#[test]
	fn pos_shift_near_overflow() {
		assert_eq!(
			Bitvec::from(0x7FFF_FFFF_u32).bvashr(30),
			Ok(Bitvec::from(1_u32))
		)
	}
}

mod lshr {
	use super::*;

	#[test]
	fn simple() {
		assert_eq!(
			Bitvec::from(0x_FEDC_BA98_u32).bvlshr(16),
			Ok(Bitvec::from(0x_0000_FEDC_u32))
		)
	}

	#[test]
	fn shift_by_zero() {
		assert_eq!(Bitvec::from(42_u32).bvlshr(0), Ok(Bitvec::from(42_u32)))
	}

	#[test]
	fn shift_overflow() {
		assert!(Bitvec::from(1337_u32).bvlshr(32).is_err());
		assert!(Bitvec::from(1337_u32).bvlshr(1337).is_err())
	}

	#[test]
	fn shift_near_overflow() {
		assert_eq!(
			Bitvec::from(0x8000_0000_u32).bvlshr(31),
			Ok(Bitvec::from(0x_0000_0001_u32))
		)
	}
}

mod zext {
	use super::*;

	#[test]
	fn from_1_to_32() {
		assert_eq!(
			Bitvec::from(false).zero_extend(BitWidth::w32()),
			Ok(Bitvec::from(0_u32))
		);
		assert_eq!(
			Bitvec::from(true).zero_extend(BitWidth::w32()),
			Ok(Bitvec::from(1_u32))
		)
	}

	#[test]
	fn from_16_to_32() {
		assert_eq!(
			Bitvec::from(0x_ABCD_u16).zero_extend(BitWidth::w32()),
			Ok(Bitvec::from(0x_ABCD_u32))
		)
	}

	#[test]
	fn eq_width() {
		assert_eq!(
			Bitvec::from(0x_0123_u16).zero_extend(BitWidth::w16()),
			Ok(Bitvec::from(0x_0123_u16))
		)
	}

	#[test]
	fn neg16_to_32() {
		assert_eq!(
			Bitvec::from(0x_8042_u16).zero_extend(BitWidth::w32()),
			Ok(Bitvec::from(0x_8042_u32))
		)
	}

	#[test]
	fn invalid_target_width() {
		assert!(Bitvec::from(42_u16).zero_extend(BitWidth::from(15)).is_err());
		assert!(Bitvec::from(42_u32).zero_extend(BitWidth::w16()).is_err())
	}
}

mod sext {
	use super::*;

	#[test]
	fn from_1_to_32() {
		assert_eq!(
			Bitvec::from(false).sign_extend(BitWidth::w32()),
			Ok(Bitvec::from(0_u32))
		);
		assert_eq!(
			Bitvec::from(true).sign_extend(BitWidth::w32()),
			Ok(Bitvec::from(0x_FFFF_FFFF_u32))
		)
	}

	#[test]
	fn from_16_to_32() {
		assert_eq!(
			Bitvec::from(0x_0123_u16).sign_extend(BitWidth::w32()),
			Ok(Bitvec::from(0x_0123_u32))
		)
	}

	#[test]
	fn eq_width() {
		assert_eq!(
			Bitvec::from(0x_ABCD_u16).sign_extend(BitWidth::w16()),
			Ok(Bitvec::from(0x_ABCD_u16))
		)
	}

	#[test]
	fn neg16_to_32() {
		assert_eq!(
			Bitvec::from(0x_8042_u16).sign_extend(BitWidth::w32()),
			Ok(Bitvec::from(0x_FFFF_8042_u32))
		)
	}

	#[test]
	fn invalid_target_width() {
		assert!(Bitvec::from(42_u16).sign_extend(BitWidth::from(15)).is_err());
		assert!(Bitvec::from(42_u32).sign_extend(BitWidth::w16()).is_err())
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
	fn err_eq_lo_hi() {
		assert!(Bitvec::from(1337_u16).extract(1, 1).is_err())
	}

	#[test]
	fn err_lo_lt_hi() {
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
