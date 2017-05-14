/// Represents a bitvector.
/// 
/// This is an initial dummy implementation.
/// A real, general and efficient implementation will replace this
/// dummy implementation in a future version of this crate.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitVec {
	value: u64
}

impl BitVec {
	pub fn to_u64(&self) -> u64 {
		self.value
	}
}

impl From<u64> for BitVec {
	fn from(val: u64) -> BitVec {
		BitVec{ value: val }
	}
}

use std::hash::Hash;

trait IBitVec: Hash + Clone {
	type Concrete: IBitVec;

	/// Creates a bitvector with `bits` bits that are all set to `0`.
	fn zeroes(bits: usize) -> Self::Concrete;

	/// Creates a bitvector with `bits` bits that are all set to `1`.
	fn ones(bits: usize) -> Self::Concrete;

	/// Unsigned less-than comparison with the other bitvec.
	fn ult(&self, other: &BitVec) -> bool;
	/// Unsigned less-than-or-equals comparison with the other bitvec.
	fn ule(&self, other: &BitVec) -> bool;
	/// Unsigned greater-than comparison with the other bitvec.
	fn ugt(&self, other: &BitVec) -> bool;
	/// Unsigned greater-than-or-equals comparison with the other bitvec.
	fn uge(&self, other: &BitVec) -> bool;

	/// Signed less-than comparison with the other bitvec.
	fn slt(&self, other: &BitVec) -> bool;
	/// Signed less-than-or-equals comparison with the other bitvec.
	fn sle(&self, other: &BitVec) -> bool;
	/// Signed greater-than comparison with the other bitvec.
	fn sgt(&self, other: &BitVec) -> bool;
	/// Signed greater-than-or-equals comparison with the other bitvec.
	fn sge(&self, other: &BitVec) -> bool;
}
