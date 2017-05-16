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
