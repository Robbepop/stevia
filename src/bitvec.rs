
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
