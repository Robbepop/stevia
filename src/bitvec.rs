
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitVec {
	value: u64
}

impl BitVec {
	pub fn width(&self) -> usize {
		self.value as usize
	}

	pub fn to_u64(&self) -> u64 {
		self.value
	}
}
