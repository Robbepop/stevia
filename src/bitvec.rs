
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitVec {
	value: u64
}

impl BitVec {
	pub fn width(&self) -> usize {
		self.value as usize
	}
}
