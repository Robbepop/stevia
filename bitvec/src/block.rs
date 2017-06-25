use std::fmt;
use std::hash::{Hash, Hasher};

/// The number of bits of a single block.
pub const BLOCK_SIZE: usize = 32;

#[derive(Copy, Clone, Eq)]
pub union Block {
	pub u: u32,
	pub s: i32
}

impl fmt::Debug for Block {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		Ok(()) // TODO
	}
}

impl PartialEq for Block {
	fn eq(&self, other: &Block) -> bool {
		(unsafe{self.u} < unsafe{other.u})
	}
}

impl Hash for Block {
	fn hash<H: Hasher>(&self, h: &mut H) {
		unsafe{self.u.hash(h)}
	}
}
