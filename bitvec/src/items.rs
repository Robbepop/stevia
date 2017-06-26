
use std::ptr::Unique;

pub struct FixInt {
	pub(crate) bits: u32,
	pub(crate) data: FixIntData
}

pub(crate) union FixIntData {
	pub inl: Block,
	pub ext: Unique<Block>
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Block(pub u64);

#[derive(Debug, Copy, Clone)]
pub(crate) struct BlockChain<'a>(&'a [Block]);

#[derive(Debug)]
pub(crate) struct BlockChainMut<'a>(&'a mut [Block]);

#[derive(Debug, Copy, Clone)]
pub(crate) enum FixIntModel<'a> {
	C8(u8),
	C16(u16),
	C32(u32),
	C64(u64),
	Var(BlockChain<'a>)
}

#[derive(Debug)]
pub(crate) enum FixIntModelMut<'a> {
	C8(&'a mut u64),
	C16(&'a mut u64),
	C32(&'a mut u64),
	C64(&'a mut u64),
	Var(BlockChainMut<'a>)
}

pub(crate) const BITS_PER_BLOCK: usize = 64;
pub(crate) const INLINED_BITS: usize = 64;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Storage {
	/// Indicating on stack and inplace memory usage.
	Inl,
	/// Indicating on heap and external memory usage.
	Ext
}
