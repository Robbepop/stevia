use items::{
	Block,
	BITS_PER_BLOCK
};

use std::ptr::Unique;

/// A const-iterator over the `Block`s of a `FlexInt`.
pub struct Blocks<'a> {
	/// Total amount of bits to iterate over in blocks.
	bits  : usize,
	/// Current amount of bits that have been iterated over already in blocks.
	cur   : usize,
	/// Immutable view of the block slice to iterate over.
	blocks: &'a [Block]
}

/// A mutable-iterator over the `Block`s of a `FlexInt`.
pub struct BlocksMut<'a> {
	/// Total amount of bits to iterate over in blocks.
	bits  : usize,
	/// Current amount of bits that have been iterated over already in blocks.
	cur   : usize,
	/// Mutable view of the block slice to iterate over.
	blocks: &'a mut [Block]
}

/// A move-iterator over the `Block`s of a `FlexInt`.
pub struct IntoBlocks {
	/// Total amount of bits to iterate over in blocks.
	bits  : usize,
	/// Current amount of bits that have been iterated over already in blocks.
	cur   : usize,
	/// Unique pointer to the owned slice containing the blocks to iterate over.
	blocks: Unique<Block>
}

/// A `Block` wrapper adding a bit-width restriction and some operational methods.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ComputeBlock {
	/// The bit-width of the valid data within the compute block data.
	bits: usize,
	/// The wrapped block and actual data.
	data: Block
}

/// A mutable reference `Block` wrapper adding a bit-width restriction and some operational methods.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct ComputeBlockMut<'a> {
	/// The bit-width of the valid data within the compute block data.
	bits: usize,
	/// The wrapped block and actual data.
	data: &'a mut Block
}

impl<'a> Blocks<'a> {
	pub(crate) fn new<'b>(bits: usize, blocks: &'b [Block]) -> Blocks<'b> {
		Blocks{bits, cur: 0, blocks}
	}
}

impl<'a> BlocksMut<'a> {
	pub(crate) fn new<'b>(bits: usize, blocks: &'b mut [Block]) -> BlocksMut<'b> {
		BlocksMut{bits, cur: 0, blocks}
	}
}

impl IntoBlocks {
	pub(crate) fn new(bits: usize, blocks: Unique<Block>) -> IntoBlocks {
		IntoBlocks{bits, cur: 0, blocks}
	}
}

impl<'a> Blocks<'a> {
	/// Returns the bit-width of this `FixInt` as `usize`.
	#[inline]
	pub fn len_bits(&self) -> usize {
		self.bits
	}

	/// Returns the number of bit-blocks used internally for value representation.
	/// 
	/// # Note
	/// 
	/// - This method should not be part of the public interface.
	/// - The returned values are valid for bit-block sizes of 32 bit.
	#[inline]
	fn len_blocks(&self) -> usize {
		((self.len_bits() - 1) / BITS_PER_BLOCK) + 1
	}
}

impl<'a> Iterator for Blocks<'a> {
	type Item = ComputeBlock;

	fn next(&mut self) -> Option<Self::Item> {
		if self.cur >= self.bits { return None; }
		use std::cmp;
		let next_bw    = cmp::max(self.bits - (self.cur * BITS_PER_BLOCK), BITS_PER_BLOCK);
		let next_block = self.blocks[self.cur];
		self.cur += 1;
		Some(ComputeBlock{bits: next_bw, data: next_block})
	}
}

impl<'a> Iterator for BlocksMut<'a> {
	type Item = ComputeBlockMut<'a>;

	fn next(&mut self) -> Option<Self::Item> {
		unimplemented!()
	}
}

impl<'a> Iterator for IntoBlocks {
	type Item = ComputeBlock;

	fn next(&mut self) -> Option<Self::Item> {
		unimplemented!()
	}
}
