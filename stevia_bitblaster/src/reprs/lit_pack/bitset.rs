/// The internal representation of a bit block.
type BitBlockRepr = u64;

/// A bit block.
///
/// Every bit block contains a fixed number of bits.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BitBlock {
	/// The underlying bits.
	bits: BitBlockRepr,
}

// impl core::fmt::Binary for BitBlock {
// 	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
// 		write!(f, "{:b}", self.bits)
// 	}
// }

impl BitBlock {
	/// The bits stored of a bit block.
	pub const BITS: usize = core::mem::size_of::<BitBlockRepr>() * 8;

	/// Returns a bit block with all bits set to `0`.
	pub fn zeros() -> Self {
		Self{ bits: 0x0 }
	}

	/// Returns a bit block with all bits set to `1`.
	pub fn ones() -> Self {
		Self{ bits: core::u64::MAX }
	}

	/// Returns the n-th bit.
	///
	/// # Panics
	///
	/// If `n` is out of bounds.
	pub fn get(self, n: usize) -> bool {
		assert!(n < Self::BITS);
		self.bits & (0x1 << (Self::BITS - n)) != 0
	}

	/// Sets the n-th bit to the given value.
	///
	/// # Panics
	///
	/// If `n` is out of bounds.
	pub fn set(&mut self, n: usize, val: bool) {
		assert!(n < Self::BITS);
		if val {
			self.bits |= 0x1 << (Self::BITS - n)
		} else {
			self.bits &= !(0x1 << (Self::BITS - n))
		}
	}

	/// Sets all bits to the given value.
	pub fn set_all(&mut self, val: bool) {
		if val {
			self.bits = core::u64::MAX;
		} else {
			self.bits = 0x0;
		}
	}

	/// Flips the n-th bit.
	///
	/// # Panics
	///
	/// If `n` is out of bounds.
	pub fn flip(&mut self, n: usize) {
		assert!(n < Self::BITS);
		self.bits ^= 0x1 << (Self::BITS - n);
	}

	/// Flips all bits.
	pub fn flip_all(&mut self) {
		self.bits ^= core::u64::MAX;
	}
}

/// The kind of the bit pack error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BitPackErrorKind {
	/// Encountered when trying to create a bit pack with zero length.
	ZeroLengthBitPack,
	/// Encountered upon out of bounds access.
	AccessOutOfBounds{
		/// The index of the out of bounds access.
		access_at: usize,
		/// The actual length of the bit pack.
		len: usize,
	},
}

/// An error encountered upon operating on bit packs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitPackError {
	/// The kind of the bit pack error.
	kind: BitPackErrorKind,
}

impl BitPackError {
	/// Returns the kind of the error.
	pub fn kind(&self) -> &BitPackErrorKind {
		&self.kind
	}

	/// Creates a new error indicating a zero length bit pack creation.
	pub fn zero_length_bit_pack() -> Self {
		Self {
			kind: BitPackErrorKind::ZeroLengthBitPack,
		}
	}

	/// Creates a new error indicating an out of bounds access.
	pub fn access_out_of_bounds(access_at: usize, len: usize) -> Self {
		Self {
			kind: BitPackErrorKind::AccessOutOfBounds{
				access_at,
				len,
			}
		}
	}
}

impl core::fmt::Display for BitPackError {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		match self.kind() {
			BitPackErrorKind::ZeroLengthBitPack => {
				write!(f, "tried to create a bit pack with zero length")
			}
			BitPackErrorKind::AccessOutOfBounds{access_at, len} => {
				write!(f,
					"encountered invalid access at (= {:?}) bit pack of length (= {:?})",
					access_at,
					len,
				)
			}
		}
	}
}

/// Result type for bit pack errors.
type Result<T> = core::result::Result<T, BitPackError>;

/// A space optimized pack of bits.
///
/// # Note
///
/// To make it waste less space instances of this type are required
/// to have their length managed by an external entity.
/// Upon usage they can be promoted to a bit pack given a length.
pub union ExternalBitPack {
	/// An inline sign pack for small sign packs.
	inl: BitBlock,
	/// An external sign pack with arbitrary length.
	ext: core::ptr::NonNull<BitBlock>,
}

impl ExternalBitPack {
	/// The maximum length that can be used to store bits inline.
	///
	/// # Note
	///
	/// Inline memory means that no heap has to be allocated for it.
	const INLINE_LEN: usize = BitBlock::BITS;

	/// Returns `true` if the given length fits the inline space.
	fn fits_inline(len: usize) -> bool {
		len <= Self::INLINE_LEN
	}

	/// Creates a new external bit pack.
	///
	/// # Panics
	///
	/// If `len` is zero.
	///
	/// # Safety
	///
	/// A sign pack does not store its own length.
	/// Instead it relies on the outside to properly manage it.
	/// This is done to prevent redundant length fields.
	pub fn new(len: usize, init_val: bool) -> Result<Self> {
		if len == 0 {
			return Err(BitPackError::zero_length_bit_pack())
		}
		let block_mask = if init_val {
			BitBlock::ones()
		} else {
			BitBlock::zeros()
		};
		if Self::fits_inline(len) {
			Ok(Self { inl: block_mask })
		} else {
			let buffer_ptr = {
				let req_blocks = 1 + (len / BitBlock::BITS);
				let mut buffer = vec![block_mask; req_blocks].into_boxed_slice();
				let ptr = buffer.as_mut_ptr();
				Box::leak(buffer);
				ptr
			};
			Ok(Self { ext: unsafe { core::ptr::NonNull::new_unchecked(buffer_ptr) } })
		}
	}

	/// Returns the block offset and index within a bit block for a given bit index.
	fn block_idx_local_idx(bit_idx: usize) -> (usize, usize) {
		if bit_idx == 0 {
			(0, 0)
		} else {
			let block_idx = (bit_idx - 1) / BitBlock::BITS;
			let block_bit = (bit_idx - 1) % BitBlock::BITS;
			(block_idx, block_bit)
		}
	}

	/// Returns the underlying bit blocks as immutable slice.
	///
	/// # Safety
	///
	/// This relies on the given length to be the exact same as
	/// when constructing the external bit pack.
	unsafe fn block_slice(&self, len: usize) -> &[BitBlock] {
		debug_assert!(len > 0);
		if Self::fits_inline(len) {
			core::slice::from_raw_parts(&self.inl, 1)
		} else {
			let req_chunks = 1 + ((len - 1) / BitBlock::BITS);
			core::slice::from_raw_parts(self.ext.as_ptr(), req_chunks)
		}
	}

	/// Returns the underlying bit blocks as mutable slice.
	///
	/// # Safety
	///
	/// This relies on the given length to be the exact same as
	/// when constructing the external bit pack.
	unsafe fn block_slice_mut(&mut self, len: usize) -> &mut [BitBlock] {
		debug_assert!(len > 0);
		if Self::fits_inline(len) {
			core::slice::from_raw_parts_mut(&mut self.inl, 1)
		} else {
			let req_chunks = 1 + ((len - 1) / BitBlock::BITS);
			core::slice::from_raw_parts_mut(self.ext.as_ptr(), req_chunks)
		}
	}

	/// Promotes `self` to an immutable bit pack with length information.
	///
	/// # Safety
	///
	/// This relies on the given length to be the exact same as
	/// when constructing the external bit pack.
	pub unsafe fn promote(&self, len: usize) -> PromotedBitPack {
		PromotedBitPack::new(len, self.block_slice(len))
	}

	/// Promotes `self` to a mutable bit pack with length information.
	///
	/// # Safety
	///
	/// This relies on the given length to be the exact same as
	/// when constructing the external bit pack.
	pub unsafe fn promote_mut(&mut self, len: usize) -> PromotedBitPackMut {
		PromotedBitPackMut::new(len, self.block_slice_mut(len))
	}

	/// Deallocates potential allocations of `self`.
	///
	/// # Panics
	///
	/// If `len` is zero.
	///
	/// # Safety
	///
	/// This relies on the given length to be the exact same as
	/// when constructing the external bit pack.
	pub unsafe fn unalloc(&mut self, len: usize) {
		assert!(len > 0);
		if !Self::fits_inline(len) {
			core::mem::drop(
				Vec::from_raw_parts(self.ext.as_ptr(), len, len)
			)
		}
	}
}

/// A promoted immutable bit pack that has a length information.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct PromotedBitPack<'a> {
	/// The length in bits of the bit pack.
	len: usize,
	/// The actual bits organized in blocks.
	blocks: &'a [BitBlock],
}

impl<'a> PromotedBitPack<'a> {
	/// Returns a promoted bit pack from the given length and bits.
	pub fn new(len: usize, blocks: &'a [BitBlock]) -> Self {
		Self { len, blocks }
	}

	/// Returns the value of the n-th bit.
	pub fn get(&self, n: usize) -> Result<bool> {
		if n >= self.len {
			return Err(BitPackError::access_out_of_bounds(n, self.len))
		}
		let (block_idx, block_bit) = ExternalBitPack::block_idx_local_idx(n);
		Ok(self.blocks[block_idx].get(block_bit))
	}

	/// Returns the value of the n-th bit.
	///
	/// # Safety
	///
	/// This does not check for valid bounds.
	pub fn get_unchecked(&self, n: usize) -> bool {
		debug_assert!(n < self.len);
		let (block_idx, block_bit) = ExternalBitPack::block_idx_local_idx(n);
		debug_assert!(block_bit < BitBlock::BITS);
		self.blocks[block_idx]
			.get(block_bit)
	}
}

/// A promoted mutable bit pack that has a length information.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct PromotedBitPackMut<'a> {
	/// The length in bits of the bit pack.
	len: usize,
	/// The actual bits organized in blocks.
	blocks: &'a mut [BitBlock],
}

impl<'a> PromotedBitPackMut<'a> {
	/// Returns a promoted bit pack from the given length and bits.
	pub fn new(len: usize, blocks: &'a mut [BitBlock]) -> Self {
		Self { len, blocks }
	}

	/// Returns the `index` if it in bounds for `self` and otherwise returns an error.
	fn block_idx_local_idx(&self, index: usize) -> Result<(usize, usize)> {
		if index >= self.len {
			return Err(BitPackError::access_out_of_bounds(index, self.len))
		}
		Ok(ExternalBitPack::block_idx_local_idx(index))
	}

	/// Sets the n-th bit to the given value.
	pub fn set(&mut self, n: usize, val: bool) -> Result<()> {
		self.block_idx_local_idx(n)
			.map(|(block_idx, local_idx)| {
				self.blocks[block_idx].set(local_idx, val)
			})
	}

	/// Flips the value of the n-th bit.
	pub fn flip(&mut self, n: usize) -> Result<()> {
		self.block_idx_local_idx(n)
			.map(|(block_idx, local_idx)| {
				self.blocks[block_idx].flip(local_idx)
			})
	}

	/// Sets all bits to the given value.
	pub fn set_all(&mut self, val: bool) {
		for block in self.blocks.iter_mut() {
			block.set_all(val)
		}
	}

	/// Flips all bits.
	pub fn flip_all(&mut self) {
		for block in self.blocks.iter_mut() {
			block.flip_all()
		}
	}

	/// Copies the bits from the other promoted bit pack.
	pub fn copy_from(&mut self, other: PromotedBitPack) {
		self.blocks.copy_from_slice(other.blocks)
	}
}
