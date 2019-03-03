use crate::reprs::Sign;
use super::{
	Error,
	ErrorKind,
	Result,
};

/// The internal representation of a sign chunk.
type SignChunkRepr = u64;

/// A sign chunk.
///
/// Every sign chunk contains a fixed number of signs.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SignChunk {
	/// The underlying bits.
	bits: SignChunkRepr,
}

impl core::fmt::Binary for SignChunk {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		write!(f, "{:b}", self.bits)
	}
}

impl SignChunk {
	/// The bits stored in a sign chunk.
	pub const BITS: usize = core::mem::size_of::<SignChunkRepr>() * 8;

	/// Returns a sign chunk with only negative signs.
	pub fn all_neg() -> Self {
		SignChunk{ bits: 0x0 }
	}

	/// Returns a sign chunk with only positive signs.
	pub fn all_pos() -> Self {
		SignChunk{ bits: core::u64::MAX }
	}

	/// Returns the n-th sign.
	///
	/// # Panics
	///
	/// If `n` is out of bounds.
	pub fn get(&self, n: usize) -> Sign {
		assert!(n < Self::BITS);

		let bit = self.bits & (0x1 << (Self::BITS - n));
		if bit == 0 {
			Sign::Neg
		} else {
			Sign::Pos
		}
	}

	/// Sets the n-th sign to the given value.
	///
	/// # Panics
	///
	/// If `n` is out of bounds.
	pub fn set(&mut self, n: usize, sign: Sign) {
		assert!(n < Self::BITS);

		match sign {
			Sign::Pos => {
				self.bits |= 0x1 << (Self::BITS - n);
			}
			Sign::Neg => {
				self.bits &= !(0x1 << (Self::BITS - n));
			}
		}
	}

	/// Sets all signs to the given sign.
	pub fn set_all(&mut self, sign: Sign) {
		match sign {
			Sign::Pos => {
				self.bits = core::u64::MAX;
			}
			Sign::Neg => {
				self.bits = 0x0;
			}
		}
	}

	/// Flips the n-th sign.
	///
	/// # Panics
	///
	/// If `n` is out of bounds.
	pub fn flip(&mut self, n: usize) {
		assert!(n < Self::BITS);

		self.bits ^= 0x1 << (Self::BITS - n);
	}

	/// Flips all signs.
	pub fn flip_all(&mut self) {
		self.bits ^= core::u64::MAX;
	}
}

/// A pack of literal signs.
pub union SignPack {
	/// An inline sign pack for small sign packs.
	inl: SignChunk,
	/// An external sign pack with arbitrary length.
	ext: core::ptr::NonNull<SignChunk>,
}

impl SignPack {
	/// The maximum length that can be used to store signs inline.
	///
	/// # Note
	///
	/// Inline memory means that no heap has to be allocated for it.
	const INLINE_LEN: usize = SignChunk::BITS;

	/// Allocates a new sign pack.
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
	pub unsafe fn new(len: usize, sign: Sign) -> Self {
		debug_assert!(len > 0);

		let sign_mask = match sign {
			Sign::Pos => SignChunk::all_pos(),
			Sign::Neg => SignChunk::all_neg(),
		};
		if len <= Self::INLINE_LEN {
			Self { inl: sign_mask }
		} else {
			let buffer_ptr = {
				let req_chunks = 1 + (len / SignChunk::BITS);
				let mut buffer = vec![sign_mask; req_chunks].into_boxed_slice();
				let ptr = buffer.as_mut_ptr();
				Box::leak(buffer);
				ptr
			};
			Self { ext: core::ptr::NonNull::new_unchecked(buffer_ptr) }
		}
	}

	/// Returns the chunk offset and index within chunk for a given sign index.
	pub(crate) fn chunk_idx_local_idx(n: usize) -> (usize, usize) {
		if n == 0 {
			(0, 0)
		} else {
			let chunk_idx = (n - 1) / SignChunk::BITS;
			let chunk_bit = (n - 1) % SignChunk::BITS;
			(chunk_idx, chunk_bit)
		}
	}

	/// Returns an immutable sign chunks slice.
	///
	/// # Safety
	///
	/// The given length must be the same as when constructing the sign pack.
	pub(crate) unsafe fn as_chunk_slice(&self, len: usize) -> &[SignChunk] {
		debug_assert!(len > 0);

		if len <= Self::INLINE_LEN {
			core::slice::from_raw_parts(&self.inl, 1)
		} else {
			let req_chunks = 1 + ((len - 1) / SignChunk::BITS);
			core::slice::from_raw_parts(self.ext.as_ptr(), req_chunks)
		}
	}

	/// Returns a mutable sign chunk slice.
	///
	/// # Safety
	///
	/// The given length must be the same as when constructing the sign pack.
	pub(crate) unsafe fn as_chunk_slice_mut(&mut self, len: usize) -> &mut [SignChunk] {
		debug_assert!(len > 0);

		if len <= Self::INLINE_LEN {
			core::slice::from_raw_parts_mut(&mut self.inl, 1)
		} else {
			let req_chunks = 1 + ((len - 1) / SignChunk::BITS);
			core::slice::from_raw_parts_mut(self.ext.as_ptr(), req_chunks)
		}
	}

	/// Deallocates potential allocations of `self`.
	///
	/// # Panics
	///
	/// If `len` is zero.
	///
	/// # Safety
	///
	/// Has to be called with the `len` with which it has been allocated.
	pub unsafe fn unalloc(self, len: usize) {
		debug_assert!(len > 0);

		if len > Self::INLINE_LEN {
			core::mem::drop(
				Vec::from_raw_parts(self.ext.as_ptr(), len, len)
			)
		}
	}
}
