use super::{
	Error,
	Result,
	ExternalBitPack,
	PromotedBitPack,
	PromotedBitPackMut,
};
use crate::reprs::{
	Sign,
	Var,
	Lit,
};

/// Represents a contiguous pack of literals.
///
/// # Note
///
/// This is just a more efficient way to relate to a bunch of
/// related variables.
pub struct LitPack {
    /// The identifier of the lowest-value variable in `self`.
    off: u32,
    /// The number of variables in `self`.
    len: u32,
    /// Sign of the represented literals when accessed.
    signs: ExternalBitPack,
}

impl Drop for LitPack {
	fn drop(&mut self) {
		let len = self.len();
		unsafe { self.signs.promote_mut(len).unalloc() }
	}
}

impl core::fmt::Debug for LitPack {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {

		f.debug_struct("LitPack")
			.field("off", &self.off)
			.field("len", &self.len)
			.field("signs", &self.signs())
			.finish()
	}
}

impl Clone for LitPack {
	fn clone(&self) -> Self {
		let mut lp = Self {
			off: self.off,
			len: self.len,
			signs: {
				ExternalBitPack::new(self.len(), true)
					.expect(
						"we already verified that creating an external
						was valid upon creating self; qed"
					)
			},
		};
		lp.signs_mut().copy_from(self.signs());
		lp
	}
}

impl PartialEq for LitPack {
	fn eq(&self, other: &Self) -> bool {
		self.off == other.off
			&& self.len() == other.len()
			&& self.signs() == other.signs()
	}
}

impl Eq for LitPack {}

impl core::hash::Hash for LitPack {
	fn hash<H>(&self, hasher: &mut H)
	where
		H: core::hash::Hasher,
	{
		self.off.hash(hasher);
		self.len.hash(hasher);
		self.signs().hash(hasher);
	}
}

impl LitPack {
    /// Creates a new literal pack with the given length
	/// starting at the given variable offset.
	/// 
	/// # Note
	///
	/// All literals have the given sign.
	///
	/// # Errors
	///
	/// - If `offset` is 0.
	/// - If `len` is 0.
	/// - If `offset + len` is out of variable bounds.
    pub fn new(offset: u32, len: u32) -> Result<LitPack> {
        if offset == 0 {
			return Err(Error::invalid_zero_offset())
        }
        if len == 0 {
			return Err(Error::invalid_lit_pack_len(len as usize))
        }
        if offset + len > Var::MAX.to_u32() {
			return Err(Error::out_of_bounds_alloc(offset as usize, len as usize))
        }
        Ok(Self {
            off: offset,
            len,
            signs: ExternalBitPack::new(len as usize, true)?
        })
    }

	/// Returns an immutable promoted bit pack representing the signs as bits.
	fn signs(&self) -> PromotedBitPack {
		unsafe { self.signs.promote(self.len()) }
	}

	/// Returns a mutable promoted bit pack representing the signs as bits.
	fn signs_mut(&mut self) -> PromotedBitPackMut {
		let len = self.len();
		unsafe { self.signs.promote_mut(len) }
	}

	/// Returns the sign of the n-th literal.
	///
	/// # Errors
	///
	/// If `n` is out of bounds.
	fn sign_at(&self, n: usize) -> Result<Sign> {
		self.signs()
			.get(n)
			.map(|val| {
				if val {
					Sign::Pos
				} else {
					Sign::Neg
				}
			})
			.map_err(From::from)
	}

	/// Returns the sign of the n-th literal.
	///
	/// # Safety
	///
	/// Does not check if `n` is out of bounds.
	unsafe fn sign_at_unchecked(&self, n: usize) -> Sign {
		if self.signs().get_unchecked(n) {
			Sign::Pos
		} else {
			Sign::Neg
		}
	}

	/// Returs the n-th variable.
	///
	/// # Errors
	///
	/// If `n` is out of bounds.
	fn var_at(&self, n: usize) -> Result<Var> {
		if n >= self.len() {
			return Err(Error::out_of_bounds_access(n, self.len()))
		}
		Ok(Var::new(self.off + n as u32)
			.expect(
				"since offset of a literal pack can never be 0
				no zero variable could ever be created"))
	}

	/// Returs the n-th variable.
	///
	/// # Safety
	///
	/// Does not check if `n` is out of bounds.
	unsafe fn var_at_unchecked(&self, n: usize) -> Var {
		Var::new_unchecked(self.off + n as u32)
	}

    /// CFlips the sign of all literals.
    pub fn flip_all(&mut self) {
		self.signs_mut().flip_all()
    }

	/// Flips the sign of the n-th literal.
	///
	/// # Errors
	///
	/// If `n` is out of bounds.
	pub fn flip_at(&mut self, n: usize) -> Result<()> {
		self.signs_mut()
			.flip(n)
			.map_err(From::from)
	}

    /// Returns the n-th literal.
	///
    /// # Errors
    ///
    /// If `n` is out of bounds.
    pub fn get(&self, n: usize) -> Result<Lit> {
		let var = self.var_at(n)?;
		let sign = self.sign_at(n)?;
		Ok(Lit::new(var, sign))
    }

	/// Returns the n-th literal.
    ///
    /// # Safety
    ///
    /// This does not check if `n` is out of bounds.
    pub unsafe fn get_unchecked(&self, n: usize) -> Lit {
        debug_assert!(n < self.len());
		Lit::new(
			self.var_at_unchecked(n),
			self.sign_at_unchecked(n)
		)
    }

    /// Returns the length (number of represented variables) of `self`.
    pub fn len(&self) -> usize {
        self.len as usize
    }

	/// Splits the literal pack at the given offset returning
	/// a left hand-side and right hand-side literal pack.
	///
	/// # Note
	///
	/// The left hand-side contains all literals in the range of `[0..mid]`
	/// (excluding mid) and the right hand-side contains all literals in the
	/// range of `[mid..self.len())`
	///
	/// # Errors
	///
	/// If `mid` is 0 or if mid exceeds the length of the literal pack.
    pub fn split(&self, mid: usize) -> Result<(LitPack, LitPack)> {
        if mid == 0 || mid >= self.len() {
			return Err(Error::invalid_split_position(mid, self.len()))
        }
        let mid = mid as u32; // Safe to cast at this point!
		let mut lhs = LitPack::new(self.off, mid)?;
		let mut rhs = LitPack::new(self.off + mid, self.len - mid)?;
		// Sets the original literal signs of lhs.
		// Note: This operation could be optimized
		//       by operating on chunks instead of
		//       single signs (bits).
		for i in 0..(mid as usize) {
			if self.sign_at(i)? == Sign::Neg {
				lhs.flip_at(i)?;
			}
		}
		// Sets the original literal signs of rhs.
		// Note: This operation could be optimized
		//       by operating on chunks instead of
		//       single signs (bits).
		for i in (mid as usize)..self.len() {
			if self.sign_at(i)? == Sign::Neg {
				rhs.flip_at(i)?;
			}
		}
        Ok((lhs, rhs))
    }

	/// Returns an iterator over the literals of `self`.
	pub fn iter(&self) -> LitPackIter {
		LitPackIter::new(self)
	}
}

impl<'a> FnOnce<(usize,)> for &'a LitPack {
    type Output = Lit;

    extern "rust-call" fn call_once(self, idx: (usize,)) -> Self::Output {
        unsafe { self.get_unchecked(idx.0) }
    }
}

impl<'a> IntoIterator for &'a LitPack {
    type Item = Lit;
    type IntoIter = LitPackIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        LitPackIter::new(self)
    }
}

/// An iterator through a pack of variables.
//
// # Dev Note
//
// This data structure could benefit greatly from packing bits.
// We do not really need the `lit_pack` here. Instead we could
// directly compute the `begin` and `end` variables upon
// construction and simply use them as raw literal identifiers
// instead of as offsets into the `lit_pack`.
//
// Without testing and benchmarking this however is premature
// optimization as it could yield an ugly implementation.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct LitPackIter<'a> {
    /// The variable pack to be iterated.
    lit_pack: &'a LitPack,
    /// The current begin position.
    ///
    /// # Note
    ///
    /// The following invariant must hold: `self.begin < self.end`.
    begin: usize,
    /// The current end position.
    ///
    /// # Note
    ///
    /// The following invariant must hold: `self.begin < self.end`.
    end: usize,
}

impl<'a> LitPackIter<'a> {
    /// Creates a new variable pack iterator.
    pub(crate) fn new(lp: &'a LitPack) -> Self {
        Self {
            lit_pack: lp,
            begin: 0,
            end: lp.len(),
        }
    }
}

impl<'a> Iterator for LitPackIter<'a> {
    type Item = Lit;

    fn next(&mut self) -> Option<Self::Item> {
        if self.begin == self.end {
            return None;
        }
        let lit = unsafe { self.lit_pack.get_unchecked(self.begin) };
        self.begin += 1;
        Some(lit)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.end - self.begin;
        (remaining, Some(remaining))
    }

    fn nth(&mut self, index: usize) -> Option<Self::Item> {
        use std::cmp;
        let nth_lit = unsafe { self.lit_pack.get_unchecked(self.begin + index) };
        self.begin += cmp::min(index + 1, self.end);
        Some(nth_lit)
    }
}

impl<'a> DoubleEndedIterator for LitPackIter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.begin == self.end {
            return None;
        }
        self.end -= 1;
        Some(unsafe {
			self.lit_pack.get_unchecked(self.end)
		})
    }
}

impl<'a> ExactSizeIterator for LitPackIter<'a> {}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn new_invalid_offset() {
		assert!(LitPack::new(0, 1).is_err());
		assert!(LitPack::new(0, 5).is_err());
		assert!(LitPack::new(0, 42).is_err());
		assert!(LitPack::new(0, Var::MAX.to_u32()).is_err());
	}

	#[test]
	fn new_invalid_length() {
		assert!(LitPack::new(1, 0).is_err());
		assert!(LitPack::new(5, 0).is_err());
		assert!(LitPack::new(42, 0).is_err());
		assert!(LitPack::new(Var::MAX.to_u32(), 0).is_err());
	}

	#[test]
	fn new_off_len_out_of_bounds() {
		assert!(LitPack::new(Var::MAX.to_u32(), 1).is_err());
		assert!(LitPack::new(1, Var::MAX.to_u32()).is_err());
	}

	#[test]
	fn new_ok() {
		fn assert_for_off_len(valid_off: u32, valid_len: u32) {
			assert!(
				LitPack::new(valid_off, valid_len).is_ok()
			);
		}
		assert_for_off_len(1, 1);
		assert_for_off_len(5, 1);
		assert_for_off_len(1, 5);
		assert_for_off_len(5, 5);
		assert_for_off_len(42, 5);
		assert_for_off_len(5, 42);
		assert_for_off_len(42, 42);
		assert_for_off_len(Var::MAX.to_u32() - 1, 1);
		assert_for_off_len(1, Var::MAX.to_u32() - 1);
	}

	#[test]
	fn flip_all() {
		let mut lp1 = LitPack::new(1, 5).unwrap();
		let mut lp2 = LitPack::new(1, 5).unwrap();
		lp1.flip_all();
		for i in 0..5 {
			lp2.flip_at(i).unwrap();
		}
		assert_eq!(lp1, lp2);
	}

	#[test]
	fn flip_all_involution() {
		let mut lp1 = LitPack::new(1, 5).unwrap();
		let lp2 = LitPack::new(1, 5).unwrap();
		lp1.flip_all();
		lp1.flip_all();
		assert_eq!(lp1, lp2);
	}

	#[test]
	fn get_ok() {
		let lp = LitPack::new(100, 42).unwrap();
		assert_eq!(lp.get(0), Ok(Lit::pos(unsafe { Var::new_unchecked(100) })));
		assert_eq!(lp.get(1), Ok(Lit::pos(unsafe { Var::new_unchecked(101) })));
		assert_eq!(lp.get(5), Ok(Lit::pos(unsafe { Var::new_unchecked(105) })));
		assert_eq!(lp.get(41), Ok(Lit::pos(unsafe { Var::new_unchecked(141) })));
	}

	#[test]
	fn get_err() {
		let lp = LitPack::new(100, 42).unwrap();
		assert!(lp.get(42).is_err());
		assert!(lp.get(100).is_err());
	}

	#[test]
	fn get_unchecked_ok() {
		let lp = LitPack::new(100, 42).unwrap();
		assert_eq!(unsafe { lp.get_unchecked( 0) }, Lit::pos(unsafe { Var::new_unchecked(100) }));
		assert_eq!(unsafe { lp.get_unchecked( 1) }, Lit::pos(unsafe { Var::new_unchecked(101) }));
		assert_eq!(unsafe { lp.get_unchecked( 5) }, Lit::pos(unsafe { Var::new_unchecked(105) }));
		assert_eq!(unsafe { lp.get_unchecked(41) }, Lit::pos(unsafe { Var::new_unchecked(141) }));
	}

	#[test]
	#[should_panic]
	#[cfg(debug_assertions)]
	fn get_unchecked_err() {
		unsafe {LitPack::new(100, 42).unwrap().get_unchecked(42); }
	}

	#[test]
	fn len() {
		assert_eq!(LitPack::new(1, 1).unwrap().len(), 1);
		assert_eq!(LitPack::new(5, 1).unwrap().len(), 1);
		assert_eq!(LitPack::new(1, 5).unwrap().len(), 5);
		assert_eq!(LitPack::new(42, 42).unwrap().len(), 42);
	}

	#[test]
	fn split_at_0() {
		assert!(LitPack::new(1, 5).unwrap().split(0).is_err())
	}

	#[test]
	fn split_out_of_bounds_close() {
		assert!(LitPack::new(1, 5).unwrap().split(5).is_err())
	}

	#[test]
	fn split_out_of_bounds() {
		assert!(LitPack::new(100, 500).unwrap().split(1000).is_err())
	}

	#[test]
	fn split_ok() {
		assert_eq!(
			LitPack::new(1, 2).unwrap().split(1),
			Ok(
				(
					LitPack::new(1, 1).unwrap(),
					LitPack::new(2, 1).unwrap()
				)
			)
		);
		assert_eq!(
			LitPack::new(100, 500).unwrap().split(200),
			Ok(
				(
					LitPack::new(100, 200).unwrap(),
					LitPack::new(300, 300).unwrap()
				)
			)
		)
	}

    mod iter {
        use super::*;

        #[test]
        fn single_lit() {
			let pack = LitPack::new(1, 1).unwrap();
			let mut iter = pack.iter();
			assert_eq!(iter.next(), Some(Lit::pos(Var::new(1).unwrap())));
			assert_eq!(iter.next(), None);
        }

        #[test]
        fn next() {
			let pack = LitPack::new(100, 4).unwrap();
			let mut it = pack.iter();
            assert_eq!(it.next(), Some(Lit::pos(unsafe { Var::new_unchecked(100) })));
            assert_eq!(it.next(), Some(Lit::pos(unsafe { Var::new_unchecked(101) })));
            assert_eq!(it.next(), Some(Lit::pos(unsafe { Var::new_unchecked(102) })));
            assert_eq!(it.next(), Some(Lit::pos(unsafe { Var::new_unchecked(103) })));
            assert_eq!(it.next(), None);
        }

        #[test]
        fn next_back() {
			let pack = LitPack::new(100, 4).unwrap();
			let mut it = pack.iter();
            assert_eq!(it.next_back(), Some(Lit::pos(unsafe { Var::new_unchecked(103) })));
            assert_eq!(it.next_back(), Some(Lit::pos(unsafe { Var::new_unchecked(102) })));
            assert_eq!(it.next_back(), Some(Lit::pos(unsafe { Var::new_unchecked(101) })));
            assert_eq!(it.next_back(), Some(Lit::pos(unsafe { Var::new_unchecked(100) })));
            assert_eq!(it.next_back(), None);
        }

        #[test]
        fn next_mixed() {
			let pack = LitPack::new(100, 4).unwrap();
			let mut it = pack.iter();
            assert_eq!(it.next(), Some(Lit::pos(unsafe { Var::new_unchecked(100) })));
            assert_eq!(it.next_back(), Some(Lit::pos(unsafe { Var::new_unchecked(103) })));
            assert_eq!(it.next(), Some(Lit::pos(unsafe { Var::new_unchecked(101) })));
            assert_eq!(it.next_back(), Some(Lit::pos(unsafe { Var::new_unchecked(102) })));
            assert_eq!(it.next(), None);
            assert_eq!(it.next_back(), None);
        }

        #[test]
        fn size_hint() {
            assert_eq!(LitPack::new(100, 4).unwrap().into_iter().size_hint(), (4, Some(4)))
        }
    }
}
