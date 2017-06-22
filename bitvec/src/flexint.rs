use std::fmt;
use std::ptr::Unique;
use std::hash::{Hash, Hasher};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FlexInt {
	data: FlexIntKind
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FlexIntKind {
	_1(bool),
	_8(u8),
	_16(u16),
	_32(u32),
	_64(u64),
	Dyn(DynFlexInt)
}
use self::FlexIntKind::*;

struct DynFlexInt {
	bits: u32,
	data: BlockChain
}

impl Clone for DynFlexInt {
	fn clone(&self) -> Self {
		unimplemented!() // TODO
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum Storage {
	Inl,
	Ext
}

impl DynFlexInt {
	#[inline]
	fn bits(&self) -> u32 {
		self.bits
	}

	/// Returns `Storage::Inl` when the representant is stored 
	/// inline (on the stack) and `Storage::Ext` otherwise.
	#[inline]
	fn storage(&self) -> Storage {
		match self.bits {
			n if n <= 64 => Storage::Inl,
			_            => Storage::Ext
		}
	}
}

impl fmt::Debug for DynFlexInt {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		Ok(()) // TODO
	}
}

impl PartialEq for DynFlexInt {
	fn eq(&self, other: &DynFlexInt) -> bool {
		if self.bits != other.bits {
			return false;
		}
		match self.storage() {
			Storage::Inl => {
				let ldat = unsafe{self.data.inl};
				let rdat = unsafe{other.data.inl};
				ldat == rdat
			}
			Storage::Ext => {
				unimplemented!()
			}
		}
	}
}

impl Eq for DynFlexInt {}

impl Hash for DynFlexInt {
	fn hash<H: Hasher>(&self, h: &mut H) {
		self.bits.hash(h);
		match self.storage() {
			Storage::Inl => {
				unsafe{self.data.inl.hash(h)}
			}
			Storage::Ext => {
				unimplemented!()
			}
		}
	}
}

union BlockChain {
	inl: [Block; 2],
	ext: Unique<Block>
}

#[derive(Copy, Clone, Eq)]
union Block {
	u: u32,
	s: i32
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

/// Constructors for `FlexInt`.
impl FlexInt {
	/// Creates a new `FlexInt` from a given `bool` value with a bit-width of 1.
	#[inline]
	fn from_bool(val: bool) -> FlexInt {
		FlexInt{data: FlexIntKind::_1(val)}
	}

	/// Creates a new `FlexInt` from a given `i8` value with a bit-width of 8.
	#[inline]
	fn from_i8(val: i8) -> FlexInt {
		FlexInt{data: FlexIntKind::_8(val as u8)}
	}

	/// Creates a new `FlexInt` from a given `i8` value with a bit-width of 8.
	#[inline]
	fn from_u8(val: u8) -> FlexInt {
		FlexInt{data: FlexIntKind::_8(val)}
	}

	/// Creates a new `FlexInt` from a given `i16` value with a bit-width of 16.
	#[inline]
	fn from_i16(val: i16) -> FlexInt {
		FlexInt{data: FlexIntKind::_16(val as u16)}
	}

	/// Creates a new `FlexInt` from a given `i16` value with a bit-width of 16.
	#[inline]
	fn from_u16(val: u16) -> FlexInt {
		FlexInt{data: FlexIntKind::_16(val)}
	}

	/// Creates a new `FlexInt` from a given `i32` value with a bit-width of 32.
	#[inline]
	fn from_i32(val: i32) -> FlexInt {
		FlexInt{data: FlexIntKind::_32(val as u32)}
	}

	/// Creates a new `FlexInt` from a given `i32` value with a bit-width of 32.
	#[inline]
	fn from_u32(val: u32) -> FlexInt {
		FlexInt{data: FlexIntKind::_32(val)}
	}

	/// Creates a new `FlexInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	fn from_i64(val: i64) -> FlexInt {
		FlexInt{data: FlexIntKind::_64(val as u64)}
	}

	/// Creates a new `FlexInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	fn from_u64(val: u64) -> FlexInt {
		FlexInt{data: FlexIntKind::_64(val)}
	}

	/// Creates a new `FlexInt` with the given bit-width that represents zero.
	#[inline]
	fn zero(bits: u32) -> FlexInt {
		match bits {
			0  => panic!("FlexInt::zero(0): Cannot be called with 0 bits."),
			1  => FlexInt::from_bool(false),
			8  => FlexInt::from_u8(0),
			16 => FlexInt::from_u16(0),
			32 => FlexInt::from_u32(0),
			64 => FlexInt::from_u64(0),
			n  => unimplemented!()
		}
	}

	/// Creates a new `FlexInt` with the given bit-width that represents one.
	#[inline]
	fn one(bits: u32) -> FlexInt {
		match bits {
			0  => panic!("FlexInt::zero(0): Cannot be called with 0 bits."),
			1  => FlexInt::from_bool(true),
			8  => FlexInt::from_u8(1),
			16 => FlexInt::from_u16(1),
			32 => FlexInt::from_u32(1),
			64 => FlexInt::from_u64(1),
			n  => unimplemented!()
		}
	}

	/// Creates a new `FlexInt` with the given bit-width and sets all bits to the
	/// given pattern which is repeated until all bits are set.
	/// 
	/// The pattern's size has to divie the given bit-width properly.
	#[inline]
	fn from_pattern<T>(bits: u32, pattern: T) -> FlexInt
		where T: Into<FlexInt>
	{
		match bits {
			bits if bits < 64 => {
				let pattern = pattern.into();
				assert!(pattern.bits() <= bits);
				let dynflex = DynFlexInt{
					bits: bits,
					data: BlockChain{
						inl: unimplemented!()
					}
				};
				FlexInt{data: FlexIntKind::Dyn(dynflex)}
			}
			_ => {
				unimplemented!()
			}
		}
	}
}

/// Utility and informational getter methods.
impl FlexInt {
	/// Returns the bit-width of this `FlexInt`.
	#[inline]
	fn bits(&self) -> u32 {
		match &self.data {
			&_1(_)  => 1,
			&_8(_)  => 8,
			&_16(_) => 16,
			&_32(_) => 32,
			&_64(_) => 64,
			&Dyn(ref i) => i.bits()
		}
	}
}
