//! This library provides an implementation for bitvectors in the context of SMT solving.
//!
//! Bitvectors in the context of SMT solving are fixed-sized signed or unsigned integer representatives.
//! They are needed to express and propagate constant values within an SMT procedure and are required
//! to be very fast and have low memory overhead since their quantity on a common run might be very high.
//!
//! Bitvectors in the context of SMT solving must not be confused with bitvectors that act as storage
//! for bits as in C++'s `<bitset>`. Although they also allow to operate on them via the typical bitset-based
//! methods as `intersect`, `union` and `difference`.
//!
//! This data structure was designed to be especially fast for smaller instances.
//! As of now small instances are instances that represent numbers that fit into 64 bits of memory.
//!
//! Since bitvector instances might store a variadic and potentially large amount of data they might
//! require heap allocation and thus are no `Copy` types.
//! This also eliminates the possibilities to overload operators on them in the current Rust design.
//!
//! Instances of bitvectors cannot grow or shrink as normal vectors and are fixed upon construction.
//! This allows further optimizations and even less memory overhead since no capacity field is required.
//! 
//! There are some methods that do not result in a new bitvector instance but that mutate the given
//! instance and most often are suffixed with `_assign`.
//!

use std::result;
use std::fmt;
use std::ptr::Unique;
use std::hash::{Hash, Hasher};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorKind {
	InvalidBinaryStr(String),
	InvalidDecimalStr(String),
	InvalidHexStr(String),
	UnmatchingBitwidth(u32, u32),
	InvalidZeroBitWidth,
	InvalidBitWidthArgument(u32)
}
use self::ErrorKind::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Error(ErrorKind);

pub type Result<T> = result::Result<T, Error>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FlexInt {
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
		match self.storage() {
			Storage::Inl => {
				DynFlexInt{bits: self.bits, data: BlockChain{inl: unsafe{self.data.inl}}}
			}
			Storage::Ext => {
				let req_blocks = ((self.bits as usize - 1) / BLOCK_SIZE) + 1;
				let mut buffer = Vec::with_capacity(req_blocks);
				let src: *const Block = unsafe{self.data.ext.as_ptr()};
				let dst: *mut   Block = buffer.as_mut_ptr();
				unsafe{::std::ptr::copy_nonoverlapping(src, dst, req_blocks);}
				::std::mem::forget(buffer);
				DynFlexInt{bits: self.bits, data: BlockChain{ext: unsafe{Unique::new(dst)}}}
			}
		}
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum Storage {
	/// Indicating on stack and inplace memory usage.
	Inl,
	/// Indicating on heap and external memory usage.
	Ext
}

/// The maximum bit-width value that is memory-inlined on the stack.
const MAX_INLINED_SIZE: usize = 64;

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

impl Drop for DynFlexInt {
	fn drop(&mut self) {
		if self.storage() == Storage::Ext {
			::std::mem::drop(unsafe{self.data.ext})
		}
	}
}

#[derive(Copy, Clone, Eq)]
union Block {
	u: u32,
	s: i32
}

/// The number of bits of a single block.
const BLOCK_SIZE: usize = 32;

union BlockChain {
	inl: [Block; 2],
	ext: Unique<Block>
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

//  =======================================================================
///  Constructors for `FlexInt`.
/// =======================================================================
impl FlexInt {
	/// Creates a new `FlexInt` from a given `bool` value with a bit-width of 1.
	#[inline]
	pub fn from_bool(val: bool) -> FlexInt {
		FlexInt{data: FlexIntKind::_1(val)}
	}

	/// Creates a new `FlexInt` from a given `i8` value with a bit-width of 8.
	#[inline]
	pub fn from_i8(val: i8) -> FlexInt {
		FlexInt{data: FlexIntKind::_8(val as u8)}
	}

	/// Creates a new `FlexInt` from a given `i8` value with a bit-width of 8.
	#[inline]
	pub fn from_u8(val: u8) -> FlexInt {
		FlexInt{data: FlexIntKind::_8(val)}
	}

	/// Creates a new `FlexInt` from a given `i16` value with a bit-width of 16.
	#[inline]
	pub fn from_i16(val: i16) -> FlexInt {
		FlexInt{data: FlexIntKind::_16(val as u16)}
	}

	/// Creates a new `FlexInt` from a given `i16` value with a bit-width of 16.
	#[inline]
	pub fn from_u16(val: u16) -> FlexInt {
		FlexInt{data: FlexIntKind::_16(val)}
	}

	/// Creates a new `FlexInt` from a given `i32` value with a bit-width of 32.
	#[inline]
	pub fn from_i32(val: i32) -> FlexInt {
		FlexInt{data: FlexIntKind::_32(val as u32)}
	}

	/// Creates a new `FlexInt` from a given `i32` value with a bit-width of 32.
	#[inline]
	pub fn from_u32(val: u32) -> FlexInt {
		FlexInt{data: FlexIntKind::_32(val)}
	}

	/// Creates a new `FlexInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	pub fn from_i64(val: i64) -> FlexInt {
		FlexInt{data: FlexIntKind::_64(val as u64)}
	}

	/// Creates a new `FlexInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	pub fn from_u64(val: u64) -> FlexInt {
		FlexInt{data: FlexIntKind::_64(val)}
	}

	/// Creates a new `FlexInt` with the given bit-width that represents zero.
	///
	/// **Error** Returns `InvalidZeroBitWidth` in case of a given target bit-width of zero.
	#[inline]
	pub fn zero(bits: u32) -> Result<FlexInt> {
		match bits {
			0  => Err(Error(InvalidZeroBitWidth)),
			1  => Ok(FlexInt::from_bool(false)),
			8  => Ok(FlexInt::from_u8(0)),
			16 => Ok(FlexInt::from_u16(0)),
			32 => Ok(FlexInt::from_u32(0)),
			64 => Ok(FlexInt::from_u64(0)),
			n  => unimplemented!()
		}
	}

	/// Creates a new `FlexInt` with the given bit-width that represents one.
	///
	/// **Error** Returns `InvalidZeroBitWidth` in case of a given target bit-width of zero.
	#[inline]
	pub fn one(bits: u32) -> Result<FlexInt> {
		match bits {
			0  => Err(Error(InvalidZeroBitWidth)),
			1  => Ok(FlexInt::from_bool(true)),
			8  => Ok(FlexInt::from_u8(1)),
			16 => Ok(FlexInt::from_u16(1)),
			32 => Ok(FlexInt::from_u32(1)),
			64 => Ok(FlexInt::from_u64(1)),
			n  => unimplemented!()
		}
	}

	/// Creates a new `FlexInt` with the given bit-width that has all bits set.
	///
	/// **Error** Returns `InvalidZeroBitWidth` in case of a given target bit-width of zero.
	#[inline]
	pub fn zeroes(bits: u32) -> Result<FlexInt> {
		match bits {
			0  => Err(Error(InvalidZeroBitWidth)),
			1  => Ok(FlexInt::from_bool(false)),
			8  => Ok(FlexInt::from_u8(0x00)),
			16 => Ok(FlexInt::from_u16(0x0000)),
			32 => Ok(FlexInt::from_u32(0x0000_0000)),
			64 => Ok(FlexInt::from_u64(0x0000_0000_0000_0000)),
			n  => unimplemented!()
		}
	}

	/// Creates a new `FlexInt` with the given bit-width that has all bits set.
	///
	/// **Error** Returns `InvalidZeroBitWidth` in case of a given target bit-width of zero.
	#[inline]
	pub fn ones(bits: u32) -> Result<FlexInt> {
		match bits {
			0  => Err(Error(InvalidZeroBitWidth)),
			1  => Ok(FlexInt::from_bool(true)),
			8  => Ok(FlexInt::from_u8(0xFF)),
			16 => Ok(FlexInt::from_u16(0xFFFF)),
			32 => Ok(FlexInt::from_u32(0xFFFF_FFFF)),
			64 => Ok(FlexInt::from_u64(0xFFFF_FFFF_FFFF_FFFF)),
			n  => unimplemented!()
		}
	}

}

//  =======================================================================
///  Deserialization
/// =======================================================================
impl FlexInt {

	/// Creates a new bitvector from the given binary string representation.
	/// 
	/// The format of the binary string must follow some rules.
	///  - The only allowed characters are ascii `0`, `1` and a digit separator `_`.
	///  - The input string must contain at least a single `0` or `1` character.
	/// 
	/// In any other case the implementation will return an error.
	/// 
	/// **Good Examples**  
	/// 
	/// - `"0101"`  
	/// - `"0111_0010_0000_1110"`  
	/// - `"11__00"`  
	/// - `"__0__"`  
	/// 
	/// **Bad Examples**  
	/// 
	/// - `"0102"`  
	/// - `"01'0001"`  
	/// - `"foo"`  
	/// - `"-1001"`  
	/// 
	/// Note: The most significant bit (MSB) is on the left.
	pub fn from_bin_str(binary_str: &str) -> Result<FlexInt> {
		unimplemented!();
	}

	/// Creates a new bitvector from the given decimal string representation.
	/// 
	/// Note: The most significant bit (MSB) is on the left.
	pub fn from_dec_str(dec_str: &str) -> Result<FlexInt> {
		unimplemented!();
	}

	/// Creates a new bitvector from the given hexa-decimal string representation.
	/// 
	/// Note: The most significant bit (MSB) is on the left.
	pub fn from_hex_str(hex_str: &str) -> Result<FlexInt> {
		unimplemented!();
	}

}

//  =======================================================================
///  Serialization
/// =======================================================================
impl FlexInt {

	/// Returns a string representation of the binary encoded bitvector.
	pub fn to_bin_string(&self) -> String {
		unimplemented!();
	}

	/// Returns a string representation of the decimal encoded bitvector.
	pub fn to_dec_string(&self) -> String {
		unimplemented!();
	}

	/// Returns a string representation of the hex-decimal encoded bitvector.
	pub fn to_hex_string(&self) -> String {
		unimplemented!();
	}

}

//  =======================================================================
///  Utility and informational getter methods.
/// =======================================================================
impl FlexInt {
	/// Returns the bit-width of this `FlexInt`.
	#[inline]
	pub fn bits(&self) -> u32 {
		match self.data {
			_1(_)  => 1,
			_8(_)  => 8,
			_16(_) => 16,
			_32(_) => 32,
			_64(_) => 64,
			Dyn(ref i) => i.bits()
		}
	}

	/// Returns true if this `FlexInt` represents the zero (0) value.
	#[inline]
	pub fn is_zero(&self) -> bool {
		use num::Zero;
		match self.data {
			_1(n)  => n == false,
			_8(n)  => n.is_zero(),
			_16(n) => n.is_zero(),
			_32(n) => n.is_zero(),
			_64(n) => n.is_zero(),
			Dyn(ref n) => unimplemented!()
		}
	}

	/// Returns true if this `FlexInt` represents the one (1) value.
	#[inline]
	pub fn is_one(&self) -> bool {
		match self.data {
			_1(n)  => n == true,
			_8(n)  => n == 1,
			_16(n) => n == 1,
			_32(n) => n == 1,
			_64(n) => n == 1,
			Dyn(ref n) => unimplemented!()
		}
	}

	/// Returns true if all bits of this `FlexInt` are set.
	#[inline]
	pub fn all(&self) -> bool {
		unimplemented!()
	}

	/// Returns true if no bits of this `FlexInt` are set.
	#[inline]
	pub fn none(&self) -> bool {
		unimplemented!()
	}

	/// Returns true if any bit of this `FlexInt` are set.
	#[inline]
	pub fn any(&self) -> bool {
		unimplemented!()
	}

	/// Returns the number of ones in the binary representation of this `FlexInt`.
	pub fn count_ones(&self) -> usize {
		unimplemented!()
	}

	/// Returns the number of zeroes in the binary representation of this `FlexInt`.
	pub fn count_zeroes(&self) -> usize {
		unimplemented!()
	}

	/// Returns the number of leading zeroes in the binary representation of this `FlexInt`.
	pub fn leading_zeroes(&self) -> usize {
		unimplemented!()
	}

	/// Returns the number of trailing zeroes in the binary representation of this `FlexInt`.
	pub fn trailing_zeroes(&self) -> usize {
		unimplemented!()
	}

	/// Returns `true` if and only if `self == 2^k` for some `k`.
	pub fn is_power_of_two(&self) -> usize {
		unimplemented!()
	}
}
