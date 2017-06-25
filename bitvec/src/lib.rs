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

#![feature(untagged_unions)]
#![feature(unique)]

#![allow(dead_code)]
#![allow(unused_variables)]

extern crate num;

mod errors;
mod block;
mod fixint;

use block::{Block};

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

impl DynFlexInt {
	fn len_blocks(&self) -> usize {
		((self.bits as usize - 1) / block::BLOCK_SIZE) + 1
	}
}

impl Clone for DynFlexInt {
	fn clone(&self) -> Self {
		match self.storage() {
			Storage::Inl => {
				DynFlexInt{bits: self.bits, data: BlockChain{inl: unsafe{self.data.inl}}}
			}
			Storage::Ext => {
				let req_blocks = self.len_blocks();
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
		match self.bits as usize {
			n if n <= MAX_INLINED_SIZE => Storage::Inl,
			_                          => Storage::Ext
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

union BlockChain {
	inl: [Block; 2],
	ext: Unique<Block>
}

//  =======================================================================
///  Constructors
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TargetBitWidth {
	/// Tells methods to try to infer the resulting bit-width from the input.
	Infer,
	/// Tells methods to use the given fixed bit-width as resulting bit-width.
	Fixed(u32)
}
// use self::TargetBitWidth::*;

//  =======================================================================
///  Deserialization
/// =======================================================================
impl FlexInt {

	/// Creates a new bitvector from the given binary string representation.
	/// 
	/// Using the first parameter `bitwidth` the user can either let the method infer the resulting bit-width
	/// or set it explicitely.
	/// 
	/// The format of the binary string must follow some rules.
	///  - The only allowed characters are digits `'0'`, `'1'` and the digit-separator `'_'` (underscore).
	///  - The input string must contain at least a single `'0'` or `'1'` character.
	/// 
	/// In any other case the implementation will return an error.
	/// 
	/// # Good Examples
	/// 
	/// - `"0101"`
	/// - `"0111_0010_0000_1110"`
	/// - `"11__00"`
	/// - `"__0__"`
	/// 
	/// # Bad Examples
	/// 
	/// - `"0102"`
	/// - `"01'0001"`
	/// - `"foo"`
	/// - `"-1001"`
	/// 
	/// # Note
	/// 
	/// - The most significant bit (MSB) is on the left.
	/// - The bitwidth of the resulting `FlexInt` is infered from the number of valid digits in the input.
	/// - Input may start with `'0'` which may influence the bit-width of the resulting `FlexInt`.
	pub fn from_bin_str(bitwidth: TargetBitWidth, binary_str: &str) -> Result<FlexInt> {
		unimplemented!();
	}

	/// Creates a new bitvector from the given decimal string representation.
	/// 
	/// Using the first parameter `bitwidth` the user can either let the method infer the resulting bit-width
	/// or set it explicitely.
	/// 
	/// The format of the decimal string must follow some rules.
	///  - The only allowed characters are digits `'0'`, `'1'`,..,`'9'` and the digit-separator `'_'` (underscore).
	///  - The input string must contain at least a single valid digit character.
	/// 
	/// In any other case the implementation will return an error.
	/// 
	/// # Good Examples
	/// 
	/// - `"3497"`
	/// - `"0323_0321_9876_5432"`
	/// - `"85__132"`
	/// - `"__9__"`
	/// - `"000075"`
	/// 
	/// # Bad Examples
	/// 
	/// - `"0A5C"`
	/// - `"13'8273"`
	/// - `"bar"`
	/// - `"-1337"`
	/// 
	/// # Note
	/// 
	/// - The most significant digit is on the left.
	/// - The bitwidth of the resulting `FlexInt` is infered from the number of valid digits in the input.
	/// - Input may start with `'0'` which may influence the bit-width of the resulting `FlexInt`.
	pub fn from_dec_str(bitwidth: TargetBitWidth, dec_str: &str) -> Result<FlexInt> {
		unimplemented!();
	}

	/// Creates a new bitvector from the given hexa-decimal string representation.
	/// 
	/// Using the first parameter `bitwidth` the user can either let the method infer the resulting bit-width
	/// or set it explicitely.
	/// 
	/// The format of the decimal string must follow some rules.
	///  - The only allowed characters are the digits `'0'`, `'1'`,..,`'9'` the alphas `'A'`,`'B'`,..,`'F'` and the digit-separator `'_'` (underscore).
	///  - The input string must contain at least a single valid alpha-numeric character.
	/// 
	/// In any other case the implementation will return an error.
	/// 
	/// # Good Examples
	/// 
	/// - `"AC08"`
	/// - `"03B8_A30D_EEE2_007"`
	/// - `"FF__A00"`
	/// - `"__E__"`
	/// - `"B008CE"`
	/// 
	/// # Bad Examples
	/// 
	/// - `"ffcc0"`: no small letters!
	/// - `"0K5X"`
	/// - `"13'8273"`
	/// - `"foobar"`
	/// - `"-MCLVII"`
	/// 
	/// # Note
	/// 
	/// - The most significant quad is on the left.
	/// - The bitwidth of the resulting `FlexInt` is infered from the number of valid digits in the input.
	/// - Input may start with `'0'` which may influence the bit-width of the resulting `FlexInt`.
	pub fn from_hex_str(bitwidth: TargetBitWidth, hex_str: &str) -> Result<FlexInt> {
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

	/// Returns the bit-width of this `FlexInt` as `usize`.
	#[inline]
	pub fn len_bits(&self) -> usize {
		self.bits() as usize
	}

	/// Returns the number of bit-blocks used internally for value representation.
	/// 
	/// Note:
	/// 
	/// - This method should not be part of the public interface.
	/// - The returned values are valid for bit-block sizes of 32 bit.
	fn len_blocks(&self) -> usize {
		match self.data {
			_1(_)  => 1,
			_8(_)  => 1,
			_16(_) => 1,
			_32(_) => 1,
			_64(_) => 2,
			Dyn(ref i) => i.len_blocks()
		}
	}

	/// Returns true if this `FlexInt` represents the zero (0) value.
	#[inline]
	pub fn is_zero(&self) -> bool {
		use num::Zero;
		match self.data {
			_1(v)  => v == false,
			_8(v)  => v.is_zero(),
			_16(v) => v.is_zero(),
			_32(v) => v.is_zero(),
			_64(v) => v.is_zero(),
			Dyn(ref v) => unimplemented!()
		}
	}

	/// Returns true if this `FlexInt` represents the one (1) value.
	#[inline]
	pub fn is_one(&self) -> bool {
		match self.data {
			_1(v)  => v == true,
			_8(v)  => v == 1,
			_16(v) => v == 1,
			_32(v) => v == 1,
			_64(v) => v == 1,
			Dyn(ref n) => unimplemented!()
		}
	}

	/// Returns true if all bits of this `FlexInt` are `1` (one).
	#[inline]
	pub fn is_ones(&self) -> bool {
		match self.data {
			_1(v)  => v == true,
			_8(v)  => v == 0xFF,
			_16(v) => v == 0xFFFF,
			_32(v) => v == 0xFFFF_FFFF,
			_64(v) => v == 0xFFFF_FFFF_FFFF_FFFF,
			Dyn(ref v) => unimplemented!()
		}
	}

	/// Returns true if no bits of this `FlexInt` are `0` (zero).
	#[inline]
	pub fn is_zeros(&self) -> bool {
		self.is_zero()
	}

	/// Returns the number of ones in the binary representation of this `FlexInt`.
	pub fn count_ones(&self) -> usize {
		match self.data {
			_1(v)  => if v { 1 } else { 0 },
			_8(v)  => v.count_ones() as usize,
			_16(v) => v.count_ones() as usize,
			_32(v) => v.count_ones() as usize,
			_64(v) => v.count_ones() as usize,
			Dyn(ref v) => unimplemented!()
		}
	}

	/// Returns the number of zeroes in the binary representation of this `FlexInt`.
	pub fn count_zeros(&self) -> usize {
		match self.data {
			_1(v)  => if v { 0 } else { 1 },
			_8(v)  => v.count_zeros() as usize,
			_16(v) => v.count_zeros() as usize,
			_32(v) => v.count_zeros() as usize,
			_64(v) => v.count_zeros() as usize,
			Dyn(ref v) => unimplemented!()
		}
	}

	/// Returns the number of leading zeroes in the binary representation of this `FlexInt`.
	pub fn leading_zeros(&self) -> usize {
		match self.data {
			_1(v)  => if v { 0 } else { 1 },
			_8(v)  => v.leading_zeros() as usize,
			_16(v) => v.leading_zeros() as usize,
			_32(v) => v.leading_zeros() as usize,
			_64(v) => v.leading_zeros() as usize,
			Dyn(ref v) => unimplemented!()
		}
	}

	/// Returns the number of trailing zeroes in the binary representation of this `FlexInt`.
	pub fn trailing_zeroes(&self) -> usize {
		match self.data {
			_1(v)  => if v { 0 } else { 1 },
			_8(v)  => v.trailing_zeros() as usize,
			_16(v) => v.trailing_zeros() as usize,
			_32(v) => v.trailing_zeros() as usize,
			_64(v) => v.trailing_zeros() as usize,
			Dyn(ref v) => unimplemented!()
		}
	}

	/// Returns `true` if and only if `self == 2^k` for some `k`.
	pub fn is_power_of_two(&self) -> usize {
		unimplemented!()
	}
}

//  =======================================================================
///  Bit-level getters and setters
/// =======================================================================
impl FlexInt {

	/// Returns `true` if the bit at the `n`th position is set, else `false`.
	/// 
	/// #Panics
	/// 
	/// If `n` is out of bounds.
	pub fn get(&self, n: usize) -> bool {
		if n >= self.len_bits() {
			panic!("FlexInt::get({:?}) is out of bounds of instance with {:?} bits.", n, self.bits())
		}
		match self.data {
			_1(v)  => v,
			_8(v)  => ((v >> n) & 0x01) == 1,
			_16(v) => ((v >> n) & 0x01) == 1,
			_32(v) => ((v >> n) & 0x01) == 1,
			_64(v) => ((v >> n) & 0x01) == 1,
			Dyn(ref v) => unimplemented!()
		}
	}

	/// Sets the bit at the `n`th position to `1`.
	/// 
	/// Returns the value of the bit before this operation.
	/// 
	/// #Panics
	/// 
	/// If `n` is out of bounds.
	pub fn set(&mut self, n: usize) {
		if n >= self.len_bits() {
			panic!("FlexInt::set({:?}) is out of bounds of instance with {:?} bits.", n, self.bits())
		}
		match self.data {
			_1(ref mut v)  => *v  = true,
			_8(ref mut v)  => *v |= 0x01 << n,
			_16(ref mut v) => *v |= 0x01 << n,
			_32(ref mut v) => *v |= 0x01 << n,
			_64(ref mut v) => *v |= 0x01 << n,
			Dyn(ref mut v) => unimplemented!()
		}
	}

	/// Unsets the bit at the `n`th position to `0`.
	/// 
	/// #Panics
	/// 
	/// If `n` is out of bounds.
	pub fn unset(&mut self, n: usize) {
		if n >= self.len_bits() {
			panic!("FlexInt::unset({:?}) is out of bounds of instance with {:?} bits.", n, self.bits())
		}
		match self.data {
			_1(ref mut v)  => *v  = false,
			_8(ref mut v)  => *v &= !(0x01 << n),
			_16(ref mut v) => *v &= !(0x01 << n),
			_32(ref mut v) => *v &= !(0x01 << n),
			_64(ref mut v) => *v &= !(0x01 << n),
			Dyn(ref mut v) => unimplemented!()
		}
	}

	/// Flips the bit at the `n`th position.
	/// 
	/// #Panics
	/// 
	/// If `n` is out of bounds.
	pub fn flip(&mut self, n: usize) {
		if n >= self.len_bits() {
			panic!("FlexInt::flip({:?}) is out of bounds of instance with {:?} bits.", n, self.bits())
		}
		match self.data {
			_1(ref mut v)  => *v  = !*v,
			_8(ref mut v)  => *v ^= 0x01 << n,
			_16(ref mut v) => *v ^= 0x01 << n,
			_32(ref mut v) => *v ^= 0x01 << n,
			_64(ref mut v) => *v ^= 0x01 << n,
			Dyn(ref mut v) => unimplemented!()
		}
	}

}

//  =======================================================================
///  Relational Operations
/// =======================================================================
impl FlexInt {

	/// Unsigned less-than comparison with the other bitvec.
	pub fn ult(&self, other: &FlexInt) -> bool {
		unimplemented!()
		// match (self.repr, other.repr) {

		// 	// one of them is undef
		// 	(Undef, _) | (_, Undef) => {
		// 		panic!("FlexInt::ult(): Cannot decide this information on undefined representant!")
		// 	}

		// 	// non-undefs
		// 	(l, r) => {
		// 		// match for storage properties
		// 		match (l.storage(), r.storage()) {
		// 			(Inline, Inline) => {
		// 				unsafe{self.data.inl.u < other.data.inl.u}
		// 			}
		// 			(Inline, Extern) => {
		// 				unimplemented!()
		// 			}
		// 			(Extern, Inline) => {
		// 				unimplemented!()
		// 			}
		// 			(Extern, Extern) => {
		// 				unimplemented!()
		// 			}
		// 		}
		// 	}
		// }
	}

	/// Unsigned less-than-or-equals comparison with the other bitvec.
	pub fn ule(&self, other: &FlexInt) -> bool {
		!(other.ult(self))
	}

	/// Unsigned greater-than comparison with the other bitvec.
	pub fn ugt(&self, other: &FlexInt) -> bool {
		other.ult(self)
	}

	/// Unsigned greater-than-or-equals comparison with the other bitvec.
	pub fn uge(&self, other: &FlexInt) -> bool {
		!(self.ult(other))
	}

	/// Signed less-than comparison with the other bitvec.
	pub fn slt(&self, other: &FlexInt) -> bool {
		unimplemented!()
		// match (self.repr, other.repr) {

		// 	// one of them is undef
		// 	(Undef, _) | (_, Undef) => {
		// 		panic!("FlexInt::slt(): Cannot decide this information on undefined representant!")
		// 	}

		// 	// non-undefs
		// 	(l, r) => {
		// 		// match for storage properties
		// 		match (l.storage(), r.storage()) {
		// 			(Inline, Inline) => {
		// 				unsafe{self.data.inl.s < other.data.inl.s}
		// 			}
		// 			(Inline, Extern) => {
		// 				unimplemented!()
		// 			}
		// 			(Extern, Inline) => {
		// 				unimplemented!()
		// 			}
		// 			(Extern, Extern) => {
		// 				unimplemented!()
		// 			}
		// 		}
		// 	}
		// }
	}

	/// Signed less-than-or-equals comparison with the other bitvec.
	pub fn sle(&self, other: &FlexInt) -> bool {
		!(other.slt(self))
	}

	/// Signed greater-than comparison with the other bitvec.
	pub fn sgt(&self, other: &FlexInt) -> bool {
		other.slt(self)
	}

	/// Signed greater-than-or-equals comparison with the other bitvec.
	pub fn sge(&self, other: &FlexInt) -> bool {
		!(self.slt(other))
	}

}

//  =======================================================================
///  Extend & Truncate Operations
/// =======================================================================
impl FlexInt {

	/// Creates a new `FlexInt` that represents this `FlexInt` truncated to 
	/// the given amount of bits.
	///
	/// # Panics
	/// 
	/// - If `bits` is greater than the `FlexInt`'s current bit-width.
	/// - If `bits` is zero (`0`).
	/// 
	/// # Note
	/// 
	/// Equal to a call to `clone()` if `bits` is equal to this `FlexInt`'s bit-width.
	pub fn truncate(&self, bits: usize) -> Self {
		unimplemented!();
	}

	/// Creates a new `FlexInt` that represents the zero-extension of this `FlexInt` to the given bits.
	///
	/// # Semantics (from LLVM)
	/// 
	/// The zext fills the high order bits of the value with zero bits until it reaches the size of the destination bit-width.
	/// When zero extending from `i1`, the result will always be either `0` or `1`.
	/// 
	/// # Panics
	/// 
	/// - If `bits` is less than the `FlexInt`'s current bit-width.
	/// 
	/// # Note
	/// 
	/// Equal to a call to `clone()` if `bits` is equal to this `FlexInt`'s bit-width.
	pub fn zext(&self, bits: usize) -> Self {
		unimplemented!();
	}

	/// Creates a new `FlexInt` that represents the sign-extension of this `FlexInt` to the given bits.
	/// 
	/// 
	/// # Semantic (from LLVM)
	/// 
	/// The ‘sext‘ instruction performs a sign extension by copying the sign bit (highest order bit) of the value until it reaches the target bit-width.
	/// When sign extending from `i1`, the extension always results in `-1` or `0`.
	///
	/// # Panics
	/// 
	/// - If `bits` is less than the `FlexInt`'s current bit-width.
	/// 
	/// # Note
	/// 
	/// Equal to a call to `clone()` if `bits` is equal to this `FlexInt`'s bit-width.
	pub fn sext(&self, bits: usize) -> Self {
		unimplemented!();
	}

}

use std::marker::PhantomData;

/// A const-iterator over the `Block`s of a `FlexInt`.
struct Blocks<'a> {
	// TODO
	temp: &'a PhantomData<()> // TODO: remove this again when implementation is done
}

/// A mutable-iterator over the `Block`s of a `FlexInt`.
struct BlocksMut<'a> {
	// TODO
	temp: &'a PhantomData<()> // TODO: remove this again when implementation is done
}

/// A move-iterator over the `Block`s of a `FlexInt`.
struct IntoBlocks {
	// TODO
}

/// A `Block` wrapper adding a bit-width restriction and some operational methods.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct ComputeBlock {
	bits: u32,
	data: Block
}

/// A mutable reference `Block` wrapper adding a bit-width restriction and some operational methods.
#[derive(Debug, PartialEq, Eq, Hash)]
struct ComputeBlockMut<'a> {
	bits: u32,
	data: &'a mut Block
}

impl<'a> Iterator for Blocks<'a> {
	type Item = ComputeBlock;

	fn next(&mut self) -> Option<Self::Item> {
		unimplemented!()
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

#[cfg(test)]
mod tests {
	// use super::*;

	// #[test]
	// fn test_01() {
	// 	let s0: u64 = 200;
	// 	let s1: u64 =  60;
	// 	let r0: u64 = (s0 as u8).wrapping_add(s1 as u8) as u64; // 200 + 60 % 256 = 4
	// 	assert_eq!(r0, 4);
	// }

	// #[test]
	// fn test_02() {
	// 	let s0: i32 = -200;
	// 	let s1: u32 =  300;
	// 	let r0: u32 = (s0 as u32).wrapping_add(s1 as u32) as u32;
	// 	let r1: i32 = (s0 as i32).wrapping_add(s1 as i32) as i32;
	// 	assert_eq!(r0, 100);
	// 	assert_eq!(r1, 100);
	// 	assert_eq!(s0 as u32, 4294967096);
	// }

}
