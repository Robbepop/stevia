use ::block::{BLOCK_SIZE, Block};
use ::errors::{Error, Result};

use errors::ErrorKind::*;

use std::ptr::Unique;
use std::hash::{Hash, Hasher};
use std::fmt;

pub struct FixInt {
	bits: u32,
	data: FixIntData
}

const INLINED_BLOCKS: usize = 2;
const INLINED_BITS  : usize = INLINED_BLOCKS * BLOCK_SIZE;

union FixIntData {
	opt: u64,
	inl: [Block; INLINED_BLOCKS],
	ext: Unique<Block>
}

#[derive(Debug, Copy, Clone)]
struct BlockChain<'a>(&'a [Block]);

#[derive(Debug)]
struct BlockChainMut<'a>(&'a mut [Block]);

impl Clone for FixInt {
	fn clone(&self) -> Self {
		match self.storage() {
			Storage::Inl => {
				FixInt{bits: self.bits, data: FixIntData{opt: unsafe{self.data.opt}}}
			}
			Storage::Ext => {
				let req_blocks = self.len_blocks();
				let mut buffer = Vec::with_capacity(req_blocks);
				let src: *const Block = unsafe{self.data.ext.as_ptr()};
				let dst: *mut   Block = buffer.as_mut_ptr();
				unsafe{::std::ptr::copy_nonoverlapping(src, dst, req_blocks);}
				::std::mem::forget(buffer);
				FixInt{bits: self.bits, data: FixIntData{ext: unsafe{Unique::new(dst)}}}
			}
		}
	}
}

impl fmt::Debug for FixInt {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		Ok(()) // TODO
	}
}

impl PartialEq for FixInt {
	fn eq(&self, other: &FixInt) -> bool {
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

impl Eq for FixInt {}

impl Hash for FixInt {
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

impl Drop for FixInt {
	fn drop(&mut self) {
		if self.storage() == Storage::Ext {
			::std::mem::drop(unsafe{self.data.ext})
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

#[derive(Debug, Copy, Clone)]
enum FixIntModel<'a> {
	C8(u8),
	C16(u16),
	C32(u32),
	C64(u64),
	Var(BlockChain<'a>)
}

#[derive(Debug)]
enum FixIntModelMut<'a> {
	C8(&'a mut u64),
	C16(&'a mut u64),
	C32(&'a mut u64),
	C64(&'a mut u64),
	Var(BlockChainMut<'a>)
}

impl FixInt {
	/// Returns `Storage::Inl` when the representant is stored 
	/// inline (on the stack) and `Storage::Ext` otherwise.
	#[inline]
	fn storage(&self) -> Storage {
		match self.bits as usize {
			n if n <= INLINED_BITS => Storage::Inl,
			_                      => Storage::Ext
		}
	}

	#[inline]
	fn model(&self) -> FixIntModel {
		match self.bits {
			0  => unreachable!(),
			8  => FixIntModel::C8(unsafe{self.data.opt} as u8),
			16 => FixIntModel::C16(unsafe{self.data.opt} as u16),
			32 => FixIntModel::C32(unsafe{self.data.opt} as u32),
			64 => FixIntModel::C64(unsafe{self.data.opt} as u64),
			n  => unimplemented!()
		}
	}

	#[inline]
	fn model_mut(&mut self) -> FixIntModelMut {
		match self.bits {
			0  => unreachable!(),
			8  => FixIntModelMut::C8(unsafe{&mut self.data.opt}),
			16 => FixIntModelMut::C16(unsafe{&mut self.data.opt}),
			32 => FixIntModelMut::C32(unsafe{&mut self.data.opt}),
			64 => FixIntModelMut::C64(unsafe{&mut self.data.opt}),
			n  => unimplemented!()
		}
	}
}


//  =======================================================================
///  Constructors
/// =======================================================================
impl FixInt {
	/// Creates a new `FixInt` from a given `bool` value with a bit-width of 1.
	#[inline]
	pub fn from_bool(val: bool) -> FixInt {
		FixInt{bits: 1, data: FixIntData{opt: if val { 1 } else { 0 }}}
	}

	/// Creates a new `FixInt` from a given `i8` value with a bit-width of 8.
	#[inline]
	pub fn from_i8(val: i8) -> FixInt {
		FixInt{bits: 8, data: FixIntData{opt: val as u64}}
	}

	/// Creates a new `FixInt` from a given `i8` value with a bit-width of 8.
	#[inline]
	pub fn from_u8(val: u8) -> FixInt {
		FixInt{bits: 8, data: FixIntData{opt: val as u64}}
	}

	/// Creates a new `FixInt` from a given `i16` value with a bit-width of 16.
	#[inline]
	pub fn from_i16(val: i16) -> FixInt {
		FixInt{bits: 16, data: FixIntData{opt: val as u64}}
	}

	/// Creates a new `FixInt` from a given `i16` value with a bit-width of 16.
	#[inline]
	pub fn from_u16(val: u16) -> FixInt {
		FixInt{bits: 16, data: FixIntData{opt: val as u64}}
	}

	/// Creates a new `FixInt` from a given `i32` value with a bit-width of 32.
	#[inline]
	pub fn from_i32(val: i32) -> FixInt {
		FixInt{bits: 32, data: FixIntData{opt: val as u64}}
	}

	/// Creates a new `FixInt` from a given `i32` value with a bit-width of 32.
	#[inline]
	pub fn from_u32(val: u32) -> FixInt {
		FixInt{bits: 32, data: FixIntData{opt: val as u64}}
	}

	/// Creates a new `FixInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	pub fn from_i64(val: i64) -> FixInt {
		FixInt{bits: 64, data: FixIntData{opt: val as u64}}
	}

	/// Creates a new `FixInt` from a given `i64` value with a bit-width of 64.
	#[inline]
	pub fn from_u64(val: u64) -> FixInt {
		FixInt{bits: 64, data: FixIntData{opt: val as u64}}
	}

	/// Creates a new `FixInt` with the given bit-width that represents zero.
	///
	/// **Error** Returns `InvalidZeroBitWidth` in case of a given target bit-width of zero.
	#[inline]
	pub fn zero(bits: u32) -> Result<FixInt> {
		match bits {
			0  => Err(Error::from_kind(InvalidZeroBitWidth)),
			1  => Ok(FixInt::from_bool(false)),
			8  => Ok(FixInt::from_u8(0)),
			16 => Ok(FixInt::from_u16(0)),
			32 => Ok(FixInt::from_u32(0)),
			64 => Ok(FixInt::from_u64(0)),
			n  => unimplemented!()
		}
	}

	/// Creates a new `FixInt` with the given bit-width that represents one.
	///
	/// **Error** Returns `InvalidZeroBitWidth` in case of a given target bit-width of zero.
	#[inline]
	pub fn one(bits: u32) -> Result<FixInt> {
		match bits {
			0  => Err(Error::from_kind(InvalidZeroBitWidth)),
			8  => Ok(FixInt::from_u8(1)),
			16 => Ok(FixInt::from_u16(1)),
			32 => Ok(FixInt::from_u32(1)),
			64 => Ok(FixInt::from_u64(1)),
			n  => unimplemented!()
		}
	}

	/// Creates a new `FixInt` with the given bit-width that has all bits set.
	///
	/// **Error** Returns `InvalidZeroBitWidth` in case of a given target bit-width of zero.
	#[inline]
	pub fn zeroes(bits: u32) -> Result<FixInt> {
		match bits {
			0  => Err(Error::from_kind(InvalidZeroBitWidth)),
			1  => Ok(FixInt::from_bool(false)),
			8  => Ok(FixInt::from_u8(0x00)),
			16 => Ok(FixInt::from_u16(0x0000)),
			32 => Ok(FixInt::from_u32(0x0000_0000)),
			64 => Ok(FixInt::from_u64(0x0000_0000_0000_0000)),
			n  => unimplemented!()
		}
	}

	/// Creates a new `FixInt` with the given bit-width that has all bits set.
	///
	/// **Error** Returns `InvalidZeroBitWidth` in case of a given target bit-width of zero.
	#[inline]
	pub fn ones(bits: u32) -> Result<FixInt> {
		match bits {
			0  => Err(Error::from_kind(InvalidZeroBitWidth)),
			1  => Ok(FixInt::from_bool(true)),
			8  => Ok(FixInt::from_u8(0xFF)),
			16 => Ok(FixInt::from_u16(0xFFFF)),
			32 => Ok(FixInt::from_u32(0xFFFF_FFFF)),
			64 => Ok(FixInt::from_u64(0xFFFF_FFFF_FFFF_FFFF)),
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
impl FixInt {

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
	/// - The bitwidth of the resulting `FixInt` is infered from the number of valid digits in the input.
	/// - Input may start with `'0'` which may influence the bit-width of the resulting `FixInt`.
	pub fn from_bin_str(bitwidth: TargetBitWidth, binary_str: &str) -> Result<FixInt> {
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
	/// - The bitwidth of the resulting `FixInt` is infered from the number of valid digits in the input.
	/// - Input may start with `'0'` which may influence the bit-width of the resulting `FixInt`.
	pub fn from_dec_str(bitwidth: TargetBitWidth, dec_str: &str) -> Result<FixInt> {
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
	/// - The bitwidth of the resulting `FixInt` is infered from the number of valid digits in the input.
	/// - Input may start with `'0'` which may influence the bit-width of the resulting `FixInt`.
	pub fn from_hex_str(bitwidth: TargetBitWidth, hex_str: &str) -> Result<FixInt> {
		unimplemented!();
	}

}

//  =======================================================================
///  Serialization
/// =======================================================================
impl FixInt {

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
impl FixInt {
	/// Returns the bit-width of this `FixInt`.
	#[inline]
	pub fn bits(&self) -> u32 {
		self.bits
	}

	/// Returns the bit-width of this `FixInt` as `usize`.
	#[inline]
	pub fn len_bits(&self) -> usize {
		self.bits() as usize
	}

	/// Returns the number of bit-blocks used internally for value representation.
	/// 
	/// # Note
	/// 
	/// - This method should not be part of the public interface.
	/// - The returned values are valid for bit-block sizes of 32 bit.
	#[inline]
	fn len_blocks(&self) -> usize {
		((self.len_bits() - 1) / BLOCK_SIZE) + 1
	}

	/// Returns true if this `FixInt` represents the zero (0) value.
	#[inline]
	pub fn is_zero(&self) -> bool {
		use self::FixIntModel::*;
		match self.model() {
			C8(n)  => n == 0,
			C16(n) => n == 0,
			C32(n) => n == 0,
			C64(n) => n == 0,
			Var(ref bc) => unimplemented!()
		}
	}

	/// Returns true if this `FixInt` represents the one (1) value.
	#[inline]
	pub fn is_one(&self) -> bool {
		use self::FixIntModel::*;
		match self.model() {
			C8(n)  => n == 1,
			C16(n) => n == 1,
			C32(n) => n == 1,
			C64(n) => n == 1,
			Var(ref bc) => unimplemented!()
		}
	}

	/// Returns true if all bits of this `FixInt` are `1` (one).
	#[inline]
	pub fn is_ones(&self) -> bool {
		use self::FixIntModel::*;
		match self.model() {
			C8(n)  => n == 0xFF,
			C16(n) => n == 0xFFFF,
			C32(n) => n == 0xFFFF_FFFF,
			C64(n) => n == 0xFFFF_FFFF_FFFF_FFFF,
			Var(ref bc) => unimplemented!()
		}
	}

	/// Returns true if no bits of this `FixInt` are `0` (zero).
	#[inline]
	pub fn is_zeros(&self) -> bool {
		self.is_zero()
	}

	/// Returns the number of ones in the binary representation of this `FixInt`.
	pub fn count_ones(&self) -> usize {
		use self::FixIntModel::*;
		match self.model() {
			C8(n)  => n.count_ones() as usize,
			C16(n) => n.count_ones() as usize,
			C32(n) => n.count_ones() as usize,
			C64(n) => n.count_ones() as usize,
			Var(ref bc) => unimplemented!()
		}
	}

	/// Returns the number of zeroes in the binary representation of this `FixInt`.
	pub fn count_zeros(&self) -> usize {
		use self::FixIntModel::*;
		match self.model() {
			C8(n)  => n.count_zeros() as usize,
			C16(n) => n.count_zeros() as usize,
			C32(n) => n.count_zeros() as usize,
			C64(n) => n.count_zeros() as usize,
			Var(ref bc) => unimplemented!()
		}
	}

	/// Returns the number of leading zeroes in the binary representation of this `FixInt`.
	pub fn leading_zeros(&self) -> usize {
		use self::FixIntModel::*;
		match self.model() {
			C8(n)  => n.leading_zeros() as usize,
			C16(n) => n.leading_zeros() as usize,
			C32(n) => n.leading_zeros() as usize,
			C64(n) => n.leading_zeros() as usize,
			Var(ref bc) => unimplemented!()
		}
	}

	/// Returns the number of trailing zeroes in the binary representation of this `FixInt`.
	pub fn trailing_zeroes(&self) -> usize {
		use self::FixIntModel::*;
		match self.model() {
			C8(n)  => n.trailing_zeros() as usize,
			C16(n) => n.trailing_zeros() as usize,
			C32(n) => n.trailing_zeros() as usize,
			C64(n) => n.trailing_zeros() as usize,
			Var(ref bc) => unimplemented!()
		}
	}

	/// Returns `true` if and only if `self == 2^k` for some `k`.
	pub fn is_power_of_two(&self) -> bool {
		self.count_ones() == 1
	}
}

//  =======================================================================
///  Bit-level getters and setters
/// =======================================================================
impl FixInt {

	/// Returns `true` if the bit at the `n`th position is set, else `false`.
	/// 
	/// #Panics
	/// 
	/// If `n` is out of bounds.
	pub fn get(&self, n: usize) -> bool {
		if n >= self.len_bits() {
			panic!("FixInt::get({:?}) is out of bounds of instance with {:?} bits.", n, self.bits())
		}
		unimplemented!()
		// match self.data {
		// 	_1(v)  => v,
		// 	_8(v)  => ((v >> n) & 0x01) == 1,
		// 	_16(v) => ((v >> n) & 0x01) == 1,
		// 	_32(v) => ((v >> n) & 0x01) == 1,
		// 	_64(v) => ((v >> n) & 0x01) == 1,
		// 	Dyn(ref v) => unimplemented!()
		// }
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
			panic!("FixInt::set({:?}) is out of bounds of instance with {:?} bits.", n, self.bits())
		}
		unimplemented!()
		// match self.data {
		// 	_1(ref mut v)  => *v  = true,
		// 	_8(ref mut v)  => *v |= 0x01 << n,
		// 	_16(ref mut v) => *v |= 0x01 << n,
		// 	_32(ref mut v) => *v |= 0x01 << n,
		// 	_64(ref mut v) => *v |= 0x01 << n,
		// 	Dyn(ref mut v) => unimplemented!()
		// }
	}

	/// Unsets the bit at the `n`th position to `0`.
	/// 
	/// #Panics
	/// 
	/// If `n` is out of bounds.
	pub fn unset(&mut self, n: usize) {
		if n >= self.len_bits() {
			panic!("FixInt::unset({:?}) is out of bounds of instance with {:?} bits.", n, self.bits())
		}
		// match self.data {
		// 	_1(ref mut v)  => *v  = false,
		// 	_8(ref mut v)  => *v &= !(0x01 << n),
		// 	_16(ref mut v) => *v &= !(0x01 << n),
		// 	_32(ref mut v) => *v &= !(0x01 << n),
		// 	_64(ref mut v) => *v &= !(0x01 << n),
		// 	Dyn(ref mut v) => unimplemented!()
		// }
	}

	/// Flips the bit at the `n`th position.
	/// 
	/// #Panics
	/// 
	/// If `n` is out of bounds.
	pub fn flip(&mut self, n: usize) {
		if n >= self.len_bits() {
			panic!("FixInt::flip({:?}) is out of bounds of instance with {:?} bits.", n, self.bits())
		}
		// match self.data {
		// 	_1(ref mut v)  => *v  = !*v,
		// 	_8(ref mut v)  => *v ^= 0x01 << n,
		// 	_16(ref mut v) => *v ^= 0x01 << n,
		// 	_32(ref mut v) => *v ^= 0x01 << n,
		// 	_64(ref mut v) => *v ^= 0x01 << n,
		// 	Dyn(ref mut v) => unimplemented!()
		// }
	}

}

//  =======================================================================
///  Relational Operations
/// =======================================================================
impl FixInt {

	/// Unsigned less-than comparison with the other bitvec.
	pub fn ult(&self, other: &FixInt) -> bool {
		unimplemented!()
		// match (self.repr, other.repr) {

		// 	// one of them is undef
		// 	(Undef, _) | (_, Undef) => {
		// 		panic!("FixInt::ult(): Cannot decide this information on undefined representant!")
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
	pub fn ule(&self, other: &FixInt) -> bool {
		!(other.ult(self))
	}

	/// Unsigned greater-than comparison with the other bitvec.
	pub fn ugt(&self, other: &FixInt) -> bool {
		other.ult(self)
	}

	/// Unsigned greater-than-or-equals comparison with the other bitvec.
	pub fn uge(&self, other: &FixInt) -> bool {
		!(self.ult(other))
	}

	/// Signed less-than comparison with the other bitvec.
	pub fn slt(&self, other: &FixInt) -> bool {
		unimplemented!()
		// match (self.repr, other.repr) {

		// 	// one of them is undef
		// 	(Undef, _) | (_, Undef) => {
		// 		panic!("FixInt::slt(): Cannot decide this information on undefined representant!")
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
	pub fn sle(&self, other: &FixInt) -> bool {
		!(other.slt(self))
	}

	/// Signed greater-than comparison with the other bitvec.
	pub fn sgt(&self, other: &FixInt) -> bool {
		other.slt(self)
	}

	/// Signed greater-than-or-equals comparison with the other bitvec.
	pub fn sge(&self, other: &FixInt) -> bool {
		!(self.slt(other))
	}

}

//  =======================================================================
///  Extend & Truncate Operations
/// =======================================================================
impl FixInt {

	/// Creates a new `FixInt` that represents this `FixInt` truncated to 
	/// the given amount of bits.
	///
	/// # Panics
	/// 
	/// - If `bits` is greater than the `FixInt`'s current bit-width.
	/// - If `bits` is zero (`0`).
	/// 
	/// # Note
	/// 
	/// Equal to a call to `clone()` if `bits` is equal to this `FixInt`'s bit-width.
	pub fn truncate(&self, bits: usize) -> Self {
		unimplemented!();
	}

	/// Creates a new `FixInt` that represents the zero-extension of this `FixInt` to the given bits.
	///
	/// # Semantics (from LLVM)
	/// 
	/// The zext fills the high order bits of the value with zero bits until it reaches the size of the destination bit-width.
	/// When zero extending from `i1`, the result will always be either `0` or `1`.
	/// 
	/// # Panics
	/// 
	/// - If `bits` is less than the `FixInt`'s current bit-width.
	/// 
	/// # Note
	/// 
	/// Equal to a call to `clone()` if `bits` is equal to this `FixInt`'s bit-width.
	pub fn zext(&self, bits: usize) -> Self {
		unimplemented!();
	}

	/// Creates a new `FixInt` that represents the sign-extension of this `FixInt` to the given bits.
	/// 
	/// 
	/// # Semantic (from LLVM)
	/// 
	/// The ‘sext‘ instruction performs a sign extension by copying the sign bit (highest order bit) of the value until it reaches the target bit-width.
	/// When sign extending from `i1`, the extension always results in `-1` or `0`.
	///
	/// # Panics
	/// 
	/// - If `bits` is less than the `FixInt`'s current bit-width.
	/// 
	/// # Note
	/// 
	/// Equal to a call to `clone()` if `bits` is equal to this `FixInt`'s bit-width.
	pub fn sext(&self, bits: usize) -> Self {
		unimplemented!();
	}

}
