#![feature(untagged_unions)]
#![feature(unique)]

#![allow(dead_code)]
#![allow(unused_variables)]

extern crate num;

use num::Integer;

use std::ptr::Unique;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorKind {
	InvalidBinaryStr(String),
	InvalidDecimalStr(String),
	InvalidHexStr(String),
	UnmatchingBitwidth(u32, u32),
	InvalidBitWidthArgument(u32)
}
use ErrorKind::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Error(ErrorKind);

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Bits {
	Undef,
	Poison,
	N(u32)
}
use Bits::*;

impl From<u32> for Bits {
	fn from(val: u32) -> Bits {
		match val {
			0 => Bits::Undef,
			0xFFFF_FFFF => Bits::Poison,
			n => Bits::N(n)
		}
	}
}

impl From<Bits> for u32 {
	fn from(bits: Bits) -> u32 {
		match bits {
			Undef => 0,
			Poison => 0xFFFF_FFFF,
			N(n) => n
		}
	}
}

const INLINE_BITS  : u32 = 64;

const UNDEF_MARKER : u32 = 0;
const POISON_MARKER: u32 = 0xFFFF_FFFF;

pub struct BitVec {
	/// Number of bits used by this bitvector.
	/// 
	/// Note that the actual memory consumption may be larger.
	bits: u32,
	/// The bits for this bitvector.
	data: BitVecData
}

union BitVecData {
	/// Inline, unsigned native operations on the bitvector.
	uinl: u64,
	/// Inline, signed native operations on the bitvector.
	sinl: i64,
	/// Extern, unsigned operations on the bitvector.
	uext: Unique<u64>,
	/// Extern, signed operations on the bitvector.
	sext: Unique<i64>
}

//  =======================================================================
///  Constructors
/// =======================================================================
impl BitVec {

	/// Creates a new bitvector that represents an undefined state.
	#[inline]
	pub fn undef() -> BitVec {
		BitVec{bits: UNDEF_MARKER, data: BitVecData{uinl: 0}}
	}

	/// Creates a new bitvector that represents a poison value.
	#[inline]
	pub fn poison() -> BitVec {
		BitVec{bits: POISON_MARKER, data: BitVecData{uinl: 0}}
	}

	/// Creates a new bitvector from the given `u32`.
	#[inline]
	pub fn from_u32(val: u32) -> BitVec {
		BitVec{bits: 32, data: BitVecData{uinl: val as u64}}
	}

	/// Creates a new bitvector from the given `u64`.
	#[inline]
	pub fn from_u64(val: u64) -> BitVec {
		BitVec{bits: 64, data: BitVecData{uinl: val}}
	}

	/// Creates a bitvector with `bits` bits that are all set to `0`.
	#[inline]
	pub fn zeroes<B>(bits: B) -> Result<BitVec>
		where B: Into<Bits> + Copy
	{
		match bits.into() {
			Undef | Poison => {
				Err(Error(InvalidBitWidthArgument(bits.into().into())))
			}
			N(n) if n <= INLINE_BITS => {
				Ok(BitVec::from_u64(0x0000_0000_0000_0000))
			}
			N(_) => {
				unimplemented!()
			}
		}
	}

	/// Creates a bitvector with `bits` bits that are all set to `1`.
	#[inline]
	pub fn ones<B>(bits: B) -> Result<BitVec>
		where B: Into<Bits> + Copy
	{
		match bits.into() {
			Undef | Poison => {
				Err(Error(InvalidBitWidthArgument(bits.into().into())))
			}
			N(n) if n <= INLINE_BITS => {
				Ok(BitVec::from_u64(0xFFFF_FFFF_FFFF_FFFF))
			}
			N(_) => {
				unimplemented!()
			}
		}
	}

	/// Creates a bitvector with `bits` bits and fills it with the given bit-pattern.
	pub fn from_pattern<B>(bits: B, pattern: u64) -> Result<BitVec>
		where B: Into<Bits> + Copy
	{
		match bits.into() {
			Undef | Poison => {
				Err(Error(InvalidBitWidthArgument(bits.into().into())))
			}
			N(n) if n <= INLINE_BITS => {
				Ok(BitVec::from_u64(pattern))
			}
			N(_) => {
				unimplemented!()
			}
		}
	}

}

//  =======================================================================
///  Deserialization
/// =======================================================================
impl BitVec {

	/// Creates a new bitvector from the given binary string representation.
	pub fn from_bin_str(binary_str: &str) -> Result<BitVec> {
		unimplemented!();
	}

	/// Creates a new bitvector from the given binary string representation.
	pub fn from_dec_str(dec_str: &str) -> Result<BitVec> {
		unimplemented!();
	}

	/// Creates a new bitvector from the given binary string representation.
	pub fn from_hex_str(hex_str: &str) -> Result<BitVec> {
		unimplemented!();
	}

}

//  =======================================================================
///  Serialization
/// =======================================================================
impl BitVec {

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
///  Utility methods
/// =======================================================================
impl BitVec {

	/// Returns true if this bitvector represents an undefined state.
	pub fn is_undef(&self) -> bool {
		self.bits == 0
	}

	/// Returns true if this bitvector represents a poison value.
	pub fn is_poison(&self) -> bool {
		(self.bits & 0xA000_0000) != 0
	}

	/// Returns true if all bits of this bitvector are zero.
	pub fn is_zeroes(&self) -> bool {
		if self.bits < INLINE_BITS {
			unsafe{self.data.uinl == 0}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if all bits of this bitvector are one.
	pub fn is_ones(&self) -> bool {
		if self.bits < INLINE_BITS {
			unsafe{self.data.uinl == 0xFFFF_FFFF_FFFF_FFFF}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if this bitvector represents the number zero (`0`).
	pub fn is_zero(&self) -> bool {
		if self.bits < INLINE_BITS {
			unsafe{self.data.uinl == 0}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if this bitvector represents the number one (`1`).
	pub fn is_one(&self) -> bool {
		if self.bits < INLINE_BITS {
			unsafe{self.data.uinl.is_one()}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if this bitvector represents an even number.
	pub fn is_even(&self) -> bool {
		if self.bits < INLINE_BITS {
			unsafe{self.data.uinl.is_even()}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if this bitvector represents an odd number-
	pub fn is_odd(&self) -> bool {
		if self.bits < INLINE_BITS {
			unsafe{self.data.uinl.is_odd()}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if this bitvector may represent a positive number in twos complement.
	pub fn is_positive(&self) -> bool {
		if self.bits < INLINE_BITS {
			unsafe{self.data.sinl.is_positive()}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if this bitvector may represent a negative number in twos complement.
	pub fn is_negative(&self) -> bool {
		if self.bits < INLINE_BITS {
			unsafe{self.data.sinl.is_negative()}
		}
		else {
			unimplemented!();
		}
	}

}

//  =======================================================================
///  Bit-level getters and setters
/// =======================================================================
impl BitVec {

	/// Returns `true` if the bit at the `n`th position is set, else `false`.
	pub fn get(&self, n: usize) -> bool {
		if self.bits < INLINE_BITS {
			unsafe{self.data.uinl >> n == 1}
		}
		else {
			unimplemented!();
		}
	}

	/// Sets the bit at the `n`th position to `1`.
	/// 
	/// Returns the value of the bit before this operation.
	pub fn set(&mut self, n: usize) -> bool {
		unimplemented!();
	}

	/// Unsets the bit at the `n`th position to `0`.
	pub fn unset(&mut self, n: usize) -> bool {
		unimplemented!();
	}

	/// Flips the bit at the `n`th position.
	pub fn flip(&mut self, n: usize) -> bool {
		unimplemented!();
	}

}

//  =======================================================================
///  Relational Operations
/// =======================================================================
impl BitVec {

	/// Unsigned less-than comparison with the other bitvec.
	pub fn ult(&self, other: &BitVec) -> bool {
		unimplemented!();
	}

	/// Unsigned less-than-or-equals comparison with the other bitvec.
	pub fn ule(&self, other: &BitVec) -> bool {
		unimplemented!();
	}

	/// Unsigned greater-than comparison with the other bitvec.
	pub fn ugt(&self, other: &BitVec) -> bool {
		unimplemented!();
	}

	/// Unsigned greater-than-or-equals comparison with the other bitvec.
	pub fn uge(&self, other: &BitVec) -> bool {
		unimplemented!();
	}

	/// Signed less-than comparison with the other bitvec.
	pub fn slt(&self, other: &BitVec) -> bool {
		unimplemented!();
	}

	/// Signed less-than-or-equals comparison with the other bitvec.
	pub fn sle(&self, other: &BitVec) -> bool {
		unimplemented!();
	}

	/// Signed greater-than comparison with the other bitvec.
	pub fn sgt(&self, other: &BitVec) -> bool {
		unimplemented!();
	}

	/// Signed greater-than-or-equals comparison with the other bitvec.
	pub fn sge(&self, other: &BitVec) -> bool {
		unimplemented!();
	}

}

//  =======================================================================
///  Arithmetic Operations
/// =======================================================================
impl BitVec {

	/// Creates a new bitvec that represents the negation of the given bitvector.
	pub fn neg(&self) -> BitVec {
		unimplemented!();
	}

	/// Negates the given bitvector.
	pub fn neg_assign(&mut self) {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the signed addition of both given bitvectors.
	pub fn sadd(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the unsigned addition of both given bitvectors.
	pub fn uadd(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the signed subtraction of both given bitvectors.
	pub fn ssub(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the signed subtraction of both given bitvectors.
	pub fn usub(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the multiplication of both given bitvectors.
	pub fn mul(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the unsigned multiplication of both given bitvectors.
	pub fn udiv(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the signed multiplication of both given bitvectors.
	pub fn sdiv(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the unsigned remainder of both given bitvectors.
	pub fn urem(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the signed remainder of both given bitvectors.
	pub fn srem(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

}

//  =======================================================================
///  Shift Operations
/// =======================================================================
impl BitVec {

	/// Creates a new bitvec that represents the result of this bitvector left-shifted by the other one.
	pub fn shl(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Left-shifts self by other and stores the result back into self.
	pub fn shl_assign(&mut self, other: &BitVec) {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the result of this bitvector logically right-shifted by the other one.
	pub fn lshr(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Logically right-shifts self by other and stores the result back into self.
	pub fn lshr_assign(&mut self, other: &BitVec) {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the result of this bitvector arithmetically right-shifted by the other one.
	pub fn ashr(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Arthimetically right-shifts self by other and stores the result back into self.
	pub fn ashr_assign(&mut self, other: &BitVec) {
		unimplemented!();
	}

}

//  =======================================================================
///  Bitwise Operations
/// =======================================================================
impl BitVec {

	/// Creates a new bitvev that represents the bitwise-not of the given bitvector.
	pub fn bitnot(&self) -> BitVec {
		unimplemented!();
	}

	/// Flip all bits of the given bitvector inplace.
	pub fn bitnot_assign(&mut self) {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the bitwise-and of both given bitvectors.
	pub fn bitand(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Computes bitwise-and of self and other and stores the result in self.
	pub fn bitand_assign(&mut self, other: &BitVec) {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the bitwise-or of both given bitvectors.
	pub fn bitor(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Computes bitwise-or of self and other and stores the result in self.
	pub fn bitor_assign(&mut self, other: &BitVec) {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the bitwise-xor of both given bitvectors.
	pub fn bitxor(&self, other: &BitVec) -> BitVec {
		unimplemented!();
	}

	/// Computes bitwise-xor of self and other and stores the result in self.
	pub fn bitxor_assign(&mut self, other: &BitVec) {
		unimplemented!();
	}

}

//  =======================================================================
///  Extend & Truncate Operations
/// =======================================================================
impl BitVec {

	/// Creates a new bitvec that represents the truncation of this bitvector to the given bits.
	pub fn trunc(&self, bits: usize) -> BitVec {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the zero-extension of this bitvector to the given bits.
	pub fn zext(&self, bits: usize) -> BitVec {
		unimplemented!();
	}

	/// Creates a new bitvec that represents the sign-extension of this bitvector to the given bits.
	pub fn sext(&self, bits: usize) -> BitVec {
		unimplemented!();
	}

}
