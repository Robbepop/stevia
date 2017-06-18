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
			UNDEF_MARKER => Bits::Undef,
			mask if mask & POISON_MARKER != 0 => Bits::Poison,
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
	/// Inline, on-stack data when bits in bitvector is less than `INLINE_BITS`
	inl: Block,
	/// Inline, on-heap data for any sizes of bits in bitvector
	ext: Unique<Block>
}

union Block {
	/// Signed variant for native signed operations
	s: i64,
	/// Unsigned variant for native unsigned operations
	u: u64
}

impl Block {
	/// Creates a new block from the given `i64`.
	#[inline]
	pub fn from_i64(val: i64) -> Block {
		Block{s: val}
	}

	/// Creates a new block from the given `u64`.
	#[inline]
	pub fn from_u64(val: u64) -> Block {
		Block{u: val}
	}
}

//  =======================================================================
///  Constructors
/// =======================================================================
impl BitVec {

	/// Creates a new bitvector that represents an undefined state.
	#[inline]
	pub fn undef() -> BitVec {
		BitVec{bits: UNDEF_MARKER, data: BitVecData{inl: Block::from_u64(0)}}
	}

	/// Creates a new bitvector from the given `u32`.
	#[inline]
	pub fn from_u32(val: u32) -> BitVec {
		BitVec{bits: 32, data: BitVecData{inl: Block::from_u64(val as u64)}}
	}

	/// Creates a new bitvector from the given `u64`.
	#[inline]
	pub fn from_u64(val: u64) -> BitVec {
		BitVec{bits: 64, data: BitVecData{inl: Block::from_u64(val)}}
	}

	/// Creates a new bitvector from the given `i32`.
	#[inline]
	pub fn from_i32(val: i32) -> BitVec {
		BitVec{bits: 32, data: BitVecData{inl: Block::from_i64(val as i64)}}
	}

	/// Creates a new bitvector from the given `i64`.
	#[inline]
	pub fn from_i64(val: i64) -> BitVec {
		BitVec{bits: 64, data: BitVecData{inl: Block::from_i64(val)}}
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

	/// Returns the number of bits of this bitvector.
	pub fn len(&self) -> usize {
		self.bits() as usize
	}

	pub fn bits(&self) -> u32 {
		self.bits & 0xA000_0000
	}

	/// Returns true if this bitvector represents an undefined state.
	pub fn is_undef(&self) -> bool {
		self.bits == UNDEF_MARKER
	}

	/// Returns true if this bitvector represents a poison value.
	pub fn is_poison(&self) -> bool {
		(self.bits & POISON_MARKER) != 0
	}

	/// Returns true if all bits of this bitvector are zero.
	pub fn is_zeroes(&self) -> bool {
		if self.bits <= INLINE_BITS {
			unsafe{self.data.inl.u == 0}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if all bits of this bitvector are one.
	pub fn is_ones(&self) -> bool {
		if self.bits <= INLINE_BITS {
			unsafe{self.data.inl.u == 0xFFFF_FFFF_FFFF_FFFF}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if this bitvector represents the number zero (`0`).
	pub fn is_zero(&self) -> bool {
		if self.bits <= INLINE_BITS {
			unsafe{self.data.inl.u == 0}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if this bitvector represents the number one (`1`).
	pub fn is_one(&self) -> bool {
		if self.bits <= INLINE_BITS {
			unsafe{self.data.inl.u == 1}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if this bitvector represents an even number.
	pub fn is_even(&self) -> bool {
		if self.bits <= INLINE_BITS {
			unsafe{self.data.inl.u.is_even()}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if this bitvector represents an odd number-
	pub fn is_odd(&self) -> bool {
		if self.bits <= INLINE_BITS {
			unsafe{self.data.inl.u.is_odd()}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if this bitvector may represent a positive number in twos complement.
	pub fn is_positive(&self) -> bool {
		if self.bits <= INLINE_BITS {
			unsafe{self.data.inl.s.is_positive()}
		}
		else {
			unimplemented!();
		}
	}

	/// Returns true if this bitvector may represent a negative number in twos complement.
	pub fn is_negative(&self) -> bool {
		if self.bits <= INLINE_BITS {
			unsafe{self.data.inl.s.is_negative()}
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
		if self.bits <= INLINE_BITS {
			unsafe{((self.data.inl.u >> n) & 0x01) == 1}
		}
		else {
			unimplemented!();
		}
	}

	/// Sets the bit at the `n`th position to `1`.
	/// 
	/// Returns the value of the bit before this operation.
	pub fn set(&mut self, n: usize) {
		if self.bits <= INLINE_BITS {
			unsafe{self.data.inl.u |= 0x01 << n}
		}
		else {
			unimplemented!();
		}
	}

	/// Unsets the bit at the `n`th position to `0`.
	pub fn unset(&mut self, n: usize) {
		if self.bits <= INLINE_BITS {
			unsafe{self.data.inl.u &= !(0x01 << n)}
		}
		else {
			unimplemented!();
		}
	}

	/// Flips the bit at the `n`th position.
	pub fn flip(&mut self, n: usize) {
		if self.bits <= INLINE_BITS {
			unsafe{self.data.inl.u ^= 0x01 << n}
		}
		else {
			unimplemented!();
		}
	}

}

//  =======================================================================
///  Relational Operations
/// =======================================================================
impl BitVec {

	/// Unsigned less-than comparison with the other bitvec.
	pub fn ult(&self, other: &BitVec) -> bool {
		match (self.bits, other.bits) {

			// both inline
			(l, r) if l <= INLINE_BITS && r <= INLINE_BITS => {
				unsafe{self.data.inl.u < other.data.inl.u}
			}

			// left inline, right extern
			(l, r) if l <= INLINE_BITS && r >  INLINE_BITS => {
				unimplemented!();
			}

			// left extern, right inline
			(l, r) if l >  INLINE_BITS && r <= INLINE_BITS => {
				unimplemented!();
			}

			// both extern
			_ => {
				unimplemented!();
			}

		}
	}

	/// Unsigned less-than-or-equals comparison with the other bitvec.
	pub fn ule(&self, other: &BitVec) -> bool {
		!(other.ult(self))
	}

	/// Unsigned greater-than comparison with the other bitvec.
	pub fn ugt(&self, other: &BitVec) -> bool {
		other.ult(self)
	}

	/// Unsigned greater-than-or-equals comparison with the other bitvec.
	pub fn uge(&self, other: &BitVec) -> bool {
		!(self.ult(other))
	}

	/// Signed less-than comparison with the other bitvec.
	pub fn slt(&self, other: &BitVec) -> bool {
		match (self.bits, other.bits) {

			// both inline
			(l, r) if l <= INLINE_BITS && r <= INLINE_BITS => {
				unsafe{self.data.inl.s < other.data.inl.s}
			}

			// left inline, right extern
			(l, r) if l <= INLINE_BITS && r >  INLINE_BITS => {
				unimplemented!();
			}

			// left extern, right inline
			(l, r) if l >  INLINE_BITS && r <= INLINE_BITS => {
				unimplemented!();
			}

			// both extern
			_ => {
				unimplemented!();
			}

		}
	}

	/// Signed less-than-or-equals comparison with the other bitvec.
	pub fn sle(&self, other: &BitVec) -> bool {
		!(other.slt(self))
	}

	/// Signed greater-than comparison with the other bitvec.
	pub fn sgt(&self, other: &BitVec) -> bool {
		other.slt(self)
	}

	/// Signed greater-than-or-equals comparison with the other bitvec.
	pub fn sge(&self, other: &BitVec) -> bool {
		!(self.slt(other))
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
