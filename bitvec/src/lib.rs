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

use num::Integer;

use std::ptr::Unique;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorKind {
	InvalidBinaryStr(String),
	InvalidDecimalStr(String),
	InvalidHexStr(String),
	UnmatchingBitwidth(u32, u32),
	InvalidZeroBitWidth,
	InvalidBitWidthArgument(u32),
	InvalidUndefOperation(Operation)
}
use ErrorKind::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Operation {
	UnsignedLessThan,
	SignedLessThan
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Error(ErrorKind);

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Storage {
	/// The value is stored inline on the stack within the bitvec.
	Inline,
	/// The value is stored on the heap outside the bitvec.
	Extern
}
use Storage::*;

/// A representant used to controle the behaviour of bitvectors.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Repr {
	/// Representant for an undefined value.
	Undef,
	/// Representant for a poisoned value with bits.
	Poison(u32),
	/// Representant for a normal value with bits.
	Normal(u32)
}
use Repr::*;

impl Repr {
	/// Returns true if this `Repr` represents undefinedness.
	#[inline]
	fn is_undef(self) -> bool {
		match self {
			Repr::Undef => true,
			_           => false
		}
	}

	/// Returns true if this `Repr` represents a poisoned value.
	#[inline]
	fn is_poison(self) -> bool {
		match self {
			Repr::Poison(_) => true,
			_               => false
		}
	}

	/// Returns true if this `Repr` represents a normal value.
	#[inline]
	fn is_normal(self) -> bool {
		match self {
			Repr::Normal(_) => true,
			_               => false
		}
	}

	/// Returns true if this `Repr` represents a bitvec that stores its data inplace on the stack.
	#[inline]
	fn is_small(self) -> bool {
		self.bits() <= INLINE_BITS
	}

	/// Returns the storage properties of this representant.
	#[inline]
	fn storage(self) -> Storage {
		match self.is_small() {
			true  => Inline,
			false => Extern
		}
	}

	/// Returns the number of bits that are associated with this `Repr`.
	#[inline]
	fn bits(self) -> u32 {
		match self {
			Repr::Undef        => UNDEF_BITS,
			Repr::Poison(bits) => bits,
			Repr::Normal(bits) => bits
		}
	}

	/// Creates a `Repr` from a given number of bits.
	#[inline]
	fn from_u32(val: u32) -> Self {
		match val {
			0 => Repr::Undef,
			n if n >= POISON_MARKER => Repr::Poison(n - POISON_MARKER),
			n => Repr::Normal(n)
		}
	}
}

impl From<u32> for Repr {
	fn from(val: u32) -> Repr {
		Repr::from_u32(val)
	}
}

const INLINE_BITS  : u32 = 64;

const UNDEF_BITS : u32 = 0;
const POISON_MARKER: u32 = 0xA000_0000;

pub struct BitVec {
	/// Number of bits used by this bitvector.
	/// 
	/// Note that the actual memory consumption may be larger.
	repr: Repr,
	/// The bits for this bitvector.
	data: BitVecData
}

/// A bitvec data that either stores a single block on the stack or a contiguous sequence of blocks on the heap.
union BitVecData {
	/// Inline, on-stack data when bits in bitvector is less than `INLINE_BITS`
	inl: Block,
	/// Inline, on-heap data for any sizes of bits in bitvector
	ext: Unique<Block>
}

/// A block that is either a signed or an unsigned 64-bit integer.
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
		BitVec{repr: Repr::Undef, data: BitVecData{inl: Block::from_u64(0)}}
	}

	/// Creates a new bitvector from the given `u32`.
	#[inline]
	pub fn from_u32(val: u32) -> BitVec {
		BitVec{repr: Repr::Normal(32), data: BitVecData{inl: Block::from_u64(val as u64)}}
	}

	/// Creates a new bitvector from the given `u64`.
	#[inline]
	pub fn from_u64(val: u64) -> BitVec {
		BitVec{repr: Repr::Normal(64), data: BitVecData{inl: Block::from_u64(val)}}
	}

	/// Creates a new bitvector from the given `i32`.
	#[inline]
	pub fn from_i32(val: i32) -> BitVec {
		BitVec{repr: Repr::Normal(32), data: BitVecData{inl: Block::from_i64(val as i64)}}
	}

	/// Creates a new bitvector from the given `i64`.
	#[inline]
	pub fn from_i64(val: i64) -> BitVec {
		BitVec{repr: Repr::Normal(64), data: BitVecData{inl: Block::from_i64(val)}}
	}

	/// Creates a bitvector with `bits` bits that are all set to `0`.
	#[inline]
	pub fn zeroes<B>(bits: u32) -> Result<BitVec> {
		match Repr::from_u32(bits) {
			Undef => {
				Err(Error(InvalidZeroBitWidth))
			}
			repr if repr.is_small() => {
				Ok(BitVec::from_u64(0x0000_0000_0000_0000))
			}
			Poison(bits) | Normal(bits) => {
				unimplemented!()
			}
		}
	}

	/// Creates a bitvector with `bits` bits that are all set to `1`.
	#[inline]
	pub fn ones<B>(bits: u32) -> Result<BitVec> {
		match Repr::from_u32(bits) {
			Undef => {
				Err(Error(InvalidZeroBitWidth))
			}
			repr if repr.is_small() => {
				Ok(BitVec::from_u64(0xFFFF_FFFF_FFFF_FFFF))
			}
			Poison(bits) | Normal(bits) => {
				unimplemented!()
			}
		}
	}

	/// Creates a bitvector with `bits` bits and fills it with the given bit-pattern.
	pub fn from_pattern<T>(repr: T, pattern: u64) -> Result<BitVec>
		where T: Into<Repr>
	{
		match repr.into() {
			Undef => {
				Err(Error(InvalidZeroBitWidth))
			}
			repr if repr.is_small() => {
				Ok(BitVec::from_u64(pattern))
			}
			Poison(bits) | Normal(bits) => {
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
		self.repr.bits()
	}

	/// Returns true if this bitvector represents an undefined state.
	pub fn is_undef(&self) -> bool {
		self.repr.is_undef()
	}

	/// Returns true if this bitvector represents a poison value.
	pub fn is_poison(&self) -> bool {
		self.repr.is_poison()
	}

	/// Returns true if all bits of this bitvector are zero.
	/// 
	/// Panics if this bitvec represents an undefined value.
	pub fn is_zeroes(&self) -> bool {
		match self.repr {
			Undef => {
				panic!("BitVec::is_zeroes(): Cannot decide this information on undefined representant!")
			}
			repr if repr.is_small() => {
				unsafe{self.data.inl.u == 0}
			}
			_ => {
				unimplemented!()
			}
		}
	}

	/// Returns true if all bits of this bitvector are one.
	pub fn is_ones(&self) -> bool {
		match self.repr {
			Undef => {
				panic!("BitVec::is_ones(): Cannot decide this information on undefined representant!")
			}
			repr if repr.is_small() => {
				unsafe{self.data.inl.u == 0xFFFF_FFFF_FFFF_FFFF}
			}
			_ => {
				unimplemented!()
			}
		}
	}

	/// Returns true if this bitvector represents the number zero (`0`).
	pub fn is_zero(&self) -> bool {
		match self.repr {
			Undef => {
				panic!("BitVec::is_zero(): Cannot decide this information on undefined representant!")
			}
			repr if repr.is_small() => {
				unsafe{self.data.inl.u == 0}
			}
			_ => {
				unimplemented!()
			}
		}
	}

	/// Returns true if this bitvector represents the number one (`1`).
	pub fn is_one(&self) -> bool {
		match self.repr {
			Undef => {
				panic!("BitVec::is_one(): Cannot decide this information on undefined representant!")
			}
			repr if repr.is_small() => {
				unsafe{self.data.inl.u == 1}
			}
			_ => {
				unimplemented!()
			}
		}
	}

	/// Returns true if this bitvector represents an even number.
	pub fn is_even(&self) -> bool {
		match self.repr {
			Undef => {
				panic!("BitVec::is_even(): Cannot decide this information on undefined representant!")
			}
			repr if repr.is_small() => {
				unsafe{self.data.inl.u.is_even()}
			}
			_ => {
				unimplemented!()
			}
		}
	}

	/// Returns true if this bitvector represents an odd number-
	pub fn is_odd(&self) -> bool {
		match self.repr {
			Undef => {
				panic!("BitVec::is_odd(): Cannot decide this information on undefined representant!")
			}
			repr if repr.is_small() => {
				unsafe{self.data.inl.u.is_odd()}
			}
			_ => {
				unimplemented!()
			}
		}
	}

	/// Returns true if this bitvector may represent a positive number in twos complement.
	pub fn is_positive(&self) -> bool {
		match self.repr {
			Undef => {
				panic!("BitVec::is_positive(): Cannot decide this information on undefined representant!")
			}
			repr if repr.is_small() => {
				unsafe{self.data.inl.s.is_positive()}
			}
			_ => {
				unimplemented!()
			}
		}
	}

	/// Returns true if this bitvector may represent a negative number in twos complement.
	pub fn is_negative(&self) -> bool {
		match self.repr {
			Undef => {
				panic!("BitVec::is_negative(): Cannot decide this information on undefined representant!")
			}
			repr if repr.is_small() => {
				unsafe{self.data.inl.s.is_negative()}
			}
			_ => {
				unimplemented!()
			}
		}
	}

}

//  =======================================================================
///  Bit-level getters and setters
/// =======================================================================
impl BitVec {

	/// Returns `true` if the bit at the `n`th position is set, else `false`.
	pub fn get(&self, n: usize) -> bool {
		match self.repr {
			Undef => {
				panic!("BitVec::is_negative(): Cannot decide this information on undefined representant!")
			}
			repr if repr.is_small() => {
				unsafe{((self.data.inl.u >> n) & 0x01) == 1}
			}
			_ => {
				unimplemented!()
			}
		}
	}

	/// Sets the bit at the `n`th position to `1`.
	/// 
	/// Returns the value of the bit before this operation.
	pub fn set(&mut self, n: usize) {
		match self.repr {
			Undef => {
				panic!("BitVec::set(): Cannot decide this information on undefined representant!")
			}
			repr if repr.is_small() => {
				unsafe{self.data.inl.u |= 0x01 << n}
			}
			_ => {
				unimplemented!()
			}
		}
	}

	/// Unsets the bit at the `n`th position to `0`.
	pub fn unset(&mut self, n: usize) {
		match self.repr {
			Undef => {
				panic!("BitVec::unset(): Cannot decide this information on undefined representant!")
			}
			repr if repr.is_small() => {
				unsafe{self.data.inl.u &= !(0x01 << n)}
			}
			_ => {
				unimplemented!()
			}
		}
	}

	/// Flips the bit at the `n`th position.
	pub fn flip(&mut self, n: usize) {
		match self.repr {
			Undef => {
				panic!("BitVec::flip(): Cannot decide this information on undefined representant!")
			}
			repr if repr.is_small() => {
				unsafe{self.data.inl.u ^= 0x01 << n}
			}
			_ => {
				unimplemented!()
			}
		}
	}

}

//  =======================================================================
///  Relational Operations
/// =======================================================================
impl BitVec {

	/// Unsigned less-than comparison with the other bitvec.
	pub fn ult(&self, other: &BitVec) -> bool {
		match (self.repr, other.repr) {

			// one of them is undef
			(Undef, _) | (_, Undef) => {
				panic!("BitVec::ult(): Cannot decide this information on undefined representant!")
			}

			// non-undefs
			(l, r) => {
				// match for storage properties
				match (l.storage(), r.storage()) {
					(Inline, Inline) => {
						unsafe{self.data.inl.u < other.data.inl.u}
					}
					(Inline, Extern) => {
						unimplemented!()
					}
					(Extern, Inline) => {
						unimplemented!()
					}
					(Extern, Extern) => {
						unimplemented!()
					}
				}
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
		match (self.repr, other.repr) {

			// one of them is undef
			(Undef, _) | (_, Undef) => {
				panic!("BitVec::slt(): Cannot decide this information on undefined representant!")
			}

			// non-undefs
			(l, r) => {
				// match for storage properties
				match (l.storage(), r.storage()) {
					(Inline, Inline) => {
						unsafe{self.data.inl.s < other.data.inl.s}
					}
					(Inline, Extern) => {
						unimplemented!()
					}
					(Extern, Inline) => {
						unimplemented!()
					}
					(Extern, Extern) => {
						unimplemented!()
					}
				}
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

	/// Consumes this bitvec and returns a bitvec that represents the negation of the original bitvec.
	/// 
	/// Mote: This clones the bitvector.
	pub fn neg(self) -> BitVec {
		match self.repr {
			Undef => {
				self
			}
			repr if repr.is_small() => {
				let mut this = self;
				this.neg_assign();
				this
			}
			_ => {
				unimplemented!()
			}
		}
	}

	/// Negates the given bitvector.
	pub fn neg_assign(&mut self) {
		match self.repr {
			Undef => (),
			repr if repr.is_small() => {
				unsafe{self.data.inl.s = -self.data.inl.s}
			}
			_ => {
				unimplemented!()
			}
		}
	}

	/// Creates a new bitvec that represents the signed addition of both given bitvectors.
	pub fn sadd(&self, other: &BitVec) -> BitVec {
		match (self.repr, other.repr) {

			// one of them is undef
			(Undef, _) | (_, Undef) => {
				panic!("BitVec::slt(): Cannot decide this information on undefined representant!")
			}

			// non-undefs
			(l, r) => {
				// match for storage properties
				match (l.storage(), r.storage()) {
					(Inline, Inline) => {
						let lval = unsafe{ self.data.inl.u};
						let rval = unsafe{other.data.inl.u};
						match lval.overflowing_add(rval) {
							(res, false) => BitVec::from_pattern(self.bits(), res).unwrap(),
							(res, true ) => BitVec::from_pattern(self.bits(), res).unwrap()
						}
					}
					(Inline, Extern) => {
						unimplemented!()
					}
					(Extern, Inline) => {
						unimplemented!()
					}
					(Extern, Extern) => {
						unimplemented!()
					}
				}
			}
		}
	}

	/// Creates a new bitvec that represents the unsigned addition of both given bitvectors.
	pub fn uadd(&self, other: &BitVec) -> BitVec {
		match (self.repr, other.repr) {

			// one of them is undef
			(Undef, _) | (_, Undef) => {
				panic!("BitVec::uadd(): Cannot decide this information on undefined representant!")
				// BitVec::undef()
			}

			// non-undefs
			(l, r) => {
				// match for storage properties
				match (l.storage(), r.storage()) {
					(Inline, Inline) => {
						let lval = unsafe{ self.data.inl.u};
						let rval = unsafe{other.data.inl.u};
						BitVec::from_pattern(self.repr, lval.wrapping_add(rval)).unwrap()
					}
					(Inline, Extern) => {
						unimplemented!()
					}
					(Extern, Inline) => {
						unimplemented!()
					}
					(Extern, Extern) => {
						unimplemented!()
					}
				}
			}
		}
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
