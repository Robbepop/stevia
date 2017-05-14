
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct BitVec {
	/// Number of bits used by this bitvector.
	/// 
	/// Note that the actual memory consumption may be larger.
	bits: u32,
	/// The bits for this bitvector.
	data: BitVecData
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

impl BitVec {
	/// Creates a new bitvector from the given `u32`.
	pub fn from_u32(val: u32) -> BitVec;

	/// Creates a new bitvector from the given `u64`.
	pub fn from_u64(val: u64) -> BitVec;

	/// Creates a new bitvector from the given binary string representation.
	pub fn from_bin_str(binary_str: &str) -> Result<BitVec>;

	/// Creates a new bitvector from the given binary string representation.
	pub fn from_dec_str(dec_str: &str) -> Result<BitVec>;

	/// Creates a new bitvector from the given binary string representation.
	pub fn from_hex_str(hex_str: &str) -> Result<BitVec>;

	/// Returns a string representation of the binary encoded bitvector.
	pub fn to_bin_string(&self) -> String;

	/// Returns a string representation of the decimal encoded bitvector.
	pub fn to_dec_string(&self) -> String;

	/// Returns a string representation of the hex-decimal encoded bitvector.
	pub fn to_hex_string(&self) -> String;

	/// Creates a bitvector with `bits` bits that are all set to `0`.
	pub fn zeroes(bits: usize) -> BitVec;

	/// Creates a bitvector with `bits` bits that are all set to `1`.
	pub fn ones(bits: usize) -> BitVec;

	/// Creates a bitvector with `bits` bits and fills it with the given bit-pattern.
	pub fn pattern(bits: usize, pattern: u64) -> BitVec;

	/// Returns `true` if the bit at the `n`th position is set, else `false`.
	pub fn get(&self, n: usize) -> bool;

	/// Sets the bit at the `n`th position to `1`.
	/// 
	/// Returns the value of the bit before this operation.
	pub fn set(&mut self, n: usize) -> bool;

	/// Unsets the bit at the `n`th position to `0`.
	pub fn unset(&mut self, n: usize) -> bool;

	/// Flips the bit at the `n`th position.
	pub fn flip(&mut self, n: usize) -> bool;

	/// Unsigned less-than comparison with the other bitvec.
	pub fn ult(&self, other: &BitVec) -> bool;
	/// Unsigned less-than-or-equals comparison with the other bitvec.
	pub fn ule(&self, other: &BitVec) -> bool;
	/// Unsigned greater-than comparison with the other bitvec.
	pub fn ugt(&self, other: &BitVec) -> bool;
	/// Unsigned greater-than-or-equals comparison with the other bitvec.
	pub fn uge(&self, other: &BitVec) -> bool;

	/// Signed less-than comparison with the other bitvec.
	pub fn slt(&self, other: &BitVec) -> bool;
	/// Signed less-than-or-equals comparison with the other bitvec.
	pub fn sle(&self, other: &BitVec) -> bool;
	/// Signed greater-than comparison with the other bitvec.
	pub fn sgt(&self, other: &BitVec) -> bool;
	/// Signed greater-than-or-equals comparison with the other bitvec.
	pub fn sge(&self, other: &BitVec) -> bool;

	/// Creates a new bitvec that represents the negation of the given bitvector.
	pub fn neg(&self) -> BitVec;

	/// Negates the given bitvector.
	pub fn neg_assign(&mut self);

	/// Creates a new bitvec that represents the sum of both given bitvectors.
	pub fn add(&self, other: &BitVec) -> BitVec;

	/// Creates a new bitvec that represents the subtraction of both given bitvectors.
	pub fn sub(&self, other: &BitVec) -> BitVec;

	/// Creates a new bitvec that represents the multiplication of both given bitvectors.
	pub fn mul(&self, other: &BitVec) -> BitVec;

	/// Creates a new bitvec that represents the unsigned multiplication of both given bitvectors.
	pub fn udiv(&self, other: &BitVec) -> BitVec;
	/// Creates a new bitvec that represents the signed multiplication of both given bitvectors.
	pub fn sdiv(&self, other: &BitVec) -> BitVec;
	/// Creates a new bitvec that represents the unsigned remainder of both given bitvectors.
	pub fn urem(&self, other: &BitVec) -> BitVec;
	/// Creates a new bitvec that represents the signed remainder of both given bitvectors.
	pub fn srem(&self, other: &BitVec) -> BitVec;

	/// Creates a new bitvec that represents the result of this bitvector left-shifted by the other one.
	pub fn shl(&self, other: &BitVec) -> BitVec;
	/// Creates a new bitvec that represents the result of this bitvector logically right-shifted by the other one.
	pub fn lshl(&self, other: &BitVec) -> BitVec;
	/// Creates a new bitvec that represents the result of this bitvector arithmetically right-shifted by the other one.
	pub fn ashl(&self, other: &BitVec) -> BitVec;

	/// Creates a new bitvev that represents the bitwise-not of the given bitvector.
	pub fn not(&self) -> BitVec;

	/// Flip all bits of the given bitvector inplace.
	pub fn not_assign(&mut self);

	/// Creates a new bitvec that represents the bitwise-and of both given bitvectors.
	pub fn and(&self, other: &BitVec) -> BitVec;
	/// Creates a new bitvec that represents the bitwise-or of both given bitvectors.
	pub fn or(&self, other: &BitVec) -> BitVec;
	/// Creates a new bitvec that represents the bitwise-xor of both given bitvectors.
	pub fn xor(&self, other: &BitVec) -> BitVec;

	/// Creates a new bitvec that represents the truncation of this bitvector to the given bits.
	pub fn trunc(&self, bits: usize) -> BitVec;

	/// Creates a new bitvec that represents the zero-extension of this bitvector to the given bits.
	pub fn zext(&self, bits: usize) -> BitVec;

	/// Creates a new bitvec that represents the sign-extension of this bitvector to the given bits.
	pub fn sext(&self, bits: usize) -> BitVec;
}
