TODOs for `BitVec` (deprecated) and `FixInt`
=============================================

- Implement `ComputeBlock` as `Block` wrapper for temporary instances with bit-bounds restriction and methods to operate on it.
- Implement `Blocks`, `BlocksMut` and `IntoBlocks` iterators over `ComputeBlock`.
- Implement bit-wise `set_all`, `unset_all` and `flip_all` for `FixInt`.
- Implement arithmetic traits (`Add`, `Sub`, `Mul`, `Div`, etc.) like:
	- `impl Add<FixInt> for FixInt {}
	- `impl<'a> Add<FixInt> for &'a FixInt {}`
	- `impl<'a> Add<&'a FixInt> for FixInt {}`
	- `impl<'a, 'b> Add<&'a FixInt> for &'b FixInt {}`
- Implement `From<T> for FixInt` for `T: {bool, u8, i8, u16,...,u64, i64}`.
- Implement `Binary`, `Octal`, `UpperHex`, `LowerHex`, `Zeroable`.
