TODOs for `BitVec` (deprecated) and `FlexInt`
=============================================

- Implement `ComputeBlock` as `Block` wrapper for temporary instances with bit-bounds restriction and methods to operate on it.
- Implement `Blocks`, `BlocksMut` and `IntoBlocks` iterators over `ComputeBlock`.
- Implement bit-wise `set_all`, `unset_all` and `flip_all` for `FlexInt`.
- Implement arithmetic traits (`Add`, `Sub`, `Mul`, `Div`, etc.) like:
	- `impl Add<FlexInt> for FlexInt {}
	- `impl<'a> Add<FlexInt> for &'a FlexInt {}`
	- `impl<'a> Add<&'a FlexInt> for FlexInt {}`
	- `impl<'a, 'b> Add<&'a FlexInt> for &'b FlexInt {}`
- Implement `From<T> for FlexInt` for `T: {bool, u8, i8, u16,...,u64, i64}`.
- Implement `Binary`, `Octal`, `UpperHex`, `LowerHex`, `Zeroable`.
