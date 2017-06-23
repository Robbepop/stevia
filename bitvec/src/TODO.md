TODOs for `BitVec` (deprecated) and `FlexInt`
=============================================

- Implement `Binary`, `Octal`, `UpperHex`, `LowerHex`, `Zeroable`.
- Implement arithmetic traits (`Add`, `Sub`, `Mul`, `Div`, etc.) like:
	- `impl Add<FlexInt> for FlexInt {}
	- `impl<'a> Add<FlexInt> for &'a FlexInt {}`
	- `impl<'a> Add<&'a FlexInt> for FlexInt {}`
	- `impl<'a, 'b> Add<&'a FlexInt> for &'b FlexInt {}`
- Implement `From<T> for FlexInt` for `T: {bool, u8, i8, u16,...,u64, i64}`
