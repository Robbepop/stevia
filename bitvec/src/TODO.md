TODOs for `BitVec` (deprecated) and `FlexInt`
=============================================

- Implement `Binary`, `Octal`, `UpperHex`, `LowerHex`, `Zeroable`.
- Implement arithmetic traits (`Add`, `Sub`, `Mul`, `Div`, etc.) like:
	- `impl Add<FlexInt> for FlexInt {}
	- `impl<'a> Add<FlexInt> for &'a FlexInt {}`
	- `impl<'a> Add<&'a FlexInt> for FlexInt {}`
	- `impl<'a, 'b> Add<&'a FlexInt> for &'b FlexInt {}`
