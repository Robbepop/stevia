
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
