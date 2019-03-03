mod errors;
mod pack;
mod bitset;

pub(crate) use self::{
	bitset::{
		ExternalBitPack,
		PromotedBitPack,
		PromotedBitPackMut,
		BitPackError,
	},
	errors::{
		Error,
		Result,
	},
};
pub use self::{
	pack::{
		LitPack,
		LitPackIter,
	},
};
