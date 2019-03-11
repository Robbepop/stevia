mod error;
mod width;
mod vec;

#[cfg(test)]
mod tests;

pub use self::{
	width::BitWidth,
	error::{
		BitvecError,
		BitvecErrorKind,
		BitvecResult,
	},
    vec::Bitvec,
};
