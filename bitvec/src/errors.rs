use std::result;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorKind {
	InvalidBinaryStr(String),
	InvalidDecimalStr(String),
	InvalidHexStr(String),
	UnmatchingBitwidth(u32, u32),
	InvalidZeroBitWidth,
	InvalidBitWidthArgument(u32)
}
// use self::ErrorKind::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Error(ErrorKind);

impl Error {
	pub fn from_kind(kind: ErrorKind) -> Error {
		Error(kind)
	}
}

pub type Result<T> = result::Result<T, Error>;
