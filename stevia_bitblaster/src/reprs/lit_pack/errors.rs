use super::{
	BitPackError,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrorKind {
	BitPackError(BitPackError),
	OutOfBoundsAccess{
		access_at: usize,
		actual_len: usize,
	},
	OutOfBoundsAlloc{
		offset: usize,
		len: usize,
	},
	InvalidLitPackLen{
		err_len: usize,
	},
	InvalidZeroOffset,
	InvalidSplitPosition{
		split_at: usize,
		len: usize,
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
	kind: ErrorKind,
}

impl From<BitPackError> for Error {
	fn from(err: BitPackError) -> Self {
		Self {
			kind: ErrorKind::BitPackError(err)
		}
	}
}

impl Error {
	pub fn kind(&self) -> &ErrorKind {
		&self.kind
	}

	pub fn out_of_bounds_access(access_at: usize, actual_len: usize) -> Self {
		Self {
			kind: ErrorKind::OutOfBoundsAccess {
				access_at,
				actual_len,
			},
		}
	}

	pub fn out_of_bounds_alloc(offset: usize, len: usize) -> Self {
		Self {
			kind: ErrorKind::OutOfBoundsAlloc {
				offset,
				len,
			}
		}
	}

	pub fn invalid_lit_pack_len(err_len: usize) -> Self {
		Self {
			kind: ErrorKind::InvalidLitPackLen {
				err_len,
			},
		}
	}

	pub fn invalid_zero_offset() -> Self {
		Self {
			kind: ErrorKind::InvalidZeroOffset,
		}
	}

	pub fn invalid_split_position(split_at: usize, len: usize) -> Self {
		Self {
			kind: ErrorKind::InvalidSplitPosition {
				split_at,
				len,
			}
		}
	}
}

pub type Result<T> = core::result::Result<T, Error>;

impl core::fmt::Display for Error {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		match self.kind() {
			ErrorKind::BitPackError(err) => err.fmt(f),
			ErrorKind::OutOfBoundsAccess{access_at, actual_len} => {
				write!(f,
					"access at {:?} out of bounds with actual len of {:?}",
					access_at,
					actual_len
				)
			}
			ErrorKind::OutOfBoundsAlloc{offset, len} => {
				write!(f,
					"out of bounds lit pack allocation with offset (= {:?}) and len (= {:?})",
					offset,
					len
				)
			}
			ErrorKind::InvalidLitPackLen{err_len} => {
				write!(f,
					"invalid lit pack length of {:?}",
					err_len
				)
			}
			ErrorKind::InvalidZeroOffset => {
				write!(f,
					"invalid zero offset during lit pack creation"
				)
			},
			ErrorKind::InvalidSplitPosition{split_at, len} => {
				write!(f,
					"invalid split position at {:?} of lit pack with length (= {:?}",
					split_at,
					len
				)
			}
		}
	}
}

impl std::error::Error for Error {}
