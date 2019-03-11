use crate::Bitvec;
use std::{
	result::Result as StdResult,
	error::Error as StdError,
	fmt,
};

/// The result type for bitvector operations.
pub type BitvecResult<T> = StdResult<T, BitvecError>;

/// Error kinds of errors associated to bitvector operations.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BitvecErrorKind {
    /// Errors of the underlying bitvector implementation library.
    InternalError(apint::Error),
    /// Encountered upon an invalid lo-hi boundary for extract operations.
    InvalidExtractLoHiBounds {
        /// The invalid lo-boundary.
        lo: usize,
        /// The invalid hi-boundary.
        hi: usize,
        /// The source bitvector for the extract operation.
        source: Bitvec,
    },
}

/// The error type that is returned by bitvector operations.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitvecError {
    /// The kind of the error.
    kind: BitvecErrorKind,
}

impl From<apint::Error> for BitvecError {
    fn from(err: apint::Error) -> Self {
        BitvecError::new(BitvecErrorKind::InternalError(err))
    }
}

impl BitvecError {
    /// Returns the kind of this error.
    pub fn kind(&self) -> &BitvecErrorKind {
        &self.kind
    }

    /// Unwrap this error into its underlying type.
    pub fn into_kind(self) -> BitvecErrorKind {
        self.kind
    }

    /// Returns `true` if this is an internal bitvector error from the apint crate.
    pub fn is_internal_error(&self) -> bool {
        if let BitvecErrorKind::InternalError(_) = self.kind() {
            return true;
        }
        false
    }

    /// Creates a new `ExprError` from the given `ExprErrorKind`.
    fn new(kind: BitvecErrorKind) -> Self {
        BitvecError { kind }
    }

    /// Returns a `BitvecError` that indicates that the extract operation has invalid lo-hi bounds.
    pub fn invalid_extract_lo_hi_bounds(lo: usize, hi: usize, source: Bitvec) -> Self {
        BitvecError::new(BitvecErrorKind::InvalidExtractLoHiBounds { lo, hi, source })
    }
}

impl fmt::Display for BitvecError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::BitvecErrorKind::*;
        match &self.kind {
			InternalError(internal_error) => internal_error.fmt(f),
            InvalidExtractLoHiBounds{lo, hi, source} => write!(
                f,
                "Encountered invalid lo (= {:?}) and hi (= {:?}) bounds for extract operation with source: {:?}",
                lo, hi, source
            )
		}
    }
}

impl StdError for BitvecError {
    fn description(&self) -> &str {
        use self::BitvecErrorKind::*;
        match self.kind() {
            InternalError(internal_error) => internal_error.description(),
            InvalidExtractLoHiBounds { .. } => {
                "Encountered invalid lo-hi bounds for extract operation"
            }
        }
    }

    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        if let BitvecErrorKind::InternalError(internal) = self.kind() {
            return Some(internal)
        }
        None
    }
}
