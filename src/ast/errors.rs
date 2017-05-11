use std::fmt;
use std::error;

use ast::{Type, TypeKind};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrorKind {
	TypeKindError{given: TypeKind, expected: TypeKind},

	IncompatibleBitWidth(usize, usize),
	IncompatibleIndexBitWidth(usize, usize),
	IncompatibleValueBitWidth(usize, usize),
	IncompatibleArrayTypes((usize,usize),(usize,usize)),

	ExpectedBooleanType{found_type: Type},
	ExpectedBitVecType{found_type: Type},
	ExpectedArrayType{found_type: Type},
	ExpectedBooleanTypeKind{found_kind: TypeKind},
	ExpectedBitVecTypeKind{found_kind: TypeKind},
	ExpectedArrayTypeKind{found_kind: TypeKind},

	TooFewChildren{given: usize, expected_min: usize},
	InvalidIdentifier{var: String, invalid_ident: String},
	ZeroBitwidthType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AstError(pub ErrorKind);

impl fmt::Display for AstError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TODO: better error display. {:?}", self)
    }
}

impl error::Error for AstError {
	fn description(&self) -> &str {
		use self::ErrorKind::*;
		match self.0 {
			TypeKindError{..}             => "type error",

			IncompatibleBitWidth(..)      => "found bitvectors with incompatible bit-widths",
			IncompatibleIndexBitWidth(..) => "found incompatible array index bit-width",
			IncompatibleValueBitWidth(..) => "found incompatible array value bit-width",
			IncompatibleArrayTypes(..)    => "found incompatible arrays",

			ExpectedBooleanType{..}     => "expected boolean type",
			ExpectedBitVecType{..}      => "expected bitvec type",
			ExpectedArrayType{..}       => "expected array type",
			ExpectedBooleanTypeKind{..} => "expected boolean type kind",
			ExpectedBitVecTypeKind{..}  => "expected bitvec type kind",
			ExpectedArrayTypeKind{..}   => "expected array type kind",

			TooFewChildren{..}            => "expression has too few child expressions",
			InvalidIdentifier{..}         => "invalid identifier for symbol",
			ZeroBitwidthType              => "found bitvector type specification with an invalid bit-width of 0"
		}
	}
}

pub type Result<T> = ::std::result::Result<T, AstError>;
