
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EncodeErrorKind {
	UnequalAmountOfLiterals,
	RequiresAtLeast2Inputs,
	InputsContainOutput,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncodeError {
	kind: EncodeErrorKind,
}

impl EncodeError {
	pub fn kind(&self) -> &EncodeErrorKind {
		&self.kind
	}

	pub fn unequal_amount_of_lits() -> Self {
		Self {
			kind: EncodeErrorKind::UnequalAmountOfLiterals,
		}
	}

	pub fn requires_at_least_2_inputs() -> Self {
		Self {
			kind: EncodeErrorKind::RequiresAtLeast2Inputs,
		}
	}

	pub fn inputs_contain_output() -> Self {
		Self {
			kind: EncodeErrorKind::InputsContainOutput,
		}
	}
}

pub type EncodeResult<T> = core::result::Result<T, EncodeError>;
