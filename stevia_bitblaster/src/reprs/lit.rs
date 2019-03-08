use std::num::NonZeroU32;

/// Represents the sign of a literal.
///
/// # Note
///
/// This is not used for the internal representation.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Sign {
    /// Positive polarity.
    Pos = 0,
    /// Negative polarity.
    Neg = 1,
}

impl Sign {
    /// Convert `self` into a `u32`.
    pub fn to_u32(self) -> u32 {
        match self {
            Sign::Pos => 0,
            Sign::Neg => 1,
        }
    }

    /// Returns `Pos` if `self` was `Neg` and vice versa.
    pub fn flip(self) -> Sign {
        match self {
            Sign::Pos => Sign::Neg,
            Sign::Neg => Sign::Pos,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LitErrorKind {
	ZeroLiteral,
	LiteralValueOutOfRange,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LitError {
	kind: LitErrorKind,
}

impl LitError {
	pub fn kind(&self) -> &LitErrorKind {
		&self.kind
	}

	pub fn zero_literal() -> Self {
		Self {
			kind: LitErrorKind::ZeroLiteral,
		}
	}

	pub fn literal_value_out_of_range() -> Self {
		Self {
			kind: LitErrorKind::LiteralValueOutOfRange,
		}
	}
}

impl std::fmt::Display for LitError {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match self.kind() {
			LitErrorKind::ZeroLiteral => {
				write!(f,
					"tried to create the zero literal"
				)
			}
			LitErrorKind::LiteralValueOutOfRange => {
				write!(f,
					"tried to create a literal with an invalid variable value"
				)
			}
		}
	}
}

impl std::error::Error for LitError {}

pub type LitResult<T> = std::result::Result<T, LitError>;

/// A boolean variable.
///
/// # Note
///
/// - For implementation purpose only the lowest 31 bit are valid.
/// - The 0-variable (null-variable) is invalid.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Var(NonZeroU32);

impl Var {
	/// The maximum variable.
	pub const MAX: Var = Var(unsafe { NonZeroU32::new_unchecked(core::u32::MAX >> 1) });

    /// Creates a new variable from the given value.
    ///
    /// # Errors
    ///
    /// - If the given value is zero (0).
	/// - If the given value is an invalid variable representation.
    pub fn new(val: u32) -> LitResult<Var> {
        if val == 0 {
            return Err(LitError::zero_literal())
        }
        if val > Self::MAX.to_u32() {
            return Err(LitError::literal_value_out_of_range())
        }
        Ok(unsafe { Var::new_unchecked(val) })
    }

    /// Creates a new variable from the given value.
    ///
    /// # Safety
    ///
    /// The user code has to ensure that this is not being called
    /// with val being zero (0).
    pub unsafe fn new_unchecked(val: u32) -> Var {
        debug_assert!(val != 0);
        debug_assert!(val <= Self::MAX.to_u32());
        Var(NonZeroU32::new_unchecked(val))
    }

    /// Returns the raw `u32` representation of `self`.
    pub fn to_u32(self) -> u32 {
        self.0.get()
    }
}

/// A boolean literal.
///
/// # Note
///
/// - The sign is encoded in the least-significant bit while the
///   remaining 31-bit are encoding the represented variable.
/// - A literal can only represent valid variables.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Lit(u32);

impl Lit {
    /// Creates a new literal from the given variable and sign.
    pub fn new(var: Var, sign: Sign) -> Lit {
        Lit((var.to_u32() << 1) + sign.to_u32())
    }

    /// Creates a new literal from the given variable with positive polarity.
    pub fn pos(var: Var) -> Lit {
        Lit::new(var, Sign::Pos)
    }

    /// Creates a new literal from the given variable with negative polarity.
    pub fn neg(var: Var) -> Lit {
        Lit::new(var, Sign::Neg)
    }

    /// Flips the sign of `self`.
    pub fn flip(self) -> Lit {
        let mut this = self;
        this.0 ^= 1;
        this
    }

    /// Returns the variable of `self`.
    pub fn var(self) -> Var {
        unsafe { Var::new_unchecked(self.0 >> 1) }
    }

    /// Returns the sign of `self`.
    pub fn sign(self) -> Sign {
        if (self.0 & 1) != 0 {
            return Sign::Neg;
        }
        Sign::Pos
    }
}

impl core::ops::Neg for Lit {
    type Output = Lit;

    fn neg(self) -> Self::Output {
        self.flip()
    }
}

impl From<Var> for Lit {
    fn from(var: Var) -> Self {
        Lit::new(var, Sign::Pos)
    }
}

/// This impl exists solely to allow for generic iterator
/// approach using variables instead of literals within slices.
impl<'a> From<&'a Lit> for Lit {
    fn from(lit: &'a Lit) -> Self {
        *lit
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod var {
        use super::*;
        use std::u32;

        #[test]
        fn new_ok() {
            assert_eq!(Var::new(1), Ok(unsafe { Var::new_unchecked(1) }));
            assert_eq!(Var::new(42), Ok(unsafe { Var::new_unchecked(42) }));
            assert_eq!(Var::new(u32::MAX >> 1), Ok(Var::MAX))
        }

        #[test]
        fn new_err() {
            assert!(Var::new(0).is_err());
            assert!(Var::new(Var::MAX.to_u32() + 1).is_err());
            assert!(Var::new(u32::MAX).is_err());
        }

        #[test]
        fn new_unchecked_ok() {
            unsafe { Var::new_unchecked(1) };
            unsafe { Var::new_unchecked(42) };
            unsafe { Var::new_unchecked(Var::MAX.to_u32()) };
        }

        #[test]
        #[should_panic]
		#[cfg(debug_assertions)]
        fn new_unchecked_err_0() {
            unsafe { Var::new_unchecked(0) };
        }

        #[test]
        #[should_panic]
		#[cfg(debug_assertions)]
        fn new_unchecked_err_1() {
            unsafe { Var::new_unchecked(Var::MAX.to_u32() + 1) };
        }

        #[test]
        fn to_u32() {
            assert_eq!(Var::new(1).map(|var| var.to_u32()), Ok(1));
            assert_eq!(Var::new(5).map(|var| var.to_u32()), Ok(5));
            assert_eq!(Var::new(42).map(|var| var.to_u32()), Ok(42));
            assert_eq!(Var::MAX.to_u32(), core::u32::MAX >> 1);
        }
    }

    mod sign {
        use super::*;

        #[test]
        fn to_u32() {
            assert_eq!(Sign::Pos.to_u32(), 0);
            assert_eq!(Sign::Neg.to_u32(), 1);
        }

        #[test]
        fn flip() {
            assert_eq!(Sign::Pos.flip(), Sign::Neg);
            assert_eq!(Sign::Neg.flip(), Sign::Pos);
        }
    }

    mod lit {
        use super::*;

        #[test]
        fn from_var_is_pos() {
            assert_eq!(Lit::from(Var::new(1).unwrap()), Lit::pos(Var::new(1).unwrap()));
            assert_eq!(Lit::from(Var::new(5).unwrap()), Lit::pos(Var::new(5).unwrap()));
            assert_eq!(Lit::from(Var::new(42).unwrap()), Lit::pos(Var::new(42).unwrap()));
            assert_eq!(Lit::from(Var::MAX), Lit::pos(Var::MAX));
        }

        #[test]
        fn pos() {
            assert_eq!(Lit::pos(Var::new(1).unwrap()), Lit::new(Var::new(1).unwrap(), Sign::Pos));
            assert_eq!(Lit::pos(Var::new(5).unwrap()), Lit::new(Var::new(5).unwrap(), Sign::Pos));
            assert_eq!(Lit::pos(Var::new(42).unwrap()), Lit::new(Var::new(42).unwrap(), Sign::Pos));
            assert_eq!(
                Lit::pos(Var::MAX),
                Lit::new(Var::MAX, Sign::Pos)
            );
        }

        #[test]
        fn neg() {
            assert_eq!(Lit::neg(Var::new(1).unwrap()), Lit::new(Var::new(1).unwrap(), Sign::Neg));
            assert_eq!(Lit::neg(Var::new(5).unwrap()), Lit::new(Var::new(5).unwrap(), Sign::Neg));
            assert_eq!(Lit::neg(Var::new(42).unwrap()), Lit::new(Var::new(42).unwrap(), Sign::Neg));
            assert_eq!(
                Lit::neg(Var::MAX),
                Lit::new(Var::MAX, Sign::Neg)
            );
        }

        #[test]
        fn new() {
            fn assert_for_sign(var: Var, sign: Sign) {
                assert_eq!(
                    Lit::new(var, sign),
                    Lit((var.to_u32() << 1) | sign.to_u32())
                );
            }
            fn assert_both_polarity(var: Var) {
                assert_for_sign(var, Sign::Pos);
                assert_for_sign(var, Sign::Neg);
            }
            assert_both_polarity(Var::new(1).unwrap());
            assert_both_polarity(Var::new(5).unwrap());
            assert_both_polarity(Var::new(42).unwrap());
            assert_both_polarity(Var::MAX);
        }

        #[test]
        fn neg_or_flip() {
            fn assert_both_polarity(var: Var) {
                assert_eq!(Lit::pos(var).flip(), Lit::neg(var));
                assert_eq!(Lit::neg(var).flip(), Lit::pos(var));
                assert_eq!(-Lit::pos(var), Lit::neg(var));
                assert_eq!(-Lit::neg(var), Lit::pos(var));
            }
            assert_both_polarity(Var::new(1).unwrap());
            assert_both_polarity(Var::new(5).unwrap());
            assert_both_polarity(Var::new(42).unwrap());
            assert_both_polarity(Var::MAX);
        }

        #[test]
        fn var() {
            fn assert_both_polarity(var: Var) {
                assert_eq!(Lit::pos(var).var(), var);
                assert_eq!(Lit::neg(var).var(), var);
            }
            assert_both_polarity(Var::new(1).unwrap());
            assert_both_polarity(Var::new(5).unwrap());
            assert_both_polarity(Var::new(42).unwrap());
            assert_both_polarity(Var::MAX);
        }

        #[test]
        fn sign() {
            fn assert_both_polarity(var: Var) {
                assert_eq!(Lit::pos(var).sign(), Sign::Pos);
                assert_eq!(Lit::neg(var).sign(), Sign::Neg);
            }
            assert_both_polarity(Var::new(1).unwrap());
            assert_both_polarity(Var::new(5).unwrap());
            assert_both_polarity(Var::new(42).unwrap());
            assert_both_polarity(Var::MAX);
        }
    }
}
