use std::ops;
use std::u32;

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
    fn to_u32(self) -> u32 {
        match self {
            Sign::Pos => 0,
            Sign::Neg => 1,
        }
    }

    /// Returns `Pos` if `self` was `Neg` and vice versa.
    fn flip(self) -> Sign {
        match self {
            Sign::Pos => Sign::Neg,
            Sign::Neg => Sign::Pos,
        }
    }
}

/// The maximum representable variable value.
const MAX_VAR_VALUE: u32 = u32::MAX >> 1;

/// A boolean variable.
///
/// # Note
///
/// - For implementation purpose only the lowest 31 bit are valid.
/// - The 0-variable (null-variable) is invalid.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Var(u32);

impl Var {
    /// Creates a new variable from the given value.
    ///
    /// # Errors
    ///
    /// If the given value is zero (0).
    pub fn new(val: u32) -> Result<Var, String> {
        if val == 0 {
            return Err(String::from(
                "Var::new: error: Zero is an invalid representation for a variable.",
            ));
        }
        if val > MAX_VAR_VALUE {
            return Err(format!(
                "Var::new: error: Given value (= {}) is too large to represent a variable.",
                val
            ));
        }
        Ok(Var(val))
    }

    /// Creates a new variable from the given value.
    ///
    /// # Safety
    ///
    /// The user code has to ensure that this is not being called
    /// with val being zero (0).
    pub fn new_unchecked(val: u32) -> Var {
        debug_assert!(val != 0);
        debug_assert!(val <= MAX_VAR_VALUE);
        Var(val)
    }

    /// Returns the raw `u32` representation of `self`.
    pub fn to_u32(self) -> u32 {
        self.0
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
        Var::new_unchecked(self.0 >> 1)
    }

    /// Returns the sign of `self`.
    pub fn sign(self) -> Sign {
        if (self.0 & 1) != 0 {
            return Sign::Neg;
        }
        Sign::Pos
    }
}

impl ops::Neg for Lit {
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

/// Represents a contiguous pack of literals.
///
/// # Note
///
/// This is just a more efficient way to relate to a bunch of
/// related variables.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct LitPack {
    /// The identifier of the lowest-value variable in `self`.
    off: u32,
    /// The number of variables in `self`.
    len: u32,
    /// Sign of the represented literals when accessed.
    sign: Sign,
}

impl LitPack {
    /// Creates a new `LitPack` from the given offset and length.
    ///
    /// # Note
    ///
    /// Literals represented by the returned `LitPack` have positive signs.
    pub fn new(offset: u32, len: u32) -> Result<LitPack, String> {
        if offset == 0 {
            return Err(String::from("VarPack::new: error: invalid offset of 0"));
        }
        if len == 0 {
            return Err(String::from("VarPack::new: error: invalid len of 0"));
        }
        if offset + len > MAX_VAR_VALUE {
            return Err(String::from(
                "VarPack::new: error: the given offset and length combination is out of bounds",
            ));
        }
        Ok(Self {
            off: offset,
            len,
            sign: Sign::Pos,
        })
    }

    /// Creates a `LitPack` representing the same literals but with flipped signs.
    pub fn flip_all(self) -> LitPack {
        Self {
            off: self.off,
            len: self.len,
            sign: self.sign.flip(),
        }
    }

    /// Returns the literal of `self` at the given position.
    ///
    /// # Errors
    ///
    /// If the given position is out of bounds.
    pub fn get(self, pos: usize) -> Option<Lit> {
        if pos >= self.len() {
            return None;
        }
        Some(Lit::new(
            Var::new_unchecked(self.off + pos as u32),
            self.sign,
        ))
    }

    /// Returns the literal of `self` at the given position.
    ///
    /// # Safety
    ///
    /// This does not check if `pos` is out of bounds.
    pub fn get_unchecked(self, pos: usize) -> Lit {
        debug_assert!(pos < self.len());
        Lit::new(Var::new_unchecked(self.off + pos as u32), self.sign)
    }

    /// Returns the length (number of represented variables) of `self`.
    pub fn len(self) -> usize {
        self.len as usize
    }
}

impl FnOnce<(usize,)> for LitPack {
    type Output = Lit;

    extern "rust-call" fn call_once(self, idx: (usize,)) -> Self::Output {
        self.get_unchecked(idx.0)
    }
}

/// An iterator through a pack of variables.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct LitPackIter {
    /// The variable pack to be iterated.
    lit_pack: LitPack,
    /// The current begin position.
    ///
    /// # Note
    ///
    /// The following invariant must hold: `self.begin < self.end`. 
    begin: usize,
    /// The current end position.
    ///
    /// # Note
    ///
    /// The following invariant must hold: `self.begin < self.end`.
    end: usize
}

impl LitPackIter {
    /// Creates a new variable pack iterator.
    pub(crate) fn new(lp: LitPack) -> Self {
        Self {
            lit_pack: lp,
            begin: 0,
            end: lp.len()
        }
    }
}

impl Iterator for LitPackIter {
    type Item = Lit;

    fn next(&mut self) -> Option<Self::Item> {
        if self.begin == self.end {
            return None
        }
        let lit = self.lit_pack.get(self.begin);
        self.begin += 1;
        lit
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.end - self.begin;
        (remaining, Some(remaining))
    }

    fn nth(&mut self, index: usize) -> Option<Self::Item> {
        use std::cmp;
        let nth_lit = self.lit_pack.get(self.begin + index);
        self.begin += cmp::min(index + 1, self.end);
        nth_lit
    }
}

impl DoubleEndedIterator for LitPackIter {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.begin == self.end {
            return None
        }
        self.end -= 1;
        self.lit_pack.get(self.end)
    }
}

impl IntoIterator for LitPack {
    type Item = Lit;
    type IntoIter = LitPackIter;

    fn into_iter(self) -> Self::IntoIter {
        LitPackIter::new(self)
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
            assert_eq!(Var::new(1), Ok(Var(1)));
            assert_eq!(Var::new(42), Ok(Var(42)));
            assert_eq!(Var::new(u32::MAX >> 1), Ok(Var(MAX_VAR_VALUE)))
        }

        #[test]
        fn new_err() {
            assert!(Var::new(0).is_err());
            assert!(Var::new(MAX_VAR_VALUE + 1).is_err());
            assert!(Var::new(u32::MAX).is_err());
        }

        #[test]
        fn new_unchecked_ok() {
            assert_eq!(Var::new_unchecked(1), Var(1));
            assert_eq!(Var::new_unchecked(42), Var(42));
            assert_eq!(Var::new_unchecked(MAX_VAR_VALUE), Var(MAX_VAR_VALUE));
        }

        #[test]
        #[should_panic]
        fn new_unchecked_err_0() {
            Var::new_unchecked(0);
        }

        #[test]
        #[should_panic]
        fn new_unchecked_err_1() {
            Var::new_unchecked(MAX_VAR_VALUE + 1);
        }

        #[test]
        fn to_u32() {
            assert_eq!(Var(1).to_u32(), 1);
            assert_eq!(Var(5).to_u32(), 5);
            assert_eq!(Var(42).to_u32(), 42);
            assert_eq!(Var(MAX_VAR_VALUE).to_u32(), MAX_VAR_VALUE);
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
        fn from_var() {
            assert_eq!(Lit::from(Var(1)), Lit::pos(Var(1)));
            assert_eq!(Lit::from(Var(5)), Lit::pos(Var(5)));
            assert_eq!(Lit::from(Var(42)), Lit::pos(Var(42)));
            assert_eq!(Lit::from(Var(MAX_VAR_VALUE)), Lit::pos(Var(MAX_VAR_VALUE)));
        }

        #[test]
        fn pos() {
            assert_eq!(Lit::pos(Var(1)), Lit::new(Var(1), Sign::Pos));
            assert_eq!(Lit::pos(Var(5)), Lit::new(Var(5), Sign::Pos));
            assert_eq!(Lit::pos(Var(42)), Lit::new(Var(42), Sign::Pos));
            assert_eq!(
                Lit::pos(Var(MAX_VAR_VALUE)),
                Lit::new(Var(MAX_VAR_VALUE), Sign::Pos)
            );
        }

        #[test]
        fn neg() {
            assert_eq!(Lit::neg(Var(1)), Lit::new(Var(1), Sign::Neg));
            assert_eq!(Lit::neg(Var(5)), Lit::new(Var(5), Sign::Neg));
            assert_eq!(Lit::neg(Var(42)), Lit::new(Var(42), Sign::Neg));
            assert_eq!(
                Lit::neg(Var(MAX_VAR_VALUE)),
                Lit::new(Var(MAX_VAR_VALUE), Sign::Neg)
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
            assert_both_polarity(Var(1));
            assert_both_polarity(Var(5));
            assert_both_polarity(Var(42));
            assert_both_polarity(Var(MAX_VAR_VALUE));
        }

        #[test]
        fn neg_or_flip() {
            fn assert_both_polarity(var: Var) {
                assert_eq!(Lit::pos(var).flip(), Lit::neg(var));
                assert_eq!(Lit::neg(var).flip(), Lit::pos(var));
                assert_eq!(-Lit::pos(var), Lit::neg(var));
                assert_eq!(-Lit::neg(var), Lit::pos(var));
            }
            assert_both_polarity(Var(1));
            assert_both_polarity(Var(5));
            assert_both_polarity(Var(42));
            assert_both_polarity(Var(MAX_VAR_VALUE));
        }

        #[test]
        fn var() {
            fn assert_both_polarity(var: Var) {
                assert_eq!(Lit::pos(var).var(), var);
                assert_eq!(Lit::neg(var).var(), var);
            }
            assert_both_polarity(Var(1));
            assert_both_polarity(Var(5));
            assert_both_polarity(Var(42));
            assert_both_polarity(Var(MAX_VAR_VALUE));
        }

        #[test]
        fn sign() {
            fn assert_both_polarity(var: Var) {
                assert_eq!(Lit::pos(var).sign(), Sign::Pos);
                assert_eq!(Lit::neg(var).sign(), Sign::Neg);
            }
            assert_both_polarity(Var(1));
            assert_both_polarity(Var(5));
            assert_both_polarity(Var(42));
            assert_both_polarity(Var(MAX_VAR_VALUE));
        }
    }

    mod lit_pack {
        use super::*;

        #[test]
        fn new_invalid_offset() {
            assert!(LitPack::new(0, 1).is_err());
            assert!(LitPack::new(0, 5).is_err());
            assert!(LitPack::new(0, 42).is_err());
            assert!(LitPack::new(0, MAX_VAR_VALUE).is_err());
        }

        #[test]
        fn new_invalid_length() {
            assert!(LitPack::new(1, 0).is_err());
            assert!(LitPack::new(5, 0).is_err());
            assert!(LitPack::new(42, 0).is_err());
            assert!(LitPack::new(MAX_VAR_VALUE, 0).is_err());
        }

        #[test]
        fn new_off_len_out_of_bounds() {
            assert!(LitPack::new(MAX_VAR_VALUE, 1).is_err());
            assert!(LitPack::new(1, MAX_VAR_VALUE).is_err());
        }

        #[test]
        fn new_ok() {
            fn assert_for_off_len(valid_off: u32, valid_len: u32) {
                assert_eq!(
                    LitPack::new(valid_off, valid_len),
                    Ok(LitPack {
                        off: valid_off,
                        len: valid_len,
                        sign: Sign::Pos
                    })
                );
            }
            assert_for_off_len(1, 1);
            assert_for_off_len(5, 1);
            assert_for_off_len(1, 5);
            assert_for_off_len(5, 5);
            assert_for_off_len(42, 5);
            assert_for_off_len(5, 42);
            assert_for_off_len(42, 42);
            assert_for_off_len(MAX_VAR_VALUE - 1, 1);
            assert_for_off_len(1, MAX_VAR_VALUE - 1);
        }

        #[test]
        fn flip_all() {
            assert_eq!(
                LitPack::new(1, 1).map(|lp| lp.flip_all()),
                Ok(LitPack {
                    off: 1,
                    len: 1,
                    sign: Sign::Neg
                })
            )
        }

        #[test]
        fn flip_all_involution() {
            assert_eq!(
                LitPack::new(1, 1).map(|lp| lp.flip_all().flip_all()),
                Ok(LitPack {
                    off: 1,
                    len: 1,
                    sign: Sign::Pos
                })
            )
        }

        #[test]
        fn get_ok() {
            let lp = LitPack::new(100, 42).unwrap();
            assert_eq!(lp.get(0), Some(Lit::pos(Var(100))));
            assert_eq!(lp.get(1), Some(Lit::pos(Var(101))));
            assert_eq!(lp.get(5), Some(Lit::pos(Var(105))));
            assert_eq!(lp.get(41), Some(Lit::pos(Var(141))));
        }

        #[test]
        fn get_err() {
            let lp = LitPack::new(100, 42).unwrap();
            assert_eq!(lp.get(42), None);
            assert_eq!(lp.get(100), None);
        }

        #[test]
        fn get_unchecked_ok() {
            let lp = LitPack::new(100, 42).unwrap();
            assert_eq!(lp.get_unchecked(0), Lit::pos(Var(100)));
            assert_eq!(lp.get_unchecked(1), Lit::pos(Var(101)));
            assert_eq!(lp.get_unchecked(5), Lit::pos(Var(105)));
            assert_eq!(lp.get_unchecked(41), Lit::pos(Var(141)));
        }

        #[test]
        #[should_panic]
        fn get_unchecked_err() {
            LitPack::new(100, 42).unwrap().get_unchecked(42);
        }

        #[test]
        fn len() {
            assert_eq!(LitPack::new(1, 1).unwrap().len(), 1);
            assert_eq!(LitPack::new(5, 1).unwrap().len(), 1);
            assert_eq!(LitPack::new(1, 5).unwrap().len(), 5);
            assert_eq!(LitPack::new(42, 42).unwrap().len(), 42);
        }
    }
}
