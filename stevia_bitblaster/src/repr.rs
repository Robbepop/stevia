use std::ops;

/// A boolean variable.
///
/// # Note
///
/// - For implementation purpose only the lowest 31 bit are valid.
/// - The 0-variable (null-variable) is invalid.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Var(u32);

/// A boolean literal.
///
/// # Note
///
/// - The sign is encoded in the least-significant bit while the
///   remaining 31-bit are encoding the represented variable.
/// - A literal can only represent valid variables.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Lit(u32);

/// Represents a contiguous pack of literals.
///
/// # Note
///
/// This is just a more efficient way to relate to a bunch of
/// related variables.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct LitPack {
    /// The identifier of the lowest-value variable in `self`.
    off: usize,
    /// The number of variables in `self`.
    len: usize,
    /// Sign of the represented literals when accessed.
    sign: Sign,
}

/// An iterator through a pack of variables.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct LitPackIter {
    /// The variable pack to be iterated.
    lit_pack: LitPack,
    /// The current position.
    cur: usize,
}

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

impl Var {
    /// Creates a new variable from the given value.
    ///
    /// # Errors
    ///
    /// If the given value is zero (0).
    pub fn new(val: u32) -> Result<Var, String> {
        use std::u32;
        if val == 0 {
            return Err(String::from(
                "Var::new: error: Zero is an invalid representation for a variable.",
            ));
        }
        if val > (u32::MAX >> 1) {
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
        use std::u32;
        debug_assert!(val != 0);
        debug_assert!(val <= (u32::MAX >> 1));
        Var(val)
    }

    /// Returns the raw `u32` representation of `self`.
    pub fn to_u32(self) -> u32 {
        self.0
    }
}

impl ops::Neg for Var {
    type Output = Lit;

    fn neg(self) -> Self::Output {
        Lit::from(self).flip()
    }
}

impl From<Var> for Lit {
    fn from(var: Var) -> Self {
        Lit::new(var, Sign::Pos)
    }
}

/// This impl exists solely to allow for generic iterator
/// approach using variables instead of literals within slices.
impl<'a> From<&'a Var> for Lit {
    fn from(var: &'a Var) -> Self {
        Lit::new(*var, Sign::Pos)
    }
}

/// This impl exists solely to allow for generic iterator
/// approach using variables instead of literals within slices.
impl<'a> From<&'a Lit> for Lit {
    fn from(lit: &'a Lit) -> Self {
        *lit
    }
}

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
        Sign::Neg
    }
}

impl ops::Neg for Lit {
    type Output = Lit;

    fn neg(self) -> Self::Output {
        self.flip()
    }
}

impl LitPack {
    /// Creates a new `LitPack` from the given offset and length.
    ///
    /// # Note
    ///
    /// Literals represented by the returned `LitPack` have positive signs.
    pub fn new(offset: usize, len: usize) -> Result<LitPack, String> {
        if offset == 0 {
            return Err(String::from("VarPack::new: error: invalid offset of 0"));
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
            off: self.offset(),
            len: self.len(),
            sign: self.sign.flip(),
        }
    }

    /// Returns the literal of `self` at the given position.
    ///
    /// # Errors
    ///
    /// If the given position is out of bounds.
    pub fn get(self, pos: usize) -> Option<Lit> {
        if pos < self.len {
            return Some(Lit::new(
                Var::new_unchecked((self.off + pos) as u32),
                self.sign,
            ));
        }
        None
    }

    /// Returns the literal of `self` at the given position.
    ///
    /// # Safety
    ///
    /// This does not check if `pos` is out of bounds.
    pub fn get_unchecked(self, pos: usize) -> Lit {
        debug_assert!(pos < self.len());
        Lit::new(Var::new_unchecked((self.off + pos) as u32), self.sign)
    }

    /// Returns the offset of `self`.
    pub fn offset(self) -> usize {
        self.off
    }

    /// Returns the length (number of represented variables) of `self`.
    pub fn len(self) -> usize {
        self.len
    }
}

impl FnOnce<(usize,)> for LitPack {
    type Output = Lit;

    extern "rust-call" fn call_once(self, idx: (usize,)) -> Self::Output {
        self.get_unchecked(idx.0)
    }
}

impl LitPackIter {
    /// Creates a new variable pack iterator.
    pub(crate) fn new(var_pack: LitPack) -> Self {
        Self {
            lit_pack: var_pack,
            cur: 0,
        }
    }
}

impl Iterator for LitPackIter {
    type Item = Lit;

    fn next(&mut self) -> Option<Self::Item> {
        let lit = self.lit_pack.get(self.cur);
        if self.cur < self.lit_pack.len() {
            self.cur += 1
        }
        lit
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.lit_pack.len() - self.cur;
        (remaining, Some(remaining))
    }

    fn nth(&mut self, index: usize) -> Option<Self::Item> {
        let nth_lit = self.lit_pack.get(self.cur + index);
        self.cur += index + 1;
        nth_lit
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
            assert_eq!(Var::new(u32::MAX >> 1), Ok(Var(u32::MAX >> 1)))
        }

        #[test]
        fn new_err() {
            assert!(Var::new(0).is_err());
            assert!(Var::new((u32::MAX >> 1) + 1).is_err());
            assert!(Var::new(u32::MAX).is_err());
        }

        #[test]
        fn new_unchecked_ok() {
            assert_eq!(Var::new_unchecked(1), Var(1));
            assert_eq!(Var::new_unchecked(42), Var(42));
            assert_eq!(Var::new_unchecked(u32::MAX >> 1), Var(u32::MAX >> 1));
        }

        #[test]
        #[should_panic]
        fn new_unchecked_err_0() {
            Var::new_unchecked(0);
        }

        #[test]
        #[should_panic]
        fn new_unchecked_err_1() {
            Var::new_unchecked((u32::MAX >> 1) + 1);
        }

        #[test]
        fn to_u32() {
            assert_eq!(Var(1).to_u32(), 1);
            assert_eq!(Var(5).to_u32(), 5);
            assert_eq!(Var(42).to_u32(), 42);
            assert_eq!(Var(u32::MAX >> 1).to_u32(), u32::MAX >> 1);
        }

        #[test]
        fn neg() {
            assert_eq!(-Var(1), Lit::neg(Var(1)));
            assert_eq!(-Var(5), Lit::neg(Var(5)));
            assert_eq!(-Var(42), Lit::neg(Var(42)));
            assert_eq!(-Var(u32::MAX >> 1), Lit::neg(Var(u32::MAX >> 1)));
        }
    }
}
