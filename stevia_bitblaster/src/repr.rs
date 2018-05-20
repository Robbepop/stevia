
/// A boolean variable.
/// 
/// # Note
/// 
/// - For implementation purpose only the lowest 31 bit are valid.
/// - The 0-variable (null-variable) is invalid.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Var(u32);

/// Represents a contiguous pack of variables.
///
/// # Note
///
/// This is just a more efficient way to relate to a bunch of
/// related variables.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct VarPack {
    /// The identifier of the lowest-value variable in `self`.
    off: usize,
    /// The number of variables in `self`.
    len: usize
}

/// An iterator through a pack of variables.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct VarPackIter {
    /// The variable pack to be iterated.
    var_pack: VarPack,
    /// The current position.
    cur: usize
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

/// Represents the sign of a literal.
/// 
/// # Note
/// 
/// This is not used for the internal representation.
pub enum Sign { Pos = 0, Neg = 1 }

impl Sign {
    /// Convert `self` into a `u32`.
    fn to_u32(self) -> u32 {
        match self {
            Sign::Pos => 0,
            Sign::Neg => 1
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
        if val == 0 {
            return Err(String::from("Cannot create a `Var` from `0`."))
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
        Var(val)
    }

    /// Returns the raw `u32` representation of `self`.
    pub fn to_u32(self) -> u32 {
        self.0
    }
}

impl ::std::ops::Neg for Var {
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
            return Sign::Neg
        }
        Sign::Neg
    }
}

impl ::std::ops::Neg for Lit {
    type Output = Lit;

    fn neg(self) -> Self::Output {
        self.flip()
    }
}

impl VarPack {
    /// Creates a new `VarPack` from the given offset and length.
    pub fn new(offset: usize, len: usize) -> Result<VarPack, String> {
        if offset == 0 {
            return Err(String::from("VarPack::new: error: invalid offset of 0"))
        }
        Ok(Self{ off: offset, len: len })
    }

    /// Returns the variable of `self` at the given position.
    ///
    /// # Errors
    ///
    /// If the given position is out of bounds.
    pub fn get(self, pos: usize) -> Option<Var> {
        if pos < self.len {
            return Some(Var::new_unchecked((self.off + pos) as u32))
        }
        None
    }

    /// Returns the offset of `self`.
    pub fn offset(self) -> usize {
        self.off
    }

    /// Returns the length (number of represented variables) of `self`.
    pub fn len(self) -> usize {
        self.len
    }

    /// Returns the i'th variable of `self`.
    pub fn i(self, i: usize) -> Var {
        debug_assert!(i < self.len());
        Var::new_unchecked((self.off + i) as u32)
    }
}

impl VarPackIter {
    /// Creates a new variable pack iterator.
    pub(crate) fn new(var_pack: VarPack) -> Self {
        Self{ var_pack: var_pack, cur: 0 }
    }
}

impl Iterator for VarPackIter {
    type Item = Var;

    fn next(&mut self) -> Option<Self::Item> {
        let var = self.var_pack.get(self.cur);
        if self.cur < self.var_pack.len() {
            self.cur += 1
        }
        var
    }
}

impl IntoIterator for VarPack {
    type Item = Var;
    type IntoIter = VarPackIter;

    fn into_iter(self) -> Self::IntoIter {
        VarPackIter::new(self)
    }
}
