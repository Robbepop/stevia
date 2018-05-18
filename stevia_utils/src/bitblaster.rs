//! Streaming-Bitblaster data structure.
//!
//! These data structures allow for an efficient conversion into CNF
//! and should also make it quite easy to convert into AIG if needed.
//! Also they allow for a higher-level bit blaster implementation
//! than when directly constructing CNF or AIG.
//! 
//! As with CNF this data structure allows for a streaming bit blaster
//! implementation that does not need to allocate temporary data structures
//! for partial construction.
//! 
//! This has the effect that after streaming conversion to CNF one could
//! simply and directly forward this to an IPASIR implementing SAT
//! solver in an efficient way.

#![allow(dead_code)]

/// A boolean item is either a literal or a binary formula.
/// 
/// # Note
/// 
/// The distinction between `Item` and `Cons` exists
/// entirely to break recursive cycles within the data structure.
pub enum Item {
    /// A simple literal.
    Lit(Lit),
    /// A binary operation.
    Bin(Bin)
}

/// A boolean constraint is either an item or a definition.
/// 
/// This is what a bit blaster is streaming in the end.
/// The streamed set of `Cons` instances represent the bit blasted
/// formula as conjunction.
/// 
/// # Note
/// 
/// The distinction between `Item` and `Cons` exists
/// entirely to break recursive cycles within the data structure.
pub enum Cons {
    /// An item. (Previously defined above.)
    Item(Item),
    /// A variable definition.
    Def(Def)
}

/// A boolean variable.
/// 
/// # Note
/// 
/// - For implementation purpose only the lowest 31 bit are valid.
/// - The 0-variable (null-variable) is invalid.
pub struct Var(u32);

/// A boolean literal.
/// 
/// # Note
/// 
/// - The sign is encoded in the least-significant bit while the
///   remaining 31-bit are encoding the represented variable.
/// - A literal can only represent valid variables.
pub struct Lit(u32);

/// The operator kind.
pub enum BinKind {
    /// Logical-and
    And,
    /// Logical-or
    Or,
    /// Logical-xor (either-or)
    Xor,
    /// Logical implication
    Implies,
    /// Logical if-and-only-if (iff)
    Iff
}

/// Boolean binary operators and their operands.
pub struct Bin {
    /// The operator kind.
    pub op: BinKind,
    /// The left hand-side operand.
    pub lhs: Lit,
    /// The right hand-side operand.
    pub rhs: Lit
}

/// A boolean variable definition.
/// 
/// This defines a variable to be equal to the right hand-side item.
pub struct Def {
    pub var: Var,
    pub rhs: Item
}

impl From<Lit> for Item {
    fn from(lit: Lit) -> Self {
        Item::Lit(lit)
    }
}

impl From<Bin> for Item {
    fn from(bin: Bin) -> Self {
        Item::Bin(bin)
    }
}

impl From<Item> for Cons {
    fn from(item: Item) -> Self {
        Cons::Item(item)
    }
}

impl From<Def> for Cons {
    fn from(def: Def) -> Self {
        Cons::Def(def)
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

impl From<Var> for Lit {
    fn from(var: Var) -> Self {
        Lit::new(var, Sign::Pos)
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

impl Bin {
    /// Creates a new binary operation with the given kind and operands.
    pub fn new(kind: BinKind, lhs: Lit, rhs: Lit) -> Self {
        Bin{op: kind, lhs, rhs}
    }

    /// Creates a new binary and-operation with the given operands.
    pub fn and(lhs: Lit, rhs: Lit) -> Self {
        Bin::new(BinKind::And, lhs, rhs)
    }

    /// Creates a new binary or-operation with the given operands.
    pub fn or(lhs: Lit, rhs: Lit) -> Self {
        Bin::new(BinKind::Or, lhs, rhs)
    }

    /// Creates a new binary xor-operation with the given operands.
    pub fn xor(lhs: Lit, rhs: Lit) -> Self {
        Bin::new(BinKind::Xor, lhs, rhs)
    }

    /// Creates a new binary implies-operation with the given operands.
    pub fn implies(lhs: Lit, rhs: Lit) -> Self {
        Bin::new(BinKind::Implies, lhs, rhs)
    }

    /// Creates a new binary iff-operation with the given operands.
    pub fn iff(lhs: Lit, rhs: Lit) -> Self {
        Bin::new(BinKind::Iff, lhs, rhs)
    }
}

impl Def {
    /// Creates a new definition for the given variable and item.
    /// 
    /// # Note
    /// 
    /// The given variable is now being defined as the given item.
    pub fn new(var: Var, item: Item) -> Self {
        Def{ var, rhs: item }
    }
}
