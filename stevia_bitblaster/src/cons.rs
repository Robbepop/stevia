
/// A boolean item is either a literal or a binary formula.
/// 
/// # Note
/// 
/// The distinction between `Item` and `Cons` exists
/// entirely to break recursive cycles within the data structure.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
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
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Cons {
    /// An item. (Previously defined above.)
    Item(Item),
    /// A variable definition.
    Def(Def)
}

/// The operator kind.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
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
