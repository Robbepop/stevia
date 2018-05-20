use repr::{Var, Lit, VarPack};

/// Interfaced used by bit blasters to call bitcode generators to actually
/// generate the bitblasted boolean formulas.
pub trait BitEncoder {
    /// Create a new variable and return it.
    #[must_use]
    fn new_var(&self) -> Var;

    /// Create a new continuous pack of variables and return it.
    ///
    /// # Note
    ///
    /// This is a lot more efficient than creating an equal amount
    /// of variables via multiple calls `new_var`.
    #[must_use]
    fn new_var_pack(&self, size: usize) -> VarPack;

    /// Asserts the given literal and makes the underlying SAT solver
    /// try to find an assignment for it.
    fn assert_lit<L>(&self, lit: L)
    where
        L: Into<Lit>;

    /// Defines `res` to be equivalent to the given `lit`.
    /// 
    /// # Note
    /// 
    /// This does not return a variable to represent the result
    /// and thus could and should be used as root clauses to
    /// constraint newly generated variables.
    fn def<D, L>(&self, res: D, lit: L)
    where
        D: Into<Lit>,
        L: Into<Lit>;

    /// Create a logical-and for the given literals and return a
    /// variable representing the result.
    #[must_use]
    fn and<I, L>(&self, lits: I) -> Lit
    where
        I: IntoIterator<Item = L>,
        L: Into<Lit>;

    /// Create a logical-or for the given literals and return a
    /// variable representing the result.
    #[must_use]
    fn or<I, L>(&self, lits: I) -> Lit
    where
        I: IntoIterator<Item = L>,
        L: Into<Lit>;

    /// Create a logical-xor for the given literals and return a
    /// variable representing the result.
    #[must_use]
    fn xor<L1, L2>(&self, lhs: L1, rhs: L2) -> Lit
    where
        L1: Into<Lit>,
        L2: Into<Lit>;

    /// Create a logical-implies for the given literals and return a
    /// variable representing the result.
    #[must_use]
    fn implies<L1, L2>(&self, lhs: L1, rhs: L2) -> Lit
    where
        L1: Into<Lit>,
        L2: Into<Lit>
    {
        self.or(&[lhs.into(), rhs.into().flip()])
    }

    /// Create a logical if-and-only-if (iff) for the given literals and return a
    /// variable representing the result.
    #[must_use]
    fn iff<L1, L2>(&self, lhs: L1, rhs: L2) -> Lit
    where
        L1: Into<Lit>,
        L2: Into<Lit>
    {
        self.xor(lhs, rhs).flip()
    }
}
