use repr::{Lit, LitPack};

/// Types that are able to generate single literals and literal packs.
///
/// # Note
///
/// Used by `GateEncoder` implementors.
pub trait LitGen {
    /// Generate and return a new single literal.
    ///
    /// # Note
    ///
    /// Generate a literal pack if you need multiple related literals since
    /// this is more efficient.
    fn new_lit(&self) -> Lit;

    /// Generate and return a new literal pack for the given amount of literals.
    ///
    /// # Note
    ///
    /// A literal pack of size `N` is more efficient to use than generating
    /// `N` single literals and also have a very efficient memory representation
    /// since their IDs are guaranteed to be continuous.
    ///
    /// All literals represented by the returned literal pack are in positive polarity.
    fn new_lit_pack(&self, size: usize) -> LitPack;
}

/// Types that allow to encode assertions at bit level.
pub trait AssertEncoder {
    /// Assert the given literal.
    fn assert_lit<L>(&self, lit: L)
    where
        L: Into<Lit>;
}

/// Encodes gate structures at the bit level.
///
/// # Note
///
/// - This is used as the backend of the bit blasting routines
///   and allows to transform SMT code to bit-level code.
///
/// - Implementors might transform the given gates into different
///   boolean formula forms such as CNF or AIG.
///
/// - This interface allows for semi high-level and efficient
///   modular bit blasting.
///
/// # Gate Structure
///
/// A gate structure is a boolean functional that always has
/// exactly one output at the end that is equivalent to the
/// result of the encoded boolean functional and thus its
/// representant.
///
/// The output can be used to nest gates within each other.
pub trait RawGateEncoder {
    /// Encode an AND gate with the given output and literals: `output ⇔ (l₁ ∧ l₂ ∧ ... ∧ lᵢ)`
    ///
    /// # Panics
    ///
    /// If `lits` yields less than 2 literals.
    fn and_gate<I>(&self, output: Lit, lits: I)
    where
        I: Iterator<Item = Lit>;

    /// Encode an OR gate with the given output and literals: `output ⇔ (l₁ ∨ l₂ ∨ ... ∨ lᵢ)`
    ///
    /// # Panics
    ///
    /// If `lits` yields less than 2 literals.
    fn or_gate<I>(&self, output: Lit, lits: I)
    where
        I: Iterator<Item = Lit>;

    /// Encode an XOR gate with the given output and literals: `output ⇔ (lhs XOR rhs)`
    fn xor_gate(&self, output: Lit, lhs: Lit, rhs: Lit);

    /// Encode an IMPLIES gate with the given output and literals: `output ⇔ (lhs ⇒ rhs)`
    fn implies_gate(&self, output: Lit, lhs: Lit, rhs: Lit);

    /// Encode an IFF (if-and-only-if) gate with the given output and literals: `output ⇔ (lhs ⇔ rhs)`
    fn iff_gate(&self, output: Lit, lhs: Lit, rhs: Lit);

    /// Encode a NOT gate with the given output and input literals: `output ⇔ (¬input)`
    ///
    /// # Note
    ///
    /// This is similar to a simple non-gate XOR encoding.
    fn not_gate(&self, output: Lit, input: Lit);

    /// Encode an EQUALS gate with the given output and input literals: `output ⇔ input`
    ///
    /// # Note
    ///
    /// This is similar to a simple non-gate XOR encoding.
    fn eq_gate(&self, output: Lit, input: Lit);
}

/// Represents the output literal of a gate.
///
/// # Note
///
/// This exists to make explicit gate outputs more visible in callees.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Output(pub Lit);

impl From<Output> for Lit {
    fn from(output: Output) -> Lit {
        output.0
    }
}

/// Wraps a literal generator and a raw gate encoder to provide
/// a convenient interface to the raw gate encoder.
pub struct GateEncoder<G, E>
where
    G: LitGen,
    E: RawGateEncoder,
{
    /// The literal generator.
    lit_gen: G,
    /// The gate encoder.
    enc: E,
}

impl<G, E> GateEncoder<G, E>
where
    G: LitGen,
    E: RawGateEncoder,
{
    /// Create a new gate encoder.
    pub fn new(lit_gen: G, enc: E) -> Self {
        Self { lit_gen, enc }
    }

    /// Generate and return a new single literal.
    ///
    /// # Note
    ///
    /// For more information look at
    /// [`RawGateEncoder::new_lit`](struct.RawGateEncoder.html#method.new_lit).
    pub fn new_lit(&self) -> Lit {
        self.lit_gen.new_lit()
    }

    /// Generate and return a literal pack.
    ///
    /// # Note
    ///
    /// For more information look at
    /// [`RawGateEncoder::new_lit_pack`](struct.RawGateEncoder.html#method.new_lit_pack).
    pub fn new_lit_pack(&self, size: usize) -> LitPack {
        self.lit_gen.new_lit_pack(size)
    }

    /// Define an AND gate with the given literals and the given output.
    ///
    /// # Panics
    ///
    /// If `lits` yields less than 2 literals.
    ///
    /// # Note
    ///
    /// For more information look at
    /// [`RawGateEncoder::and_gate`](struct.RawGateEncoder.html#method.and_gate).
    pub fn and_with_output<I, L>(&self, lits: I, output: Output)
    where
        I: IntoIterator<Item = L>,
        L: Into<Lit>,
    {
        self.enc
            .and_gate(output.into(), lits.into_iter().map(Into::into))
    }

    /// Define an AND gate with an implicit output.
    /// The generated output is returned to allow for nesting of gates.
    ///
    /// # Panics
    ///
    /// If `lits` yields less than 2 literals.
    pub fn and<I, L>(&self, lits: I) -> Lit
    where
        I: IntoIterator<Item = L>,
        L: Into<Lit>,
    {
        let output = self.lit_gen.new_lit();
        self.and_with_output(lits, Output(output));
        output
    }

    /// Define an OR gate with the given literals and the given output.
    ///
    /// # Panics
    ///
    /// If `lits` yields less than 2 literals.
    ///
    /// # Note
    ///
    /// For more information look at
    /// [`RawGateEncoder::or_gate`](struct.RawGateEncoder.html#method.or_gate).
    pub fn or_with_output<I, L>(&self, lits: I, output: Output)
    where
        I: IntoIterator<Item = L>,
        L: Into<Lit>,
    {
        self.enc
            .or_gate(output.into(), lits.into_iter().map(Into::into))
    }

    /// Define an OR gate with an implicit output.
    /// The generated output is returned to allow for nesting of gates.
    ///
    /// # Panics
    ///
    /// If `lits` yields less than 2 literals.
    pub fn or<I, L>(&self, lits: I) -> Lit
    where
        I: IntoIterator<Item = L>,
        L: Into<Lit>,
    {
        let output = self.lit_gen.new_lit();
        self.or_with_output(lits, Output(output));
        output
    }

    /// Define an XOR gate with the given literals and the given output.
    ///
    /// # Note
    ///
    /// For more information look at
    /// [`RawGateEncoder::xor_gate`](struct.RawGateEncoder.html#method.xor_gate).
    pub fn xor_with_output<L1, L2>(&self, lhs: L1, rhs: L2, output: Output)
    where
        L1: Into<Lit>,
        L2: Into<Lit>,
    {
        self.enc.xor_gate(output.into(), lhs.into(), rhs.into())
    }

    /// Define an XOR gate with an implicit output.
    /// The generated output is returned to allow for nesting of gates.
    pub fn xor<L1, L2>(&self, lhs: L1, rhs: L2) -> Lit
    where
        L1: Into<Lit>,
        L2: Into<Lit>,
    {
        let output = self.lit_gen.new_lit();
        self.xor_with_output(lhs.into(), rhs.into(), Output(output));
        output
    }

    /// Define an IMPLIES gate with the given literals and the given output.
    ///
    /// # Note
    ///
    /// For more information look at
    /// [`RawGateEncoder::implies_gate`](struct.RawGateEncoder.html#method.implies_gate).
    pub fn implies_with_output<L1, L2>(&self, lhs: L1, rhs: L2, output: Output)
    where
        L1: Into<Lit>,
        L2: Into<Lit>,
    {
        self.enc.implies_gate(output.into(), lhs.into(), rhs.into())
    }

    /// Define an IMPLIES gate with an implicit output.
    /// The generated output is returned to allow for nesting of gates.
    pub fn implies<L1, L2>(&self, lhs: L1, rhs: L2) -> Lit
    where
        L1: Into<Lit>,
        L2: Into<Lit>,
    {
        let output = self.lit_gen.new_lit();
        self.implies_with_output(lhs.into(), rhs.into(), Output(output));
        output
    }

    /// Define an IFF (If-And-Only-If) gate with the given literals and the given output.
    ///
    /// # Note
    ///
    /// For more information look at
    /// [`RawGateEncoder::iff_gate`](struct.RawGateEncoder.html#method.iff_gate).
    pub fn iff_with_output<L1, L2>(&self, lhs: L1, rhs: L2, output: Output)
    where
        L1: Into<Lit>,
        L2: Into<Lit>,
    {
        self.enc.iff_gate(output.into(), lhs.into(), rhs.into())
    }

    /// Define an IFF (If-And-Only-Iff) gate with an implicit output.
    /// The generated output is returned to allow for nesting of gates.
    pub fn iff<L1, L2>(&self, lhs: L1, rhs: L2) -> Lit
    where
        L1: Into<Lit>,
        L2: Into<Lit>,
    {
        let output = self.lit_gen.new_lit();
        self.iff_with_output(lhs.into(), rhs.into(), Output(output));
        output
    }

    /// Define a NOT gate for the given output and input literals.
    ///
    /// # Note
    ///
    /// For more information look at
    /// [`RawGateEncoder::not_gate`](struct.RawGateEncoder.html#method.not_gate).
    pub fn not_with_output<L>(&self, input: L, output: Output)
    where
        L: Into<Lit>,
    {
        self.enc.not_gate(output.into(), input.into())
    }

    /// Define a NOT gate for the given output and input literals.
    /// The generated output is returned to allow for nesting of gates.
    pub fn not<L>(&self, input: L) -> Lit
    where
        L: Into<Lit>,
    {
        let output = self.lit_gen.new_lit();
        self.not_with_output(input.into(), Output(output));
        output
    }

    /// Define an EQUALS gate for the given output and input literals.
    ///
    /// # Note
    ///
    /// For more information look at
    /// [`RawGateEncoder::eq_gate`](struct.RawGateEncoder.html#method.eq_gate).
    pub fn eq_with_output<L>(&self, input: L, output: Output)
    where
        L: Into<Lit>,
    {
        self.enc.eq_gate(output.into(), input.into())
    }

    /// Define an EQUALS gate for the given output and input literals.
    /// The generated output is returned to allow for nesting of gates.
    pub fn eq<L>(&self, input: L) -> Lit
    where
        L: Into<Lit>,
    {
        let output = self.lit_gen.new_lit();
        self.eq_with_output(input.into(), Output(output));
        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod output {
        use super::*;
        use repr::Var;

        #[test]
        fn into_lit() {
            assert_eq!(
                Lit::from(Output(Lit::pos(Var::new(1).unwrap()))),
                Lit::pos(Var::new(1).unwrap())
            );
        }
    }
}
