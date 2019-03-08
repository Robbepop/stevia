use crate::reprs::{
	Lit,
	LitPack,
};

/// Types implementing this trait can generate literals.
pub trait GenLit {
	/// Generate and return a new unique single literal.
	fn gen_lit(&mut self) -> Lit;

	/// Generate and return a new literal pack with the given amount of literals.
	///
	/// # Note
	///
	/// - Literal packs are space optimized for up to 64 literals.
	///   They store a signed information for every literal and require
	///   much less space compared to managing all literals by their own.
	/// - The returned literal pack has positive polarity for all its literals.
	fn gen_lit_pack(&mut self, size: usize) -> LitPack;
}

/// Types implementing this trait can consume clauses, e.g. are SAT solvers or CNF formula builders.
pub trait ConsumeClause {
	/// Consumes the given CNF encoded clause.
	fn consume_clause<C, L>(&mut self, clause: C)
	where
		C: IntoIterator<Item = L>,
		L: Into<Lit>;
}
