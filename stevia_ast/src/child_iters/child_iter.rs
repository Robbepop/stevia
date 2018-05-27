use crate::prelude::*;

use std::mem;
use std::slice;

/// Iterator over mutable child expressions.
#[derive(Debug, Clone)]
pub struct ChildrenIter<'p> {
	kind: ChildrenIterKind<'p>,
}

impl<'p> ChildrenIter<'p> {
	fn from_kind(kind: ChildrenIterKind<'p>) -> Self {
		Self { kind }
	}

	/// Create an empty iterator.
	pub fn none() -> Self {
		Self::from_kind(ChildrenIterKind::from(InlChildrenIter::none()))
	}

	/// Create an iterator that yields only `fst`.
	pub fn unary(fst: &'p AnyExpr) -> Self {
		Self::from_kind(ChildrenIterKind::from(InlChildrenIter::unary(fst)))
	}

	/// Create an iterator that yields `fst` and `snd`.
	pub fn binary(fst: &'p AnyExpr, snd: &'p AnyExpr) -> Self {
		Self::from_kind(ChildrenIterKind::from(InlChildrenIter::binary(fst, snd)))
	}

	/// Create an iterator that yields `fst`, `snd` and `trd`.
	pub fn ternary(fst: &'p AnyExpr, snd: &'p AnyExpr, trd: &'p AnyExpr) -> Self {
		Self::from_kind(ChildrenIterKind::from(InlChildrenIter::ternary(
			fst, snd, trd,
		)))
	}

	/// Create an iterator that yields all children within the given slice.
	pub fn nary(children: &'p [AnyExpr]) -> Self {
		Self::from_kind(ChildrenIterKind::from(ExtChildrenIter::from_slice(
			children,
		)))
	}
}

impl<'p> Iterator for ChildrenIter<'p> {
	type Item = &'p AnyExpr;

	fn next(&mut self) -> Option<Self::Item> {
		use self::ChildrenIterKind::*;
		match &mut self.kind {
			Inl(iter) => iter.next(),
			Ext(iter) => iter.next(),
		}
	}
}

impl<'p> DoubleEndedIterator for ChildrenIter<'p> {
	fn next_back(&mut self) -> Option<Self::Item> {
		use self::ChildrenIterKind::*;
		match &mut self.kind {
			Inl(iter) => iter.next_back(),
			Ext(iter) => iter.next_back(),
		}
	}
}

/// Iterator over mutable child expressions.
#[derive(Debug, Clone)]
enum ChildrenIterKind<'p> {
	Inl(InlChildrenIter<'p>),
	Ext(ExtChildrenIter<'p>),
}

impl<'p> From<InlChildrenIter<'p>> for ChildrenIterKind<'p> {
	fn from(inl: InlChildrenIter<'p>) -> Self {
		ChildrenIterKind::Inl(inl)
	}
}

impl<'p> From<ExtChildrenIter<'p>> for ChildrenIterKind<'p> {
	fn from(ext: ExtChildrenIter<'p>) -> Self {
		ChildrenIterKind::Ext(ext)
	}
}

/// Iterator over mutable child expressions.
///
/// This represents the special case where there are only 3 or fewer children.
///
/// # Note
///
/// The remaining yielded elements are within the range `self.begin..self.end`.
#[derive(Debug, Copy, Clone)]
struct InlChildrenIter<'p> {
	children: [Option<&'p AnyExpr>; 3],
	begin: usize,
	end: usize,
}

impl<'p> InlChildrenIter<'p> {
	fn from_array(num_children: usize, children: [Option<&'p AnyExpr>; 3]) -> Self {
		InlChildrenIter {
			children,
			begin: 0,
			end: num_children,
		}
	}

	/// Create an empty iterator.
	pub fn none() -> Self {
		InlChildrenIter::from_array(0, [None, None, None])
	}

	/// Create an iterator that yields only `fst`.
	pub fn unary(fst: &'p AnyExpr) -> Self {
		InlChildrenIter::from_array(1, [Some(fst), None, None])
	}

	/// Create an iterator that yields `fst` and `snd`.
	pub fn binary(fst: &'p AnyExpr, snd: &'p AnyExpr) -> Self {
		InlChildrenIter::from_array(2, [Some(fst), Some(snd), None])
	}

	/// Create an iterator that yields `fst`, `snd` and `trd`.
	pub fn ternary(fst: &'p AnyExpr, snd: &'p AnyExpr, trd: &'p AnyExpr) -> Self {
		InlChildrenIter::from_array(3, [Some(fst), Some(snd), Some(trd)])
	}
}

impl<'p> Iterator for InlChildrenIter<'p> {
	type Item = &'p AnyExpr;

	fn next(&mut self) -> Option<Self::Item> {
		if self.begin == self.end {
			return None;
		}
		// FIXME: Using replace here is a hack to fight the borrow-checker but works for now!
		let elem = mem::replace(&mut self.children[self.begin], None);
		self.begin += 1;
		elem
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let remaining = self.end - self.begin;
		(remaining, Some(remaining))
	}
}

impl<'p> DoubleEndedIterator for InlChildrenIter<'p> {
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.begin == self.end {
			return None;
		}
		// FIXME: Using replace here is a hack to fight the borrow-checker but works for now!
		self.end -= 1;
		mem::replace(&mut self.children[self.end], None)
	}
}

/// Iterator over mutable child expressions.
///
/// This represents the special case where there are more than 3 children.
#[derive(Debug, Clone)]
struct ExtChildrenIter<'p> {
	children: slice::Iter<'p, AnyExpr>,
}

impl<'p> ExtChildrenIter<'p> {
	fn from_slice(children: &'p [AnyExpr]) -> Self {
		ExtChildrenIter {
			children: children.into_iter(),
		}
	}
}

impl<'p> Iterator for ExtChildrenIter<'p> {
	type Item = &'p AnyExpr;

	fn next(&mut self) -> Option<Self::Item> {
		self.children.next()
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.children.size_hint()
	}
}

impl<'p> DoubleEndedIterator for ExtChildrenIter<'p> {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.children.next_back()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn none() {
		let bool_const = expr::BoolConst::t();
		let mut iter = bool_const.children();
		assert_eq!(iter.next(), None)
	}

	#[test]
	fn unary() {
		let b = PlainExprTreeBuilder::default();
		let expr = b.not(b.bool_const(false)).unwrap();
		let mut iter = expr.children();
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next(), None);
	}

	#[test]
	fn binary() {
		let b = PlainExprTreeBuilder::default();
		let expr = b.and(b.bool_const(false), b.bool_const(true)).unwrap();
		let mut iter = expr.children();
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BoolConst::t())));
		assert_eq!(iter.next(), None);
	}

	fn test_cond() -> AnyExpr {
		let b = PlainExprTreeBuilder::default();
		b.cond(
			b.bool_const(false),
			b.bitvec_const(BitvecTy::w32(), 42),
			b.bitvec_const(BitvecTy::w32(), 5),
		).unwrap()
	}

	#[test]
	fn ternary() {
		let expr = test_cond();
		let mut iter = expr.children();
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(
			iter.next(),
			Some(&AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(
			iter.next(),
			Some(&AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(iter.next(), None);
	}

	fn big_test_expr() -> AnyExpr {
		let b = PlainExprTreeBuilder::default();
		b.bitvec_add_n(vec![
			b.bitvec_const(BitvecTy::w32(), 42),
			b.bitvec_const(BitvecTy::w32(), 1337),
			b.bitvec_const(BitvecTy::w32(), 77),
			b.bitvec_const(BitvecTy::w32(), 0),
			b.bitvec_const(BitvecTy::w32(), 5),
		]).unwrap()
	}

	#[test]
	fn nary() {
		let expr = big_test_expr();
		let mut iter = expr.children();
		assert_eq!(
			iter.next(),
			Some(&AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(
			iter.next(),
			Some(&AnyExpr::from(expr::BitvecConst::from(1337)))
		);
		assert_eq!(
			iter.next(),
			Some(&AnyExpr::from(expr::BitvecConst::from(77)))
		);
		assert_eq!(
			iter.next(),
			Some(&AnyExpr::from(expr::BitvecConst::from(0)))
		);
		assert_eq!(
			iter.next(),
			Some(&AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(iter.next(), None);
	}

	#[test]
	fn ternary_next_back() {
		let expr = test_cond();
		let mut iter = expr.children();
		assert_eq!(
			iter.next_back(),
			Some(&AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_back() {
		let expr = big_test_expr();
		let mut iter = expr.children();
		assert_eq!(
			iter.next_back(),
			Some(&AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&AnyExpr::from(expr::BitvecConst::from(0)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&AnyExpr::from(expr::BitvecConst::from(77)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&AnyExpr::from(expr::BitvecConst::from(1337)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn ternary_next_and_next_back() {
		let expr = test_cond();
		let mut iter = expr.children();
		assert_eq!(
			iter.next_back(),
			Some(&AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(
			iter.next_back(),
			Some(&AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_and_next_back() {
		let expr = big_test_expr();
		let mut iter = expr.children();
		assert_eq!(
			iter.next_back(),
			Some(&AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(
			iter.next(),
			Some(&AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&AnyExpr::from(expr::BitvecConst::from(0)))
		);
		assert_eq!(
			iter.next(),
			Some(&AnyExpr::from(expr::BitvecConst::from(1337)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&AnyExpr::from(expr::BitvecConst::from(77)))
		);
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}
}
