use crate::prelude::*;

use std::slice;

/// Iterator over mutable child expressions.
///
/// This represents the special case where there are more than 3 children.
#[derive(Debug, Clone)]
pub struct ChildrenIter<'p> {
	children: slice::Iter<'p, AnyExpr>,
}

impl<'p> ChildrenIter<'p> {
	fn from_slice(children: &'p [AnyExpr]) -> Self {
		ChildrenIter {
			children: children.into_iter(),
		}
	}

	/// Create an empty iterator.
	pub fn none() -> Self {
		Self::from_slice(&[])
	}

	/// Create an iterator that yields only `fst`.
	pub fn unary(fst: &'p AnyExpr) -> Self {
		Self::from_slice(unsafe {
			std::slice::from_raw_parts(fst as *const AnyExpr, 1)
		})
	}

	/// Create an iterator that yields all children within the given slice.
	pub fn nary(children: &'p [AnyExpr]) -> Self {
		Self::from_slice(children)
	}
}

impl<'p> Iterator for ChildrenIter<'p> {
	type Item = &'p AnyExpr;

	fn next(&mut self) -> Option<Self::Item> {
		self.children.next()
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.children.size_hint()
	}
}

impl<'p> DoubleEndedIterator for ChildrenIter<'p> {
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
