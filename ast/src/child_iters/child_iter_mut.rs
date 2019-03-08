use crate::AnyExpr;

use std::slice;

/// Iterator over mutable child expressions.
///
/// This represents the special case where there are more than 3 children.
#[derive(Debug)]
pub struct ChildrenIterMut<'p> {
	children: slice::IterMut<'p, AnyExpr>,
}

impl<'p> ChildrenIterMut<'p> {
	/// Creates a children iterator for the given slice.
	#[inline]
	pub fn from_slice(children: &'p mut [AnyExpr]) -> Self {
		ChildrenIterMut {
			children: children.iter_mut(),
		}
	}
}

impl<'p> Iterator for ChildrenIterMut<'p> {
	type Item = &'p mut AnyExpr;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.children.next()
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.children.size_hint()
	}
}

impl<'p> DoubleEndedIterator for ChildrenIterMut<'p> {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		self.children.next_back()
	}
}

impl<'p> ExactSizeIterator for ChildrenIterMut<'p> {}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{expr, BitvecTy, PlainExprTreeBuilder, ChildrenMut};

	#[test]
	fn none() {
		let mut bool_const = expr::BoolConst::t();
		let mut iter = bool_const.children_mut();
		assert_eq!(iter.next(), None)
	}

	#[test]
	fn unary() {
		let b = PlainExprTreeBuilder::default();
		let mut expr = b.not(b.bool_const(false)).unwrap();
		let mut iter = expr.children_mut();
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next(), None);
	}

	#[test]
	fn binary() {
		let b = PlainExprTreeBuilder::default();
		let mut expr = b.and(b.bool_const(false), b.bool_const(true)).unwrap();
		let mut iter = expr.children_mut();
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BoolConst::t())));
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
		let mut expr = test_cond();
		let mut iter = expr.children_mut();
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(
			iter.next(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(
			iter.next(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(5)))
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
		let mut expr = big_test_expr();
		let mut iter = expr.children_mut();
		assert_eq!(
			iter.next(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(
			iter.next(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(1337)))
		);
		assert_eq!(
			iter.next(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(77)))
		);
		assert_eq!(
			iter.next(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(0)))
		);
		assert_eq!(
			iter.next(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(iter.next(), None);
	}

	#[test]
	fn ternary_next_back() {
		let mut expr = test_cond();
		let mut iter = expr.children_mut();
		assert_eq!(
			iter.next_back(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&mut AnyExpr::from(expr::BoolConst::f()))
		);
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_back() {
		let mut expr = big_test_expr();
		let mut iter = expr.children_mut();
		assert_eq!(
			iter.next_back(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(0)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(77)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(1337)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn ternary_next_and_next_back() {
		let mut expr = test_cond();
		let mut iter = expr.children_mut();
		assert_eq!(
			iter.next_back(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(
			iter.next_back(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_and_next_back() {
		let mut expr = big_test_expr();
		let mut iter = expr.children_mut();
		assert_eq!(
			iter.next_back(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(
			iter.next(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(0)))
		);
		assert_eq!(
			iter.next(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(1337)))
		);
		assert_eq!(
			iter.next_back(),
			Some(&mut AnyExpr::from(expr::BitvecConst::from(77)))
		);
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}
}
