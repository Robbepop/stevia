use crate::prelude::*;

use smallvec;

use std::iter::FromIterator;

/// Consuming iterator over child expressions.
///
/// Can transform ownership.
pub struct IntoChildrenIter {
	children: smallvec::IntoIter<[AnyExpr; 3]>,
}

impl FromIterator<AnyExpr> for IntoChildrenIter {
	fn from_iter<T>(iter: T) -> IntoChildrenIter
	where
		T: IntoIterator<Item = AnyExpr>,
	{
		IntoChildrenIter {
			children: smallvec::SmallVec::from_iter(iter).into_iter(),
		}
	}
}

impl<'parent> IntoChildrenIter {
	/// Create an empty iterator.
	pub fn none() -> IntoChildrenIter {
		IntoChildrenIter::from_iter(vec![])
	}

	/// Create an iterator that yields only `fst`.
	pub fn unary(fst: AnyExpr) -> IntoChildrenIter {
		let mut vec = smallvec::SmallVec::new();
		vec.push(fst);
		IntoChildrenIter {
			children: vec.into_iter(),
		}
	}

	/// Create an iterator that yields `fst` and `snd`.
	pub fn binary(fst: AnyExpr, snd: AnyExpr) -> IntoChildrenIter {
		let mut vec = smallvec::SmallVec::new();
		vec.push(fst);
		vec.push(snd);
		IntoChildrenIter {
			children: vec.into_iter(),
		}
	}

	/// Create an iterator that yields `fst`, `snd` and `trd`.
	pub fn ternary(fst: AnyExpr, snd: AnyExpr, trd: AnyExpr) -> IntoChildrenIter {
		let mut vec = smallvec::SmallVec::new();
		vec.push(fst);
		vec.push(snd);
		vec.push(trd);
		IntoChildrenIter {
			children: vec.into_iter(),
		}
	}

	/// Create an iterator that yields all children within the given vector.
	pub fn nary(children: Vec<AnyExpr>) -> IntoChildrenIter {
		IntoChildrenIter::from_iter(children)
	}
}

impl Iterator for IntoChildrenIter {
	type Item = AnyExpr;

	fn next(&mut self) -> Option<Self::Item> {
		self.children.next()
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.children.size_hint()
	}
}

impl DoubleEndedIterator for IntoChildrenIter {
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
		let mut iter = bool_const.into_children();
		assert_eq!(iter.next(), None)
	}

	#[test]
	fn unary() {
		let b = PlainExprTreeBuilder::default();
		let expr = b.not(b.bool_const(false)).unwrap();
		let mut iter = expr.into_children();
		assert_eq!(iter.next(), Some(AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next(), None);
	}

	#[test]
	fn binary() {
		let b = PlainExprTreeBuilder::default();
		let expr = b.and(b.bool_const(false), b.bool_const(true)).unwrap();
		let mut iter = expr.into_children();
		assert_eq!(iter.next(), Some(AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next(), Some(AnyExpr::from(expr::BoolConst::t())));
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
		let mut iter = expr.into_children();
		assert_eq!(iter.next(), Some(AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(
			iter.next(),
			Some(AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(iter.next(), Some(AnyExpr::from(expr::BitvecConst::from(5))));
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
		let mut iter = expr.into_children();
		assert_eq!(
			iter.next(),
			Some(AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(
			iter.next(),
			Some(AnyExpr::from(expr::BitvecConst::from(1337)))
		);
		assert_eq!(
			iter.next(),
			Some(AnyExpr::from(expr::BitvecConst::from(77)))
		);
		assert_eq!(iter.next(), Some(AnyExpr::from(expr::BitvecConst::from(0))));
		assert_eq!(iter.next(), Some(AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next(), None);
	}

	#[test]
	fn ternary_next_back() {
		let expr = test_cond();
		let mut iter = expr.into_children();
		assert_eq!(
			iter.next_back(),
			Some(AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(
			iter.next_back(),
			Some(AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(iter.next_back(), Some(AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_back() {
		let expr = big_test_expr();
		let mut iter = expr.into_children();
		assert_eq!(
			iter.next_back(),
			Some(AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(
			iter.next_back(),
			Some(AnyExpr::from(expr::BitvecConst::from(0)))
		);
		assert_eq!(
			iter.next_back(),
			Some(AnyExpr::from(expr::BitvecConst::from(77)))
		);
		assert_eq!(
			iter.next_back(),
			Some(AnyExpr::from(expr::BitvecConst::from(1337)))
		);
		assert_eq!(
			iter.next_back(),
			Some(AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn ternary_next_and_next_back() {
		let expr = test_cond();
		let mut iter = expr.into_children();
		assert_eq!(
			iter.next_back(),
			Some(AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(iter.next(), Some(AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(
			iter.next_back(),
			Some(AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_and_next_back() {
		let expr = big_test_expr();
		let mut iter = expr.into_children();
		assert_eq!(
			iter.next_back(),
			Some(AnyExpr::from(expr::BitvecConst::from(5)))
		);
		assert_eq!(
			iter.next(),
			Some(AnyExpr::from(expr::BitvecConst::from(42)))
		);
		assert_eq!(
			iter.next_back(),
			Some(AnyExpr::from(expr::BitvecConst::from(0)))
		);
		assert_eq!(
			iter.next(),
			Some(AnyExpr::from(expr::BitvecConst::from(1337)))
		);
		assert_eq!(
			iter.next_back(),
			Some(AnyExpr::from(expr::BitvecConst::from(77)))
		);
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}
}
