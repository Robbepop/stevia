use crate::{AnyExpr, iter::IntoChildren};

/// Iterator over the children of an expression.
///
/// # Note
///
/// This moves the children out of their parent expression.
pub struct IntoChildrenIter {
	/// The underlying iterator.
	iter: std::vec::IntoIter<AnyExpr>
}

impl IntoChildrenIter {
	/// Creates a consuming children iterator for the given expression.
	#[inline]
	pub fn from_expr<E>(expr: E) -> Self
	where
		E: IntoChildren
	{
		IntoChildrenIter{
			iter: expr.into_children_vec().into_iter()
		}
	}
}

impl Iterator for IntoChildrenIter {
	type Item = AnyExpr;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.iter.next()
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iter.size_hint()
	}
}

impl DoubleEndedIterator for IntoChildrenIter {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		self.iter.next_back()
	}
}

impl ExactSizeIterator for IntoChildrenIter {}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{expr, iter::IntoChildren, PlainExprTreeBuilder, ty::BitvecTy};

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
