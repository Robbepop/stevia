use crate::prelude::*;

use std::slice;
use std::cmp;
use std::mem;

/// Re-exports commonly used items of this module.
pub mod prelude {
    pub use super::{
		ChildrenIter	
	};
}

/// Iterator over immutable child expressions.
#[derive(Debug, Clone)]
pub enum ChildrenIter<'p> {
    Inl(InlChildrenIter<'p>),
    Ext(ExtChildrenIter<'p>)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InlChildrenIter<'p> {
    children: [Option<&'p AnyExpr>; 3],
    begin: usize,
	end: usize
}

impl<'p> InlChildrenIter<'p> {
    fn from_array(num_children: usize, children: [Option<&'p AnyExpr>; 3]) -> InlChildrenIter {
        InlChildrenIter{children, begin: 0, end: num_children.saturating_sub(1)}
    }

    pub fn none() -> InlChildrenIter<'p> {
        InlChildrenIter::from_array(0, [None; 3])
    }

	pub fn unary(fst: &'p AnyExpr) -> InlChildrenIter<'p> {
		InlChildrenIter::from_array(1, [Some(fst), None, None])
	}

	pub fn binary(fst: &'p AnyExpr, snd: &'p AnyExpr) -> InlChildrenIter<'p> {
		InlChildrenIter::from_array(2, [Some(fst), Some(snd), None])
	}

	pub fn ternary(fst: &'p AnyExpr, snd: &'p AnyExpr, trd: &'p AnyExpr) -> InlChildrenIter<'p> {
		InlChildrenIter::from_array(3, [Some(fst), Some(snd), Some(trd)])
	}
}

impl<'p> Iterator for InlChildrenIter<'p> {
    type Item = &'p AnyExpr;

    fn next(&mut self) -> Option<Self::Item> {
        // Using replace here is a trick to enable efficient correct
		// iteration using `Iterator` and `DoubleEndedIterator` so
		// that no element is yielded twice.
        let elem = mem::replace(&mut self.children[self.begin], None);
        self.begin = cmp::min(self.begin + 1, 2);
        elem
    }
}

impl<'p> DoubleEndedIterator for InlChildrenIter<'p> {
    fn next_back(&mut self) -> Option<Self::Item> {
        // Using replace here is a trick to enable efficient correct
		// iteration using `Iterator` and `DoubleEndedIterator` so
		// that no element is yielded twice.
        let elem = mem::replace(&mut self.children[self.end], None);
        self.end = self.end.saturating_sub(1);
        elem
    }
}

#[derive(Debug, Clone)]
pub struct ExtChildrenIter<'p> {
    children: slice::Iter<'p, AnyExpr>
}

impl<'p> ExtChildrenIter<'p> {
    fn from_slice(children: &'p [AnyExpr]) -> ExtChildrenIter {
        ExtChildrenIter{children: children.into_iter()}
    }
}

impl<'p> Iterator for ExtChildrenIter<'p> {
    type Item = &'p AnyExpr;

    fn next(&mut self) -> Option<Self::Item> {
        self.children.next()
    }
}

impl<'p> DoubleEndedIterator for ExtChildrenIter<'p> {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.children.next_back()
	}
}

impl<'p> ChildrenIter<'p> {
	pub fn none() -> ChildrenIter<'p> {
        ChildrenIter::Inl(InlChildrenIter::none())
	}

	pub fn unary(fst: &'p AnyExpr) -> ChildrenIter<'p> {
        ChildrenIter::Inl(InlChildrenIter::unary(fst))
	}

	pub fn binary(fst: &'p AnyExpr, snd: &'p AnyExpr) -> ChildrenIter<'p> {
        ChildrenIter::Inl(InlChildrenIter::binary(fst, snd))
	}

	pub fn ternary(
		fst: &'p AnyExpr,
		snd: &'p AnyExpr,
		trd: &'p AnyExpr) -> ChildrenIter<'p>
	{
		ChildrenIter::Inl(InlChildrenIter::ternary(fst, snd, trd))
	}

	pub fn nary(children: &'p [AnyExpr]) -> ChildrenIter<'p> {
		ChildrenIter::Ext(ExtChildrenIter::from_slice(children))
	}
}

impl<'p> Iterator for ChildrenIter<'p> {
	type Item = &'p AnyExpr;

	fn next(&mut self) -> Option<Self::Item> {
		use self::ChildrenIter::*;
		match *self {
			Inl(ref mut iter) => iter.next(),
			Ext(ref mut iter) => iter.next()
		}
	}
}

impl<'p> DoubleEndedIterator for ChildrenIter<'p> {
	fn next_back(&mut self) -> Option<Self::Item> {
		use self::ChildrenIter::*;
		match *self {
			Inl(ref mut iter) => iter.next_back(),
			Ext(ref mut iter) => iter.next_back()
		}
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
		let expr = b.and(
			b.bool_const(false),
			b.bool_const(true)
		).unwrap();
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
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BitvecConst::from(5))));
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
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BitvecConst::from(1337))));
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BitvecConst::from(77))));
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BitvecConst::from(0))));
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next(), None);
	}

	#[test]
	fn ternary_next_back() {
		let expr = test_cond();
		let mut iter = expr.children();
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_back() {
		let expr = big_test_expr();
		let mut iter = expr.children();
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(0))));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(77))));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(1337))));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn ternary_next_and_next_back() {
		let expr = test_cond();
		let mut iter = expr.children();
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_and_next_back() {
		let expr = big_test_expr();
		let mut iter = expr.children();
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(0))));
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BitvecConst::from(1337))));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(77))));
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}
}
