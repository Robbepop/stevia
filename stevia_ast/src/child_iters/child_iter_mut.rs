use crate::prelude::*;

use std::slice;
use std::cmp;
use std::mem;

/// Re-exports commonly used items of this module.
pub mod prelude {
    pub use super::{
		ChildrenIterMut	
	};
}

/// Iterator over mutable child expressions.
#[derive(Debug)]
pub enum ChildrenIterMut<'p> {
    Inl(InlChildrenIterMut<'p>),
    Ext(ExtChildrenIterMut<'p>)
}

#[derive(Debug)]
pub struct InlChildrenIterMut<'p> {
    children: [Option<&'p mut AnyExpr>; 3],
    begin: usize,
	end: usize
}

impl<'p> InlChildrenIterMut<'p> {
    fn from_array(num_children: usize, children: [Option<&'p mut AnyExpr>; 3]) -> InlChildrenIterMut {
        InlChildrenIterMut{children, begin: 0, end: num_children.saturating_sub(1)}
    }

    pub fn none() -> InlChildrenIterMut<'p> {
        InlChildrenIterMut::from_array(0, [None, None, None])
    }

	pub fn unary(fst: &'p mut AnyExpr) -> InlChildrenIterMut<'p> {
		InlChildrenIterMut::from_array(1, [Some(fst), None, None])
	}

	pub fn binary(fst: &'p mut AnyExpr, snd: &'p mut AnyExpr) -> InlChildrenIterMut<'p> {
		InlChildrenIterMut::from_array(2, [Some(fst), Some(snd), None])
	}

	pub fn ternary(fst: &'p mut AnyExpr, snd: &'p mut AnyExpr, trd: &'p mut AnyExpr) -> InlChildrenIterMut<'p> {
		InlChildrenIterMut::from_array(3, [Some(fst), Some(snd), Some(trd)])
	}
}

impl<'p> Iterator for InlChildrenIterMut<'p> {
    type Item = &'p mut AnyExpr;

    fn next(&mut self) -> Option<Self::Item> {
        // FIXME: Using replace here is a hack to fight the borrow-checker but works for now!
        let elem = mem::replace(&mut self.children[self.begin], None);
        self.begin = cmp::min(self.begin + 1, 2);
        elem
    }
}

impl<'p> DoubleEndedIterator for InlChildrenIterMut<'p> {
    fn next_back(&mut self) -> Option<Self::Item> {
        // FIXME: Using replace here is a hack to fight the borrow-checker but works for now!
        let elem = mem::replace(&mut self.children[self.end], None);
        self.end = self.end.saturating_sub(1);
        elem
    }
}

#[derive(Debug)]
pub struct ExtChildrenIterMut<'p> {
    children: slice::IterMut<'p, AnyExpr>
}

impl<'p> ExtChildrenIterMut<'p> {
    fn from_slice(children: &'p mut [AnyExpr]) -> ExtChildrenIterMut {
        ExtChildrenIterMut{children: children.into_iter()}
    }
}

impl<'p> Iterator for ExtChildrenIterMut<'p> {
    type Item = &'p mut AnyExpr;

    fn next(&mut self) -> Option<Self::Item> {
        self.children.next()
    }
}

impl<'p> DoubleEndedIterator for ExtChildrenIterMut<'p> {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.children.next_back()
	}
}

impl<'p> ChildrenIterMut<'p> {
	pub fn none() -> ChildrenIterMut<'p> {
        ChildrenIterMut::Inl(InlChildrenIterMut::none())
	}

	pub fn unary(fst: &'p mut AnyExpr) -> ChildrenIterMut<'p> {
        ChildrenIterMut::Inl(InlChildrenIterMut::unary(fst))
	}

	pub fn binary(fst: &'p mut AnyExpr, snd: &'p mut AnyExpr) -> ChildrenIterMut<'p> {
        ChildrenIterMut::Inl(InlChildrenIterMut::binary(fst, snd))
	}

	pub fn ternary(
		fst: &'p mut AnyExpr,
		snd: &'p mut AnyExpr,
		trd: &'p mut AnyExpr) -> ChildrenIterMut<'p>
	{
		ChildrenIterMut::Inl(InlChildrenIterMut::ternary(fst, snd, trd))
	}

	pub fn nary(children: &'p mut [AnyExpr]) -> ChildrenIterMut<'p> {
		ChildrenIterMut::Ext(ExtChildrenIterMut::from_slice(children))
	}
}

impl<'p> Iterator for ChildrenIterMut<'p> {
	type Item = &'p mut AnyExpr;

	fn next(&mut self) -> Option<Self::Item> {
		use self::ChildrenIterMut::*;
		match *self {
			Inl(ref mut iter) => iter.next(),
			Ext(ref mut iter) => iter.next()
		}
	}
}

impl<'p> DoubleEndedIterator for ChildrenIterMut<'p> {
	fn next_back(&mut self) -> Option<Self::Item> {
		use self::ChildrenIterMut::*;
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
		let mut expr = b.and(
			b.bool_const(false),
			b.bool_const(true)
		).unwrap();
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
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BitvecConst::from(5))));
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
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BitvecConst::from(1337))));
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BitvecConst::from(77))));
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BitvecConst::from(0))));
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next(), None);
	}

	#[test]
	fn ternary_next_back() {
		let mut expr = test_cond();
		let mut iter = expr.children_mut();
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_back() {
		let mut expr = big_test_expr();
		let mut iter = expr.children_mut();
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(0))));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(77))));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(1337))));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn ternary_next_and_next_back() {
		let mut expr = test_cond();
		let mut iter = expr.children_mut();
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_and_next_back() {
		let mut expr = big_test_expr();
		let mut iter = expr.children_mut();
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(0))));
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BitvecConst::from(1337))));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(77))));
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}
}
