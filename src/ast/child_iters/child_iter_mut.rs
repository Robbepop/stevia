use ast::prelude::*;

use std::slice;
use std::cmp;
use std::mem;

/// Re-exports commonly used items of this module.
pub mod prelude {
    pub use super::{
		ChildsIterMut	
	};
}

/// Iterator over mutable child expressions.
#[derive(Debug)]
pub enum ChildsIterMut<'p> {
    Inl(InlChildsIterMut<'p>),
    Ext(ExtChildsIterMut<'p>)
}

#[derive(Debug)]
pub struct InlChildsIterMut<'p> {
    childs: [Option<&'p mut AnyExpr>; 3],
    begin: usize,
	end: usize
}

impl<'p> InlChildsIterMut<'p> {
    fn from_array(num_childs: usize, childs: [Option<&'p mut AnyExpr>; 3]) -> InlChildsIterMut {
        InlChildsIterMut{childs, begin: 0, end: num_childs.saturating_sub(1)}
    }

    pub fn none() -> InlChildsIterMut<'p> {
        InlChildsIterMut::from_array(0, [None, None, None])
    }

	pub fn unary(fst: &'p mut AnyExpr) -> InlChildsIterMut<'p> {
		InlChildsIterMut::from_array(1, [Some(fst), None, None])
	}

	pub fn binary(fst: &'p mut AnyExpr, snd: &'p mut AnyExpr) -> InlChildsIterMut<'p> {
		InlChildsIterMut::from_array(2, [Some(fst), Some(snd), None])
	}

	pub fn ternary(fst: &'p mut AnyExpr, snd: &'p mut AnyExpr, trd: &'p mut AnyExpr) -> InlChildsIterMut<'p> {
		InlChildsIterMut::from_array(3, [Some(fst), Some(snd), Some(trd)])
	}
}

impl<'p> Iterator for InlChildsIterMut<'p> {
    type Item = &'p mut AnyExpr;

    fn next(&mut self) -> Option<Self::Item> {
        // FIXME: Using replace here is a hack to fight the borrow-checker but works for now!
        let elem = mem::replace(&mut self.childs[self.begin], None);
        self.begin = cmp::min(self.begin + 1, 2);
        elem
    }
}

impl<'p> DoubleEndedIterator for InlChildsIterMut<'p> {
    fn next_back(&mut self) -> Option<Self::Item> {
        // FIXME: Using replace here is a hack to fight the borrow-checker but works for now!
        let elem = mem::replace(&mut self.childs[self.end], None);
        self.end = self.end.saturating_sub(1);
        elem
    }
}

#[derive(Debug)]
pub struct ExtChildsIterMut<'p> {
    childs: slice::IterMut<'p, AnyExpr>
}

impl<'p> ExtChildsIterMut<'p> {
    fn from_slice(childs: &'p mut [AnyExpr]) -> ExtChildsIterMut {
        ExtChildsIterMut{childs: childs.into_iter()}
    }
}

impl<'p> Iterator for ExtChildsIterMut<'p> {
    type Item = &'p mut AnyExpr;

    fn next(&mut self) -> Option<Self::Item> {
        self.childs.next()
    }
}

impl<'p> DoubleEndedIterator for ExtChildsIterMut<'p> {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.childs.next_back()
	}
}

impl<'p> ChildsIterMut<'p> {
	pub fn none() -> ChildsIterMut<'p> {
        ChildsIterMut::Inl(InlChildsIterMut::none())
	}

	pub fn unary(fst: &'p mut AnyExpr) -> ChildsIterMut<'p> {
        ChildsIterMut::Inl(InlChildsIterMut::unary(fst))
	}

	pub fn binary(fst: &'p mut AnyExpr, snd: &'p mut AnyExpr) -> ChildsIterMut<'p> {
        ChildsIterMut::Inl(InlChildsIterMut::binary(fst, snd))
	}

	pub fn ternary(
		fst: &'p mut AnyExpr,
		snd: &'p mut AnyExpr,
		trd: &'p mut AnyExpr) -> ChildsIterMut<'p>
	{
		ChildsIterMut::Inl(InlChildsIterMut::ternary(fst, snd, trd))
	}

	pub fn nary(childs: &'p mut [AnyExpr]) -> ChildsIterMut<'p> {
		ChildsIterMut::Ext(ExtChildsIterMut::from_slice(childs))
	}
}

impl<'p> Iterator for ChildsIterMut<'p> {
	type Item = &'p mut AnyExpr;

	fn next(&mut self) -> Option<Self::Item> {
		use self::ChildsIterMut::*;
		match *self {
			Inl(ref mut iter) => iter.next(),
			Ext(ref mut iter) => iter.next()
		}
	}
}

impl<'p> DoubleEndedIterator for ChildsIterMut<'p> {
	fn next_back(&mut self) -> Option<Self::Item> {
		use self::ChildsIterMut::*;
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
		let mut iter = bool_const.childs_mut();
		assert_eq!(iter.next(), None)
	}

	#[test]
	fn unary() {
		let b = PlainExprTreeBuilder::default();
		let mut expr = b.not(b.bool_const(false)).unwrap();
		let mut iter = expr.childs_mut();
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
		let mut iter = expr.childs_mut();
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
		let mut iter = expr.childs_mut();
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
		let mut iter = expr.childs_mut();
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
		let mut iter = expr.childs_mut();
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_back() {
		let mut expr = big_test_expr();
		let mut iter = expr.childs_mut();
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
		let mut iter = expr.childs_mut();
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_and_next_back() {
		let mut expr = big_test_expr();
		let mut iter = expr.childs_mut();
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(0))));
		assert_eq!(iter.next(), Some(&mut AnyExpr::from(expr::BitvecConst::from(1337))));
		assert_eq!(iter.next_back(), Some(&mut AnyExpr::from(expr::BitvecConst::from(77))));
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}
}
