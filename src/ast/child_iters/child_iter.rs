use ast::prelude::*;

use std::slice;
use std::cmp;
use std::mem;

/// Re-exports commonly used items of this module.
pub mod prelude {
    pub use super::{
		ChildsIter	
	};
}

/// Iterator over immutable child expressions.
#[derive(Debug, Clone)]
pub enum ChildsIter<'p> {
    Inl(InlChildsIter<'p>),
    Ext(ExtChildsIter<'p>)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InlChildsIter<'p> {
    childs: [Option<&'p AnyExpr>; 3],
    begin: usize,
	end: usize
}

impl<'p> InlChildsIter<'p> {
    fn from_array(num_childs: usize, childs: [Option<&'p AnyExpr>; 3]) -> InlChildsIter {
        InlChildsIter{childs, begin: 0, end: num_childs.saturating_sub(1)}
    }

    pub fn none() -> InlChildsIter<'p> {
        InlChildsIter::from_array(0, [None; 3])
    }

	pub fn unary(fst: &'p AnyExpr) -> InlChildsIter<'p> {
		InlChildsIter::from_array(1, [Some(fst), None, None])
	}

	pub fn binary(fst: &'p AnyExpr, snd: &'p AnyExpr) -> InlChildsIter<'p> {
		InlChildsIter::from_array(2, [Some(fst), Some(snd), None])
	}

	pub fn ternary(fst: &'p AnyExpr, snd: &'p AnyExpr, trd: &'p AnyExpr) -> InlChildsIter<'p> {
		InlChildsIter::from_array(3, [Some(fst), Some(snd), Some(trd)])
	}
}

impl<'p> Iterator for InlChildsIter<'p> {
    type Item = &'p AnyExpr;

    fn next(&mut self) -> Option<Self::Item> {
        // Using replace here is a trick to enable efficient correct
		// iteration using `Iterator` and `DoubleEndedIterator` so
		// that no element is yielded twice.
        let elem = mem::replace(&mut self.childs[self.begin], None);
        self.begin = cmp::min(self.begin + 1, 2);
        elem
    }
}

impl<'p> DoubleEndedIterator for InlChildsIter<'p> {
    fn next_back(&mut self) -> Option<Self::Item> {
        // Using replace here is a trick to enable efficient correct
		// iteration using `Iterator` and `DoubleEndedIterator` so
		// that no element is yielded twice.
        let elem = mem::replace(&mut self.childs[self.end], None);
        self.end = self.end.saturating_sub(1);
        elem
    }
}

#[derive(Debug, Clone)]
pub struct ExtChildsIter<'p> {
    childs: slice::Iter<'p, AnyExpr>
}

impl<'p> ExtChildsIter<'p> {
    fn from_slice(childs: &'p [AnyExpr]) -> ExtChildsIter {
        ExtChildsIter{childs: childs.into_iter()}
    }
}

impl<'p> Iterator for ExtChildsIter<'p> {
    type Item = &'p AnyExpr;

    fn next(&mut self) -> Option<Self::Item> {
        self.childs.next()
    }
}

impl<'p> DoubleEndedIterator for ExtChildsIter<'p> {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.childs.next_back()
	}
}

impl<'p> ChildsIter<'p> {
	pub fn none() -> ChildsIter<'p> {
        ChildsIter::Inl(InlChildsIter::none())
	}

	pub fn unary(fst: &'p AnyExpr) -> ChildsIter<'p> {
        ChildsIter::Inl(InlChildsIter::unary(fst))
	}

	pub fn binary(fst: &'p AnyExpr, snd: &'p AnyExpr) -> ChildsIter<'p> {
        ChildsIter::Inl(InlChildsIter::binary(fst, snd))
	}

	pub fn ternary(
		fst: &'p AnyExpr,
		snd: &'p AnyExpr,
		trd: &'p AnyExpr) -> ChildsIter<'p>
	{
		ChildsIter::Inl(InlChildsIter::ternary(fst, snd, trd))
	}

	pub fn nary(childs: &'p [AnyExpr]) -> ChildsIter<'p> {
		ChildsIter::Ext(ExtChildsIter::from_slice(childs))
	}
}

impl<'p> Iterator for ChildsIter<'p> {
	type Item = &'p AnyExpr;

	fn next(&mut self) -> Option<Self::Item> {
		use self::ChildsIter::*;
		match *self {
			Inl(ref mut iter) => iter.next(),
			Ext(ref mut iter) => iter.next()
		}
	}
}

impl<'p> DoubleEndedIterator for ChildsIter<'p> {
	fn next_back(&mut self) -> Option<Self::Item> {
		use self::ChildsIter::*;
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
		let mut iter = bool_const.childs();
		assert_eq!(iter.next(), None)
	}

	#[test]
	fn unary() {
		let b = PlainExprTreeBuilder::default();
		let expr = b.not(b.bool_const(false)).unwrap();
		let mut iter = expr.childs();
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
		let mut iter = expr.childs();
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
		let mut iter = expr.childs();
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
		let mut iter = expr.childs();
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
		let mut iter = expr.childs();
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_back() {
		let expr = big_test_expr();
		let mut iter = expr.childs();
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
		let mut iter = expr.childs();
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BoolConst::f())));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}

	#[test]
	fn nary_next_and_next_back() {
		let expr = big_test_expr();
		let mut iter = expr.childs();
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(5))));
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BitvecConst::from(42))));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(0))));
		assert_eq!(iter.next(), Some(&AnyExpr::from(expr::BitvecConst::from(1337))));
		assert_eq!(iter.next_back(), Some(&AnyExpr::from(expr::BitvecConst::from(77))));
		assert_eq!(iter.next(), None);
		assert_eq!(iter.next_back(), None);
	}
}
