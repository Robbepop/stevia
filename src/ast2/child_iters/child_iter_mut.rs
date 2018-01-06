use ast2::prelude::*;

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
    childs: [Option<&'p mut Expr>; 3],
    cur: usize
}

impl<'p> InlChildsIterMut<'p> {
    fn from_array(childs: [Option<&'p mut Expr>; 3]) -> InlChildsIterMut {
        InlChildsIterMut{childs, cur: 0}
    }

    pub fn none() -> InlChildsIterMut<'p> {
        InlChildsIterMut::from_array([None, None, None])
    }

	pub fn unary(fst: &'p mut Expr) -> InlChildsIterMut<'p> {
		InlChildsIterMut::from_array([Some(fst), None, None])
	}

	pub fn binary(fst: &'p mut Expr, snd: &'p mut Expr) -> InlChildsIterMut<'p> {
		InlChildsIterMut::from_array([Some(fst), Some(snd), None])
	}

	pub fn ternary(fst: &'p mut Expr, snd: &'p mut Expr, trd: &'p mut Expr) -> InlChildsIterMut<'p> {
		InlChildsIterMut::from_array([Some(fst), Some(snd), Some(trd)])
	}
}

impl<'p> Iterator for InlChildsIterMut<'p> {
    type Item = &'p mut Expr;

    fn next(&mut self) -> Option<Self::Item> {
        // FIXME: Ugly hack to fight the borrow-checker but works for now!
        let elem = mem::replace(&mut self.childs[self.cur], None);
        self.cur = cmp::min(self.cur + 1, 2);
        elem
    }
}

#[derive(Debug)]
pub struct ExtChildsIterMut<'p> {
    childs: slice::IterMut<'p, Expr>
}

impl<'p> ExtChildsIterMut<'p> {
    fn from_slice(childs: &'p mut [Expr]) -> ExtChildsIterMut {
        ExtChildsIterMut{childs: childs.into_iter()}
    }
}

impl<'p> Iterator for ExtChildsIterMut<'p> {
    type Item = &'p mut Expr;

    fn next(&mut self) -> Option<Self::Item> {
        self.childs.next()
    }
}

impl<'p> ChildsIterMut<'p> {
	pub fn none() -> ChildsIterMut<'p> {
        ChildsIterMut::Inl(InlChildsIterMut::none())
	}

	pub fn unary(fst: &'p mut Expr) -> ChildsIterMut<'p> {
        ChildsIterMut::Inl(InlChildsIterMut::unary(fst))
	}

	pub fn binary(fst: &'p mut Expr, snd: &'p mut Expr) -> ChildsIterMut<'p> {
        ChildsIterMut::Inl(InlChildsIterMut::binary(fst, snd))
	}

	pub fn ternary(
		fst: &'p mut Expr,
		snd: &'p mut Expr,
		trd: &'p mut Expr) -> ChildsIterMut<'p>
	{
		ChildsIterMut::Inl(InlChildsIterMut::ternary(fst, snd, trd))
	}

	pub fn nary(childs: &'p mut [Expr]) -> ChildsIterMut<'p> {
		ChildsIterMut::Ext(ExtChildsIterMut::from_slice(childs))
	}
}

impl<'p> Iterator for ChildsIterMut<'p> {
	type Item = &'p mut Expr;

	fn next(&mut self) -> Option<Self::Item> {
		use self::ChildsIterMut::*;
		match *self {
			Inl(ref mut iter) => iter.next(),
			Ext(ref mut iter) => iter.next()
		}
	}
}
