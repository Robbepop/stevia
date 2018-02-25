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
