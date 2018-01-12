use ast2::prelude::*;

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
        let elem = mem::replace(&mut self.childs[self.end], None);
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
