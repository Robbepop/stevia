use ast::prelude::*;

use smallvec;

use std::iter::FromIterator;

/// Re-exports commonly used items of this module.
pub mod prelude {
    pub use super::{
		IntoChildsIter	
	};
}

/// Consuming iterator over child expressions.
/// 
/// Can transform ownership.
pub struct IntoChildsIter {
	childs: smallvec::IntoIter<[AnyExpr; 3]>
}

impl FromIterator<AnyExpr> for IntoChildsIter {
    fn from_iter<T>(iter: T) -> IntoChildsIter
        where T: IntoIterator<Item = AnyExpr>
    {
        IntoChildsIter{
            childs: smallvec::SmallVec::from_iter(iter).into_iter()
        }
    }
}

impl<'parent> IntoChildsIter {
	pub fn none() -> IntoChildsIter {
        IntoChildsIter::from_iter(vec![])
	}

	pub fn unary(fst: AnyExpr) -> IntoChildsIter {
		let mut vec = smallvec::SmallVec::new();
		vec.push(fst);
		IntoChildsIter{
			childs: vec.into_iter()
		}
	}

	pub fn binary(fst: AnyExpr, snd: AnyExpr) -> IntoChildsIter {
		let mut vec = smallvec::SmallVec::new();
		vec.push(fst);
		vec.push(snd);
		IntoChildsIter{
			childs: vec.into_iter()
		}
	}

	pub fn ternary(fst: AnyExpr, snd: AnyExpr, trd: AnyExpr) -> IntoChildsIter {
		let mut vec = smallvec::SmallVec::new();
		vec.push(fst);
		vec.push(snd);
		vec.push(trd);
		IntoChildsIter{
			childs: vec.into_iter()
		}
	}

	pub fn nary(childs: Vec<AnyExpr>) -> IntoChildsIter {
		IntoChildsIter::from_iter(childs)
	}
}

impl Iterator for IntoChildsIter {
	type Item = AnyExpr;

	fn next(&mut self) -> Option<Self::Item> {
		self.childs.next()
	}
}

impl DoubleEndedIterator for IntoChildsIter {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.childs.next_back()
	}
}
