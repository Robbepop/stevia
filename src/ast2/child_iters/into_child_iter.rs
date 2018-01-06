use ast2::prelude::*;

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
	childs: smallvec::IntoIter<[Expr; 3]>
}

impl FromIterator<Expr> for IntoChildsIter {
    fn from_iter<T>(iter: T) -> IntoChildsIter
        where T: IntoIterator<Item = Expr>
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

	pub fn unary(fst: Expr) -> IntoChildsIter {
		let mut vec = smallvec::SmallVec::new();
		vec.push(fst);
		IntoChildsIter{
			childs: vec.into_iter()
		}
	}

	pub fn binary(fst: Expr, snd: Expr) -> IntoChildsIter {
		let mut vec = smallvec::SmallVec::new();
		vec.push(fst);
		vec.push(snd);
		IntoChildsIter{
			childs: vec.into_iter()
		}
	}

	pub fn ternary(fst: Expr, snd: Expr, trd: Expr) -> IntoChildsIter {
		let mut vec = smallvec::SmallVec::new();
		vec.push(fst);
		vec.push(snd);
		vec.push(trd);
		IntoChildsIter{
			childs: vec.into_iter()
		}
	}

	pub fn nary(childs: Vec<Expr>) -> IntoChildsIter {
		IntoChildsIter::from_iter(childs)
	}
}

impl Iterator for IntoChildsIter {
	type Item = Expr;

	fn next(&mut self) -> Option<Self::Item> {
		self.childs.next()
	}
}
