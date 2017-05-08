
use ast::variants::Expr;
use smallvec;

//=============================================================================
// ITERATOR: Childs
//=============================================================================

pub enum Childs<'parent> {
	Inline{
		data: [Option<&'parent Expr>; 3],
		pos : usize
	},
	Extern{
		iter: ::std::slice::Iter<'parent, Expr>
	}
}

impl<'parent> Childs<'parent> {
	pub fn none() -> Childs<'parent> {
		Childs::Inline{
			data: [None, None, None],
			pos : 0
		}
	}

	pub fn unary(inner: &'parent Expr) -> Childs<'parent> {
		Childs::Inline{
			data: [Some(inner), None, None],
			pos : 0
		}
	}

	pub fn binary(left: &'parent Expr, right: &'parent Expr) -> Childs<'parent> {
		Childs::Inline{
			data: [Some(left), Some(right), None],
			pos : 0
		}
	}

	pub fn ternary(
		fst: &'parent Expr,
		snd: &'parent Expr,
		trd: &'parent Expr) -> Childs<'parent>
	{
		Childs::Inline{
			data: [Some(fst), Some(snd), Some(trd)],
			pos : 0
		}
	}

	pub fn nary(childs: &'parent [Expr]) -> Childs<'parent> {
		Childs::Extern{ iter: childs.iter() }
	}
}

impl<'parent> Iterator for Childs<'parent> {
	type Item = &'parent Expr;

	fn next(&mut self) -> Option<Self::Item> {
		use self::Childs::*;
		match *self {
			Inline{ref data, ref mut pos} => {
				if *pos < 3 {
					let elem: Option<Self::Item> = data[*pos];
					*pos += 1;
					elem
				}
				else {
					None
				}
			},
			Extern{ref mut iter} => iter.next()
		}
	}
}

//=============================================================================
// ITERATOR: ChildsMut
//=============================================================================

pub enum ChildsMut<'parent> {
	Inline{
		data: [Option<&'parent mut Expr>; 3],
		pos : usize
	},
	Extern{
		iter: ::std::slice::IterMut<'parent, Expr>
	}
}

impl<'parent> ChildsMut<'parent> {
	pub fn none() -> ChildsMut<'parent> {
		ChildsMut::Inline{
			data: [None, None, None],
			pos : 0
		}
	}

	pub fn unary(inner: &'parent mut Expr) -> ChildsMut<'parent> {
		ChildsMut::Inline{
			data: [Some(inner), None, None],
			pos : 0
		}
	}

	pub fn binary(left: &'parent mut Expr, right: &'parent mut Expr) -> ChildsMut<'parent> {
		ChildsMut::Inline{
			data: [Some(left), Some(right), None],
			pos : 0
		}
	}

	pub fn ternary(
		fst: &'parent mut Expr,
		snd: &'parent mut Expr,
		trd: &'parent mut Expr) -> ChildsMut<'parent>
	{
		ChildsMut::Inline{
			data: [Some(fst), Some(snd), Some(trd)],
			pos : 0
		}
	}

	pub fn nary(childs: &'parent mut [Expr]) -> ChildsMut<'parent> {
		ChildsMut::Extern{ iter: childs.iter_mut() }
	}
}

impl<'parent> Iterator for ChildsMut<'parent> {
	type Item = &'parent mut Expr;

	fn next(&mut self) -> Option<Self::Item> {
		use self::ChildsMut::*;
		match *self {
			Inline{ref mut data, ref mut pos} => {
				if *pos < 3 {
					let old_pos = *pos;
					*pos += 1;
					// FIXME: ugly hack to fight the borrow-checker but works for now!
					::std::mem::replace(&mut data[old_pos], None)
				}
				else {
					None
				}
			},
			Extern{ref mut iter} => iter.next()
		}
	}
}

//=============================================================================
// ITERATOR: IntoChilds
//=============================================================================

pub struct IntoChilds {
	iter: smallvec::IntoIter<[Expr; 3]>
}

impl<'parent> IntoChilds {
	pub fn none() -> IntoChilds {
		IntoChilds{
			iter: smallvec::SmallVec::new().into_iter()
		}
	}

	pub fn unary(inner: Expr) -> IntoChilds {
		let mut vec = smallvec::SmallVec::new();
		vec.push(inner);
		IntoChilds{
			iter: vec.into_iter()
		}
	}

	pub fn binary(left: Expr, right: Expr) -> IntoChilds {
		let mut vec = smallvec::SmallVec::new();
		vec.push(left);
		vec.push(right);
		IntoChilds{
			iter: vec.into_iter()
		}
	}

	pub fn ternary(fst: Expr, snd: Expr, trd: Expr) -> IntoChilds {
		let mut vec = smallvec::SmallVec::new();
		vec.push(fst);
		vec.push(snd);
		vec.push(trd);
		IntoChilds{
			iter: vec.into_iter()
		}
	}

	pub fn nary(childs: Vec<Expr>) -> IntoChilds {
		IntoChilds{
			iter: smallvec::SmallVec::from_vec(childs).into_iter()
		}
	}
}

impl Iterator for IntoChilds {
	type Item = Expr;

	fn next(&mut self) -> Option<Self::Item> {
		self.iter.next()
	}
}
