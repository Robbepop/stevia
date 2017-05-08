
use ast::variants::ExprVariant;
use smallvec;

//=============================================================================
// ITERATOR: Childs
//=============================================================================

pub enum Childs<'parent> {
	Inline{
		data: [Option<&'parent ExprVariant>; 3],
		pos : usize
	},
	Extern{
		iter: ::std::slice::Iter<'parent, ExprVariant>
	}
}

impl<'parent> Childs<'parent> {
	pub fn none() -> Childs<'parent> {
		Childs::Inline{
			data: [None, None, None],
			pos : 0
		}
	}

	pub fn unary(inner: &'parent ExprVariant) -> Childs<'parent> {
		Childs::Inline{
			data: [Some(inner), None, None],
			pos : 0
		}
	}

	pub fn binary(left: &'parent ExprVariant, right: &'parent ExprVariant) -> Childs<'parent> {
		Childs::Inline{
			data: [Some(left), Some(right), None],
			pos : 0
		}
	}

	pub fn ternary(
		fst: &'parent ExprVariant,
		snd: &'parent ExprVariant,
		trd: &'parent ExprVariant) -> Childs<'parent>
	{
		Childs::Inline{
			data: [Some(fst), Some(snd), Some(trd)],
			pos : 0
		}
	}

	pub fn nary(childs: &'parent [ExprVariant]) -> Childs<'parent> {
		Childs::Extern{ iter: childs.iter() }
	}
}

impl<'parent> Iterator for Childs<'parent> {
	type Item = &'parent ExprVariant;

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
		data: [Option<&'parent mut ExprVariant>; 3],
		pos : usize
	},
	Extern{
		iter: ::std::slice::IterMut<'parent, ExprVariant>
	}
}

impl<'parent> ChildsMut<'parent> {
	pub fn none() -> ChildsMut<'parent> {
		ChildsMut::Inline{
			data: [None, None, None],
			pos : 0
		}
	}

	pub fn unary(inner: &'parent mut ExprVariant) -> ChildsMut<'parent> {
		ChildsMut::Inline{
			data: [Some(inner), None, None],
			pos : 0
		}
	}

	pub fn binary(left: &'parent mut ExprVariant, right: &'parent mut ExprVariant) -> ChildsMut<'parent> {
		ChildsMut::Inline{
			data: [Some(left), Some(right), None],
			pos : 0
		}
	}

	pub fn ternary(
		fst: &'parent mut ExprVariant,
		snd: &'parent mut ExprVariant,
		trd: &'parent mut ExprVariant) -> ChildsMut<'parent>
	{
		ChildsMut::Inline{
			data: [Some(fst), Some(snd), Some(trd)],
			pos : 0
		}
	}

	pub fn nary(childs: &'parent mut [ExprVariant]) -> ChildsMut<'parent> {
		ChildsMut::Extern{ iter: childs.iter_mut() }
	}
}

impl<'parent> Iterator for ChildsMut<'parent> {
	type Item = &'parent mut ExprVariant;

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
	iter: smallvec::IntoIter<[ExprVariant; 3]>
}

impl<'parent> IntoChilds {
	pub fn none() -> IntoChilds {
		IntoChilds{
			iter: smallvec::SmallVec::new().into_iter()
		}
	}

	pub fn unary(inner: ExprVariant) -> IntoChilds {
		let mut vec = smallvec::SmallVec::new();
		vec.push(inner);
		IntoChilds{
			iter: vec.into_iter()
		}
	}

	pub fn binary(left: ExprVariant, right: ExprVariant) -> IntoChilds {
		let mut vec = smallvec::SmallVec::new();
		vec.push(left);
		vec.push(right);
		IntoChilds{
			iter: vec.into_iter()
		}
	}

	pub fn ternary(fst: ExprVariant, snd: ExprVariant, trd: ExprVariant) -> IntoChilds {
		let mut vec = smallvec::SmallVec::new();
		vec.push(fst);
		vec.push(snd);
		vec.push(trd);
		IntoChilds{
			iter: vec.into_iter()
		}
	}

	pub fn nary(childs: Vec<ExprVariant>) -> IntoChilds {
		IntoChilds{
			iter: smallvec::SmallVec::from_vec(childs).into_iter()
		}
	}
}

impl Iterator for IntoChilds {
	type Item = ExprVariant;

	fn next(&mut self) -> Option<Self::Item> {
		self.iter.next()
	}
}
