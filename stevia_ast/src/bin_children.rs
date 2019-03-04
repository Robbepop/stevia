use crate::prelude::*;

/// Utility struct to allow storing child expressions of binary expressions
/// continuously in memory while having a name `lhs` and `rhs` to refer to them
/// for improved usability.
/// 
/// All binary expressions should strive to use this utility to store their
/// child expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct BinaryChildren {
    pub lhs: AnyExpr,
    pub rhs: AnyExpr
}

impl BinaryChildren {
    /// Creates a new `BinaryChildren` for the given child expressions.
    #[inline]
    pub fn new(lhs: AnyExpr, rhs: AnyExpr) -> Self {
        BinaryChildren{lhs, rhs}
    }

    /// Creates a new boxed (on heap) `BinaryChildren` for the given child expressions.
    #[inline]
    pub fn new_boxed(lhs: AnyExpr, rhs: AnyExpr) -> Box<Self> {
        P::new(BinaryChildren::new(lhs, rhs))
    }

    /// Swaps its left-hand side child with the right-hand side child.
	#[inline]
    pub fn swap_children(&mut self) {
        std::mem::swap(&mut self.lhs, &mut self.rhs)
    }

    /// Returns a pair of both child expressions.
    /// 
    /// Note: Consumes `self`.
	#[inline]
    pub fn into_children_pair(self) -> (AnyExpr, AnyExpr) {
        (self.lhs, self.rhs)
    }

	/// Returns both children as array to immutable references.
	#[inline]
	pub fn as_children_array(&self) -> &[AnyExpr; 2] {
		unsafe {
			std::mem::transmute::<&Self, &[AnyExpr; 2]>(self)
		}
	}

	/// Returns both children as array to mutable references.
	#[inline]
	pub fn as_children_array_mut(&mut self) -> &mut [AnyExpr; 2] {
		unsafe {
			std::mem::transmute::<&mut Self, &mut [AnyExpr; 2]>(self)
		}
	}

	/// Returns both children as vector of expressions.
	#[inline]
	fn into_vec(self: Box<Self>) -> Vec<AnyExpr> {
		let ptr = Box::into_raw(self) as *mut AnyExpr;
		unsafe {
			Vec::from_raw_parts(ptr, 2, 2)
		}
	}
}

impl Children for BinaryChildren {
	#[inline]
	fn children_slice(&self) -> &[AnyExpr] {
		self.as_children_array()
	}
}

impl ChildrenMut for BinaryChildren {
	#[inline]
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		self.as_children_array_mut()
	}
}

impl IntoChildren for Box<BinaryChildren> {
	#[inline]
	fn into_children_vec(self) -> Vec<AnyExpr> {
		self.into_vec()
	}
}

impl HasArity for BinaryChildren {
    #[inline]
    fn arity(&self) -> usize {
        2
    }
}

impl BinaryExpr for BinaryChildren {
    fn lhs_child(&self) -> &AnyExpr {
        &self.lhs
    }
    fn rhs_child(&self) -> &AnyExpr {
        &self.rhs
    }
}
