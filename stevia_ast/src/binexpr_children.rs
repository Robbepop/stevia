use crate::prelude::*;

/// Utility struct to allow storing child expressions of binary expressions
/// continuously in memory while having a name `lhs` and `rhs` to refer to them
/// for improved usability.
/// 
/// All binary expressions should strive to use this utility to store their
/// child expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct BinExprChildren {
    pub lhs: AnyExpr,
    pub rhs: AnyExpr
}

impl BinExprChildren {
    /// Creates a new `BinExprChildren` for the given child expressions.
    #[inline]
    pub fn new(lhs: AnyExpr, rhs: AnyExpr) -> BinExprChildren {
        BinExprChildren{lhs, rhs}
    }

    /// Creates a new boxed (on heap) `BinExprChildren` for the given child expressions.
    #[inline]
    pub fn new_boxed(lhs: AnyExpr, rhs: AnyExpr) -> P<BinExprChildren> {
        P::new(BinExprChildren::new(lhs, rhs))
    }

    /// Swaps its left-hand side child with the right-hand side child.
	#[inline]
    pub fn swap_children(&mut self) {
        use std::mem;
        mem::swap(&mut self.lhs, &mut self.rhs)
    }

    /// Returns a pair of both child expressions.
    /// 
    /// Note: Consumes `self`.
	#[inline]
    pub fn into_children_pair(self) -> (AnyExpr, AnyExpr) {
        (self.lhs, self.rhs)
    }

	#[inline]
	pub fn as_children_slice(&self) -> &[AnyExpr] {
		self.as_children_array()
	}

	#[inline]
	pub fn as_children_slice_mut(&mut self) -> &mut [AnyExpr] {
		self.as_children_array_mut()
	}

	#[inline]
	pub fn as_children_array(&self) -> &[AnyExpr; 2] {
		unsafe {
			std::mem::transmute::<&Self, &[AnyExpr; 2]>(self)
		}
	}

	#[inline]
	pub fn as_children_array_mut(&mut self) -> &mut [AnyExpr; 2] {
		unsafe {
			std::mem::transmute::<&mut Self, &mut [AnyExpr; 2]>(self)
		}
	}
}

impl Children for BinExprChildren {
	#[inline]
	fn children_slice(&self) -> &[AnyExpr] {
		self.as_children_slice()
	}
}

impl ChildrenMut for BinExprChildren {
	#[inline]
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		self.as_children_slice_mut()
	}
}

impl HasArity for BinExprChildren {
    #[inline]
    fn arity(&self) -> usize {
        2
    }
}

impl BinaryExpr for BinExprChildren {
    fn lhs_child(&self) -> &AnyExpr {
        &self.lhs
    }
    fn rhs_child(&self) -> &AnyExpr {
        &self.rhs
    }
}
