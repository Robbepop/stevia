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
    pub fn swap_children(&mut self) {
        use std::mem;
        mem::swap(&mut self.lhs, &mut self.rhs)
    }

    /// Returns a pair of both child expressions.
    /// 
    /// Note: Consumes `self`.
    pub fn into_children_pair(self) -> (AnyExpr, AnyExpr) {
        (self.lhs, self.rhs)
    }

	pub fn as_children_slice(&self) -> &[AnyExpr] {
		self.as_children_array()
	}

	pub fn as_children_array(&self) -> &[AnyExpr; 2] {
		unsafe {
			std::mem::transmute::<&Self, &[AnyExpr; 2]>(self)
		}
	}
}

impl Children for BinExprChildren {
    /// Returns an immutable iterator over the two child expressions.
    #[inline]
    fn children(&self) -> ChildrenIter {
        // ChildrenIter::binary(&self.lhs, &self.rhs)
		ChildrenIter::nary(self.as_children_slice())
    }
}

impl ChildrenMut for BinExprChildren {
    /// Returns an mutable iterator over the two child expressions.
    #[inline]
    fn children_mut(&mut self) -> ChildrenIterMut {
        ChildrenIterMut::binary(&mut self.lhs, &mut self.rhs)
    }
}

impl IntoChildren for BinExprChildren {
    /// Consumes this `BinExprChildren` and returns an iterator over its two child expressions.
    /// 
    /// This may be used to transfer ownership of its child expressions.
    #[inline]
    fn into_children(self) -> IntoChildrenIter {
        IntoChildrenIter::binary(self.lhs, self.rhs)
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
