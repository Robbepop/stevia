use ast::prelude::*;

pub mod prelude {
    pub use super::{
        BinExprChilds
    };
}

/// Utility struct to allow storing child expressions of binary expressions
/// continuously in memory while having a name `lhs` and `rhs` to refer to them
/// for improved usability.
/// 
/// All binary expressions should strive to use this utility to store their
/// child expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BinExprChilds {
    pub lhs: AnyExpr,
    pub rhs: AnyExpr
}

impl BinExprChilds {
    /// Creates a new `BinExprChilds` for the given child expressions.
    #[inline]
    pub fn new(lhs: AnyExpr, rhs: AnyExpr) -> BinExprChilds {
        BinExprChilds{lhs, rhs}
    }

    /// Creates a new boxed (on heap) `BinExprChilds` for the given child expressions.
    #[inline]
    pub fn new_boxed(lhs: AnyExpr, rhs: AnyExpr) -> P<BinExprChilds> {
        P::new(BinExprChilds::new(lhs, rhs))
    }

    /// Swaps its left-hand side child with the right-hand side child.
    pub fn swap_childs(&mut self) {
        use std::mem;
        mem::swap(&mut self.lhs, &mut self.rhs)
    }
}

impl Childs for BinExprChilds {
    /// Returns an immutable iterator over the two child expressions.
    #[inline]
    fn childs(&self) -> ChildsIter {
        ChildsIter::binary(&self.lhs, &self.rhs)
    }
}

impl ChildsMut for BinExprChilds {
    /// Returns an mutable iterator over the two child expressions.
    #[inline]
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::binary(&mut self.lhs, &mut self.rhs)
    }
}

impl IntoChilds for BinExprChilds {
    /// Consumes this `BinExprChilds` and returns an iterator over its two child expressions.
    /// 
    /// This may be used to transfer ownership of its child expressions.
    #[inline]
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::binary(self.lhs, self.rhs)
    }
}

impl HasArity for BinExprChilds {
    #[inline]
    fn arity(&self) -> usize {
        2
    }
}
