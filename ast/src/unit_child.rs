use crate::{
	AnyExpr,
	Children,
	ChildrenMut,
	IntoChildren,
	HasArity,
};

/// Utility struct to allow storing child expressions of binary expressions
/// continuously in memory while having a name `lhs` and `rhs` to refer to them
/// for improved usability.
/// 
/// All binary expressions should strive to use this utility to store their
/// child expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct UnaryChild {
    pub inner: AnyExpr,
}

impl UnaryChild {
    /// Creates a new `UnaryChild` for the given child expression.
    #[inline]
    pub fn new(inner: AnyExpr) -> Self {
        UnaryChild{inner}
    }

    /// Creates a new boxed (on heap) `UnaryChild` for the given child expression.
    #[inline]
    pub fn new_boxed(inner: AnyExpr) -> Box<Self> {
        Box::new(UnaryChild::new(inner))
    }

    /// Returns the inner children expression.
    /// 
    /// Note: Consumes `self`.
	#[inline]
    pub fn into_inner(self) -> AnyExpr {
        self.inner
    }
}

impl Children for UnaryChild {
	#[inline]
	fn children_slice(&self) -> &[AnyExpr] {
		let ptr = self as *const UnaryChild as *const AnyExpr;
		unsafe {
			std::slice::from_raw_parts(ptr, 1)
		}
	}
}

impl ChildrenMut for UnaryChild {
	#[inline]
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		let ptr = self as *mut UnaryChild as *mut AnyExpr;
		unsafe {
			std::slice::from_raw_parts_mut(ptr, 1)
		}
	}
}

impl IntoChildren for Box<UnaryChild> {
	#[inline]
	fn into_children_vec(self) -> Vec<AnyExpr> {
		let ptr = Box::into_raw(self) as *mut AnyExpr;
		unsafe {
			Vec::from_raw_parts(ptr, 1, 1)
		}
	}
}

impl HasArity for UnaryChild {
    #[inline]
    fn arity(&self) -> usize {
        1
    }
}
