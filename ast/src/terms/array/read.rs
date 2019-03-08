use crate::prelude::*;

pub mod prelude {
    pub use super::{ArrayRead, ArrayReadChildren};
}

/// Array read-from-index expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayRead {
    /// The two child expressions of this array read expression.
    pub children: P<ArrayReadChildren>,
    /// The bit width of this read expression.
    ///
    /// This is a cache for the value bit width of the child
    /// array expression to prevent the indirection over the
    /// children structure if this value is used often.
    pub bitvec_ty: BitvecTy,
}

/// The child expressions of a `Read` expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct ArrayReadChildren {
    /// The array expression.
    ///
    /// This must be of array type.
    pub array: AnyExpr,
    /// The index where the array shall be read.
    ///
    /// This must be of bitvec type.
    pub index: AnyExpr,
}

impl ArrayReadChildren {
    /// Creates a new `ArrayReadChildren` object.
    ///
    /// Does not check any invariants of `ArrayRead`.
    /// This function should be marked unsafe since it fails to hold any guarantees.
    pub fn new(array: AnyExpr, index: AnyExpr) -> ArrayReadChildren {
        ArrayReadChildren { array, index }
    }

    /// Creates a new boxed `ArrayReadChildren` object.
    ///
    /// This is just a convenience wrapper around `ArrayReadChildren::new`.
    pub fn new_boxed(array: AnyExpr, index: AnyExpr) -> P<ArrayReadChildren> {
        P::new(ArrayReadChildren::new(array, index))
    }

	/// Returns the children as slice to immutable references.
	///
	/// # Note
	///
	/// The order of the children is the following:
	///
	/// 1. `array`
	/// 1. `array_index`
	pub fn as_children_slice(&self) -> &[AnyExpr] {
		self.as_children_array()
	}

	/// Returns the children as slice to mutable references.
	///
	/// # Note
	///
	/// The order of the children is the following:
	///
	/// 1. `array`
	/// 1. `array_index`
	pub fn as_children_slice_mut(&mut self) -> &mut [AnyExpr] {
		self.as_children_array_mut()
	}

	/// Returns the children as array to immutable references.
	///
	/// # Note
	///
	/// The order of the children is the following:
	///
	/// 1. `array`
	/// 1. `array_index`
	pub fn as_children_array(&self) -> &[AnyExpr; 2] {
		unsafe {
			&*(self as *const ArrayReadChildren as *const [AnyExpr; 2])
		}
	}

	/// Returns the children as array to mutable references.
	///
	/// # Note
	///
	/// The order of the children is the following:
	///
	/// 1. `array`
	/// 1. `array_index`
	pub fn as_children_array_mut(&mut self) -> &mut [AnyExpr; 2] {
		unsafe {
			&mut *(self as *mut ArrayReadChildren as *mut [AnyExpr; 2])
		}
	}
}

impl ArrayRead {
    /// Returns a new `ArrayRead` expression for the given array expression
    /// and reading at the given term expression index.
    ///
    /// # Errors
    ///
    /// - If the given `array` is not of array type.
    /// - If the given `index` is not of bitvec type and does not match the
    ///   index bit width of the given array.
    pub fn new<E1, E2>(array: E1, index: E2) -> ExprResult<ArrayRead>
    where
        E1: Into<AnyExpr>,
        E2: Into<AnyExpr>,
    {
        let array = array.into();
        let index = index.into();
        let array_ty = expect_array_ty(&array)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(
                    "Expected the left hand-side expression of the ArrayRead \
                    expression to be of array type.",
                )
            })?;
        expect_type(array_ty.index_ty(), &index)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(
                    "Expected the right hand-side expression of the ArrayRead \
                    expression to be of the same bitvector type as the index-type \
                    of the left hand-side array expression.",
                )
            })?;
        Ok(ArrayRead {
            bitvec_ty: array_ty.value_ty(),
            children: ArrayReadChildren::new_boxed(array, index),
        })
    }
}

impl Children for ArrayReadChildren {
	#[inline]
	fn children_slice(&self) -> &[AnyExpr] {
		self.as_children_slice()
	}
}

impl ChildrenMut for ArrayReadChildren {
	#[inline]
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		self.as_children_slice_mut()
	}
}

impl HasType for ArrayRead {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl HasKind for ArrayRead {
	#[inline]
    fn kind(&self) -> ExprKind {
        ExprKind::ArrayRead
    }
}

impl HasArity for ArrayRead {
	#[inline]
    fn arity(&self) -> usize {
        2
    }
}

impl Children for ArrayRead {
	#[inline]
	fn children_slice(&self) -> &[AnyExpr] {
		self.children.children_slice()
	}
}

impl ChildrenMut for ArrayRead {
	#[inline]
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		self.children.children_slice_mut()
	}
}

impl IntoChildren for ArrayRead {
    fn into_children_vec(self) -> Vec<AnyExpr> {
		let ptr = Box::leak(self.children) as *mut ArrayReadChildren as *mut AnyExpr;
		unsafe {
			Vec::from_raw_parts(ptr, 2, 2)
		}
    }
}
