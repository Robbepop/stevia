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

	pub fn as_children_slice(&self) -> &[AnyExpr] {
		self.as_children_array()
	}

	pub fn as_children_array(&self) -> &[AnyExpr; 2] {
		unsafe {
			std::mem::transmute::<&Self, &[AnyExpr; 2]>(self)
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
    fn children(&self) -> ChildrenIter {
        // ChildrenIter::binary(&self.array, &self.index)
		ChildrenIter::nary(self.as_children_slice())
    }
}

impl ChildrenMut for ArrayReadChildren {
    fn children_mut(&mut self) -> ChildrenIterMut {
        ChildrenIterMut::binary(&mut self.array, &mut self.index)
    }
}

impl IntoChildren for ArrayReadChildren {
    fn into_children(self) -> IntoChildrenIter {
        IntoChildrenIter::binary(self.array, self.index)
    }
}

impl HasType for ArrayRead {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl HasKind for ArrayRead {
    fn kind(&self) -> ExprKind {
        ExprKind::ArrayRead
    }
}

impl HasArity for ArrayRead {
    fn arity(&self) -> usize {
        2
    }
}

impl From<ArrayRead> for AnyExpr {
    fn from(array_read: ArrayRead) -> AnyExpr {
        AnyExpr::ArrayRead(array_read)
    }
}

impl Children for ArrayRead {
    fn children(&self) -> ChildrenIter {
        self.children.children()
    }
}

impl ChildrenMut for ArrayRead {
    fn children_mut(&mut self) -> ChildrenIterMut {
        self.children.children_mut()
    }
}

impl IntoChildren for ArrayRead {
    fn into_children(self) -> IntoChildrenIter {
        self.children.into_children()
    }
}
