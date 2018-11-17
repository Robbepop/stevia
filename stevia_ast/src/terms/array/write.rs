use crate::prelude::*;

pub mod prelude {
    pub use super::ArrayWrite;
}

/// Array write-at-index expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayWrite {
    /// The two child expressions of this array read expression.
    pub children: P<ArrayWriteChildren>,
    /// The type of this array expr.
    ///
    /// This mainly stores the index bit width and value bit width.
    pub widths: ArrayTy,
}

/// The child expressions of a `Read` expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct ArrayWriteChildren {
    /// The array expression.
    ///
    /// This must be of array type.
    pub array: AnyExpr,
    /// The index where the array shall be read.
    ///
    /// This must be of bitvec type with a bit width
    /// equals to the array's index bit width.
    pub index: AnyExpr,
    /// The value that is written at the position
    /// of the index.
    ///
    /// This must be of bitvec type with a bit width
    /// equal to the array's value bit width.
    pub value: AnyExpr,
}

impl ArrayWriteChildren {
    /// Creates a new `ArrayWriteChildren` object.
    ///
    /// Does not check any invariants of `ArrayWrite`.
    /// This function should be marked unsafe since it fails to hold any guarantees.
    pub fn new(array: AnyExpr, index: AnyExpr, value: AnyExpr) -> ArrayWriteChildren {
        ArrayWriteChildren {
            array,
            index,
            value,
        }
    }

    /// Creates a new boxed `ArrayWriteChildren` object.
    ///
    /// This is just a convenience wrapper around `ArrayWriteChildren::new`.
    pub fn new_boxed(array: AnyExpr, index: AnyExpr, value: AnyExpr) -> P<ArrayWriteChildren> {
        P::new(ArrayWriteChildren::new(array, index, value))
    }

	pub fn as_children_slice(&self) -> &[AnyExpr] {
		self.as_children_array()
	}

	pub fn as_children_array(&self) -> &[AnyExpr; 3] {
		unsafe {
			std::mem::transmute::<&Self, &[AnyExpr; 3]>(self)
		}
	}
}

impl ArrayWrite {
    /// Returns a new `ArrayWrite` expression for the given array expression
    /// and writing the given value at the given term expression index.
    ///
    /// # Errors
    ///
    /// - If the given `array` is not of array type.
    /// - If the given `index` is not of bitvec type and does not match the
    ///   index bit width of the given array.
    /// - If the given `value` is not of bitvec type and does not match the
    ///   value bit width of the given array.
    pub fn new<A, I, V>(array: A, index: I, value: V) -> ExprResult<ArrayWrite>
    where
        A: Into<AnyExpr>,
        I: Into<AnyExpr>,
        V: Into<AnyExpr>,
    {
        let array = array.into();
        let index = index.into();
        let value = value.into();
        let array_ty = expect_array_ty(&array)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(
                    "Expected the array (left hand-side) expression of the ArrayWrite \
                    expression to be of array type.",
                )
            })?;
        expect_type(array_ty.index_ty(), &index)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(
                    "Expected the index (middle) expression of the ArrayRead \
                    expression to be of the same bitvector type as the index-type \
                    of the left hand-side array expression.",
                )
            })?;
        expect_type(array_ty.value_ty(), &value)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(
                    "Expected the value (right hand-side) expression of the ArrayRead \
                    expression to be of the same bitvector type as the value-type \
                    of the left hand-side array expression.",
                )
            })?;
        Ok(ArrayWrite {
            widths: array_ty,
            children: ArrayWriteChildren::new_boxed(array, index, value),
        })
    }
}

impl Children for ArrayWriteChildren {
    fn children(&self) -> ChildrenIter {
		ChildrenIter::nary(self.as_children_slice())
    }
}

impl ChildrenMut for ArrayWriteChildren {
    fn children_mut(&mut self) -> ChildrenIterMut {
        ChildrenIterMut::ternary(&mut self.array, &mut self.index, &mut self.value)
    }
}

impl IntoChildren for ArrayWriteChildren {
    fn into_children(self) -> IntoChildrenIter {
        IntoChildrenIter::ternary(self.array, self.index, self.value)
    }
}

impl HasType for ArrayWrite {
    fn ty(&self) -> Type {
        self.widths.into()
    }
}

impl HasKind for ArrayWrite {
    fn kind(&self) -> ExprKind {
        ExprKind::ArrayWrite
    }
}

impl HasArity for ArrayWrite {
    fn arity(&self) -> usize {
        3
    }
}

impl From<ArrayWrite> for AnyExpr {
    fn from(array_write: ArrayWrite) -> AnyExpr {
        AnyExpr::ArrayWrite(array_write)
    }
}

impl Children for ArrayWrite {
    fn children(&self) -> ChildrenIter {
        self.children.children()
    }
}

impl ChildrenMut for ArrayWrite {
    fn children_mut(&mut self) -> ChildrenIterMut {
        self.children.children_mut()
    }
}

impl IntoChildren for ArrayWrite {
    fn into_children(self) -> IntoChildrenIter {
        self.children.into_children()
    }
}
