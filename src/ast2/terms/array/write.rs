use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        ArrayWrite
    };
}

/// Array write-at-index expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayWrite {
    /// The two child expressions of this array read expression.
    pub childs: P<ArrayWriteChilds>,
    /// The type of this array expr.
    /// 
    /// This mainly stores the index bit width and value bit width.
    pub widths: ArrayTy
}

/// The child expressions of a `Read` expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayWriteChilds {
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
    pub value: AnyExpr
}

impl ArrayWriteChilds {
    /// Creates a new `ArrayWriteChilds` object.
    /// 
    /// Does not check any invariants of `ArrayWrite`.
    /// This function should be marked unsafe since it fails to hold any guarantees.
    pub fn new(array: AnyExpr, index: AnyExpr, value: AnyExpr) -> ArrayWriteChilds {
        ArrayWriteChilds{array, index, value}
    }

    /// Creates a new boxed `ArrayWriteChilds` object.
    /// 
    /// This is just a convenience wrapper around `ArrayWriteChilds::new`.
    pub fn new_boxed(array: AnyExpr, index: AnyExpr, value: AnyExpr) -> P<ArrayWriteChilds> {
        P::new(ArrayWriteChilds::new(array, index, value))
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
    pub fn new(array: AnyExpr, index: AnyExpr, value: AnyExpr) -> Result<ArrayWrite, String> {
        let array_ty = checks::expect_array_ty(&array)?;
        checks::expect_bitvec_ty_and_width(&index, array_ty.index_width())?;
        checks::expect_bitvec_ty_and_width(&value, array_ty.value_width())?;
        Ok(ArrayWrite{
            widths: array_ty,
            childs: ArrayWriteChilds::new_boxed(array, index, value)
        })
    }
}

impl Childs for ArrayWriteChilds {
    fn childs(&self) -> ChildsIter {
        ChildsIter::ternary(&self.array, &self.index, &self.value)
    }
}

impl ChildsMut for ArrayWriteChilds {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::ternary(&mut self.array, &mut self.index, &mut self.value)
    }
}

impl IntoChilds for ArrayWriteChilds {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::ternary(self.array, self.index, self.value)
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

impl Childs for ArrayWrite {
    fn childs(&self) -> ChildsIter {
        self.childs.childs()
    }
}

impl ChildsMut for ArrayWrite {
    fn childs_mut(&mut self) -> ChildsIterMut {
        self.childs.childs_mut()
    }
}

impl IntoChilds for ArrayWrite {
    fn into_childs(self) -> IntoChildsIter {
        self.childs.into_childs()
    }
}
