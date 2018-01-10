use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        ArrayRead
    };
}

/// Array read-from-index expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayRead {
    /// The two child expressions of this array read expression.
    pub childs: P<ArrayReadChilds>,
    /// The bit width of this read expression.
    /// 
    /// This is a cache for the value bit width of the child
    /// array expression to prevent the indirection over the
    /// childs structure if this value is used often.
    pub width: BitWidth
}

/// The child expressions of a `Read` expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayReadChilds {
    /// The array expression.
    /// 
    /// This must be of array type.
    pub array: Expr,
    /// The index where the array shall be read.
    /// 
    /// This must be of bitvec type.
    pub index: Expr
}

impl ArrayReadChilds {
    /// Creates a new `ArrayReadChilds` object.
    /// 
    /// Does not check any invariants of `ArrayRead`.
    /// This function should be marked unsafe since it fails to hold any guarantees.
    pub fn new(array: Expr, index: Expr) -> ArrayReadChilds {
        ArrayReadChilds{array, index}
    }

    /// Creates a new boxed `ArrayReadChilds` object.
    /// 
    /// This is just a convenience wrapper around `ArrayReadChilds::new`.
    pub fn new_boxed(array: Expr, index: Expr) -> P<ArrayReadChilds> {
        P::new(ArrayReadChilds::new(array, index))
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
    pub fn new(array: Expr, index: Expr) -> Result<ArrayRead, String> {
        let array_ty = checks::expect_array_ty(&array)?;
        checks::expect_bitvec_ty_and_width(&index, array_ty.index_width())?;
        Ok(ArrayRead{ width: array_ty.value_width(), childs: ArrayReadChilds::new_boxed(array, index) })
    }
}

impl Childs for ArrayReadChilds {
    fn childs(&self) -> ChildsIter {
        ChildsIter::binary(&self.array, &self.index)
    }
}

impl ChildsMut for ArrayReadChilds {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::binary(&mut self.array, &mut self.index)
    }
}

impl IntoChilds for ArrayReadChilds {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::binary(self.array, self.index)
    }
}

impl HasType for ArrayRead {
    fn ty(&self) -> Type {
        self.width.ty()
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

impl From<ArrayRead> for Expr {
    fn from(array_read: ArrayRead) -> Expr {
        Expr::ArrayRead(array_read)
    }
}

impl Childs for ArrayRead {
    fn childs(&self) -> ChildsIter {
        self.childs.childs()
    }
}

impl ChildsMut for ArrayRead {
    fn childs_mut(&mut self) -> ChildsIterMut {
        self.childs.childs_mut()
    }
}

impl IntoChilds for ArrayRead {
    fn into_childs(self) -> IntoChildsIter {
        self.childs.into_childs()
    }
}
