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
