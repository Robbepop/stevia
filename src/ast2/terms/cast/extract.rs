use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        Extract
    };
}

/// Binary concatenate term expression.
/// 
/// Concatenates the given bitvec term expressions together.
/// The resulting term expression has a width that is equal to
/// the sum of the bit width of both child term expressions.
/// 
/// The extracted bits are [lo, hi) of the source term expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Extract {
    /// The source term expression that is to be extracted.
    pub src: P<Expr>,
    /// The index of the hi bit position where lo < hi.
    pub hi: usize,
    /// The index of the lo bit position where lo < hi.
    pub lo: usize
}

impl Extract {
    /// Returns a new `Extract` term expression for the given source child term expression
    /// in the range of [lo, hi) that are also given as term expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new<E>(src: E, hi: usize, lo: usize) -> Result<Extract, String>
        where E: IntoBoxExpr
    {
        let src = src.into_box_expr();
        if !(lo < hi) {
            return Err(format!("Expected lo (={:?}) < hi (={:?}) for creation of Extract term expression.", lo, hi))
        }
        let src_width = checks::expect_bitvec_ty(&*src)?;
        if BitWidth::from(hi) > src_width {
            return Err(format!(
                "Encountered hi-overflow for new Extract term expression with source bit width of {:?} and hi position of {:?}.",
                src_width, hi))
        }
        Ok(Extract{hi, lo, src})
    }
}

impl Childs for Extract {
    fn childs(&self) -> ChildsIter {
        ChildsIter::unary(&self.src)
    }
}

impl ChildsMut for Extract {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::unary(&mut self.src)
    }
}

impl IntoChilds for Extract {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::unary(*self.src)
    }
}

impl HasType for Extract {
    fn ty(&self) -> Type {
        BitWidth::from(self.hi - self.lo).ty()
    }
}

impl HasKind for Extract {
    fn kind(&self) -> ExprKind {
        ExprKind::Extract
    }
}

impl HasArity for Extract {
    fn arity(&self) -> usize {
        1
    }
}

impl From<Extract> for Expr {
    fn from(extract: Extract) -> Expr {
        Expr::Extract(extract)
    }
}
