use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        ZeroExtend
    };
}

/// Zero-extend term expression.
/// 
/// Extends the source child term expression to the given bit width.
/// This extend operation respects the sign of the term expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ZeroExtend {
    /// The source term expression for extension.
    pub src: P<Expr>,
    /// The target bit width.
    /// 
    /// This is also the bit width of this term expression.
    pub width: BitWidth
}

impl ZeroExtend {
    /// Returns a new `ZeroExtend` (zero-extension) term expression for the
    /// given child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If the bit width of the child term expression is greater than
    ///   the target extension bit width.
    pub fn new<E>(target_width: BitWidth, src: E) -> Result<ZeroExtend, String>
        where E: IntoBoxExpr
    {
        let src = src.into_box_expr();
        let src_width = checks::expect_bitvec_ty(&*src)?;
        if target_width < src_width {
            return Err(format!(
                "Encountered zero-extend creation where the target width (={:?}) is smaller than the source width (={:?}).",
                target_width, src_width))
        }
        Ok(ZeroExtend{ width: target_width, src })
    }
}

impl Childs for ZeroExtend {
    fn childs(&self) -> ChildsIter {
        ChildsIter::unary(&self.src)
    }
}

impl ChildsMut for ZeroExtend {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::unary(&mut self.src)
    }
}

impl IntoChilds for ZeroExtend {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::unary(*self.src)
    }
}

impl HasType for ZeroExtend {
    fn ty(&self) -> Type {
        self.width.ty()
    }
}

impl HasKind for ZeroExtend {
    fn kind(&self) -> ExprKind {
        ExprKind::ZeroExtend
    }
}

impl HasArity for ZeroExtend {
    fn arity(&self) -> usize {
        1
    }
}

impl From<ZeroExtend> for Expr {
    fn from(zero_extend: ZeroExtend) -> Expr {
        Expr::ZeroExtend(zero_extend)
    }
}
