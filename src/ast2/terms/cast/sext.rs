use ast2::prelude::*;
use ast2::terms::checks;

pub mod prelude {
    pub use super::{
        SignExtend
    };
}

/// Sign-extend term expression.
/// 
/// Extends the source child term expression to the given bit width.
/// This extend operation respects the sign of the term expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SignExtend {
    /// The source term expression for extension.
    pub src: P<AnyExpr>,
    /// The target bit width.
    /// 
    /// This is also the bit width of this term expression.
    pub width: BitWidth
}

impl SignExtend {
    /// Returns a new `SignExtend` (sign-extension) term expression for the
    /// given child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If the bit width of the child term expression is greater than
    ///   the target extension bit width.
    pub fn new<E>(target_width: BitWidth, src: E) -> Result<SignExtend, String>
        where E: IntoBoxedAnyExpr
    {
        let src = src.into_boxed_any_expr();
        let src_width = checks::expect_bitvec_ty(&*src)?;
        if target_width < src_width {
            return Err(format!(
                "Encountered sign-extend creation where the target width (={:?}) is smaller than the source width (={:?}).",
                target_width, src_width))
        }
        Ok(SignExtend{ width: target_width, src })
    }
}

impl Childs for SignExtend {
    fn childs(&self) -> ChildsIter {
        ChildsIter::unary(&self.src)
    }
}

impl ChildsMut for SignExtend {
    fn childs_mut(&mut self) -> ChildsIterMut {
        ChildsIterMut::unary(&mut self.src)
    }
}

impl IntoChilds for SignExtend {
    fn into_childs(self) -> IntoChildsIter {
        IntoChildsIter::unary(*self.src)
    }
}

impl HasType for SignExtend {
    fn ty(&self) -> Type {
        self.width.ty()
    }
}

impl HasKind for SignExtend {
    fn kind(&self) -> ExprKind {
        ExprKind::SignExtend
    }
}

impl HasArity for SignExtend {
    fn arity(&self) -> usize {
        1
    }
}

impl From<SignExtend> for AnyExpr {
    fn from(sign_extend: SignExtend) -> AnyExpr {
        AnyExpr::SignExtend(sign_extend)
    }
}
