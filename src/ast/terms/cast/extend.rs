use ast::prelude::*;
use ast::terms::ExprMarker;

use std::marker::PhantomData;

pub mod prelude {
    pub use super::{
        SignExtend,
        ZeroExtend
    };
}

/// Generic binary extend term expression.
/// 
/// # Note
/// 
/// This generic expression is used as foundation for sign and zero
/// extend expressions since they share a lot of behaviour.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExtendExpr<M> {
    /// The source term expression for extension.
    pub src: P<AnyExpr>,
    /// The target bit width.
    /// 
    /// This is also the bit width of this term expression.
    pub bitvec_ty: BitvecTy,
    /// Marker to differentiate term expressions from each
    /// other using the type system.
    marker: PhantomData<M>
}

impl<M> ExtendExpr<M> {
    /// Returns a new extend term expression for the given child term expressions.
    /// 
    /// # Errors
    /// 
    /// - If the bit width of the child term expression is greater than
    ///   the target extension bit width.
    pub fn new<E>(target_width: BitWidth, src: E) -> Result<Self, String>
        where E: IntoBoxedAnyExpr
    {
        let src = src.into_boxed_any_expr();
        let src_bvty = expect_bitvec_ty(&*src)?;
        if target_width < src_bvty.width() {
            return Err(format!(
                "Encountered target width (={:?}) that is smaller than the source width (={:?}) upon extend expression construction.",
                target_width, src_bvty.width()))
        }
        Ok(Self{ bitvec_ty: BitvecTy::from(target_width), src, marker: PhantomData })
    }
}

impl<M> Children for ExtendExpr<M> {
    fn children(&self) -> ChildrenIter {
        ChildrenIter::unary(&self.src)
    }
}

impl<M> ChildrenMut for ExtendExpr<M> {
    fn children_mut(&mut self) -> ChildrenIterMut {
        ChildrenIterMut::unary(&mut self.src)
    }
}

impl<M> IntoChildren for ExtendExpr<M> {
    fn into_children(self) -> IntoChildrenIter {
        IntoChildrenIter::unary(*self.src)
    }
}

impl<M> HasType for ExtendExpr<M> {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl<M> HasKind for ExtendExpr<M>
    where M: ExprMarker
{
    fn kind(&self) -> ExprKind {
        M::EXPR_KIND
    }
}

impl<M> HasArity for ExtendExpr<M> {
    fn arity(&self) -> usize {
        1
    }
}

mod marker {
    use ast::prelude::*;
    use ast::terms::ExprMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct SignExtendMarker;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct ZeroExtendMarker;

    impl ExprMarker for SignExtendMarker {
        const EXPR_KIND: ExprKind = ExprKind::SignExtend;
    }

    impl ExprMarker for ZeroExtendMarker {
        const EXPR_KIND: ExprKind = ExprKind::ZeroExtend;
    }
}

/// Zero-extend term expression.
/// 
/// Extends the source child term expression to the given bit width.
/// This extend operation respects the sign of the term expression.
pub type ZeroExtend = ExtendExpr<marker::ZeroExtendMarker>;

impl From<ZeroExtend> for AnyExpr {
    fn from(expr: ZeroExtend) -> AnyExpr {
        AnyExpr::ZeroExtend(expr)
    }
}

/// Sign-extend term expression.
/// 
/// Extends the source child term expression to the given bit width.
/// This extend operation respects the sign of the term expression.
pub type SignExtend = ExtendExpr<marker::SignExtendMarker>;

impl From<SignExtend> for AnyExpr {
    fn from(expr: SignExtend) -> AnyExpr {
        AnyExpr::SignExtend(expr)
    }
}
