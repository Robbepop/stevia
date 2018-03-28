use ast::prelude::*;

pub mod prelude {
    pub use super::{
        Neg
    };
}

/// The arithmetic negation term expression.
/// 
/// This negate the inner term expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Neg {
    /// The inner child formula expression.
    pub child: P<AnyExpr>,
    /// The bit width of this term expression.
    pub bitvec_ty: BitvecTy
}

impl Neg {
    /// Creates a new `Neg` term expression for the given child expression.
    /// 
    /// # Errors
    /// 
    /// - If the given child expression is not of bitvec type with the
    ///   proper given bit width specified.
    pub fn new_with_type<E>(bitvec_ty: BitvecTy, child: E) -> Result<Neg, String>
        where E: IntoBoxedAnyExpr
    {
        let child = child.into_boxed_any_expr();
        expect_concrete_bitvec_ty(&*child, bitvec_ty)?;
        Ok(Neg{bitvec_ty, child})
    }

    /// Creates a new `Neg` term expression for the given child expression.
    /// 
    /// # Note
    /// 
    /// Infers the bitvector type for this expression from its child expression.
    /// 
    /// # Errors
    /// 
    /// - If the given child expression is not of bitvec type.
    pub fn new<E>(child: E) -> Result<Neg, String>
        where E: IntoBoxedAnyExpr
    {
        let child = child.into_boxed_any_expr();
        let bitvec_ty = expect_bitvec_ty(&*child)?;
        Ok(Neg{bitvec_ty, child})
    }
}

impl Children for Neg {
    fn children(&self) -> ChildrenIter {
        ChildrenIter::unary(&self.child)
    }
}

impl ChildrenMut for Neg {
    fn children_mut(&mut self) -> ChildrenIterMut {
        ChildrenIterMut::unary(&mut self.child)
    }
}

impl IntoChildren for Neg {
    fn into_children(self) -> IntoChildrenIter {
        IntoChildrenIter::unary(*self.child)
    }
}

impl HasType for Neg {
    fn ty(&self) -> Type {
        self.bitvec_ty.ty()
    }
}

impl HasKind for Neg {
    fn kind(&self) -> ExprKind {
        ExprKind::Neg
    }
}

impl HasArity for Neg {
    fn arity(&self) -> usize {
        1
    }
}

impl From<Neg> for AnyExpr {
    fn from(neg: Neg) -> AnyExpr {
        AnyExpr::Neg(neg)
    }
}

impl UnaryExpr for Neg {}

impl SingleChild for Neg {
    fn single_child(&self) -> &AnyExpr {
        &*self.child
    }

    fn single_child_mut(&mut self) -> &mut AnyExpr {
        &mut *self.child
    }

    fn into_single_child(self) -> AnyExpr {
        *self.child
    }

    fn into_boxed_single_child(self) -> Box<AnyExpr> {
        self.child
    }
}
