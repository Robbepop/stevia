use ast::prelude::*;
use ast::terms::checks;
use ast::terms::ExprMarker;

use std::marker::PhantomData;

pub mod prelude {
    pub use super::{
        SignedGreaterEquals,
        SignedGreaterThan,
        SignedLessEquals,
        SignedLessThan,
        UnsignedGreaterEquals,
        UnsignedGreaterThan,
        UnsignedLessEquals,
        UnsignedLessThan
    };
}

/// Generic comparison term expression.
/// 
/// # Note
/// 
/// Used by concrete binary formula expressions as base template.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ComparisonExpr<M> {
    /// The two child term expressions.
    pub childs: P<BinExprChilds>,
    /// The bit width of this expression.
    /// 
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub childs_bitvec_ty: BitvecTy,
    /// Marker to differentiate bool expressions from each
    /// other using the type system.
    marker: PhantomData<M>
}

impl<M> ComparisonExpr<M> {
    /// Returns a new comparison term expression with the given two child expressions.
    /// 
    /// # Errors
    /// 
    /// - If any of the two given child expressions is not of bitvec type or
    ///   has an unmatching bit width to the given bit width.
    pub fn new<E1, E2>(bitvec_ty: BitvecTy, lhs: E1, rhs: E2) -> Result<Self, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        checks::expect_concrete_bitvec_ty(&lhs, bitvec_ty)?;
        checks::expect_concrete_bitvec_ty(&rhs, bitvec_ty)?;
        Ok(Self{ childs_bitvec_ty: bitvec_ty, childs: BinExprChilds::new_boxed(lhs, rhs), marker: PhantomData })
    }

    /// Returns a new comparison expression for the given two child expressions.
    /// 
    /// # Note
    /// 
    /// Infers the concrete bitvector type of the resulting expression from its childs.
    /// 
    /// # Errors
    /// 
    /// - If `lhs` or `rhs` do not share a common bitvec type.
    pub fn new_infer<E1, E2>(lhs: E1, rhs: E2) -> Result<Self, String>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        let common_ty = checks::expect_common_bitvec_ty(&lhs, &rhs)?;
        Ok(Self{ childs_bitvec_ty: common_ty, childs: BinExprChilds::new_boxed(lhs, rhs), marker: PhantomData })
    }

    /// Creates a new comparison expression from the given raw parts.
    /// 
    /// # Safety
    /// 
    /// This is unsafe since it does not check the type requirements for the given child expressions.
    pub unsafe fn new_unchecked(bitvec_ty: BitvecTy, childs: P<BinExprChilds>) -> Self {
        Self{childs_bitvec_ty: bitvec_ty, childs, marker: PhantomData}
    }
}

impl<M> BoolExpr for ComparisonExpr<M>
    where Self: Into<AnyExpr>
{}

impl<M> Childs for ComparisonExpr<M> {
    fn childs(&self) -> ChildsIter {
        self.childs.childs()
    }
}

impl<M> ChildsMut for ComparisonExpr<M> {
    fn childs_mut(&mut self) -> ChildsIterMut {
        self.childs.childs_mut()
    }
}

impl<M> IntoChilds for ComparisonExpr<M> {
    fn into_childs(self) -> IntoChildsIter {
        self.childs.into_childs()
    }
}

impl<M> HasType for ComparisonExpr<M> {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl<M> HasKind for ComparisonExpr<M>
    where M: ExprMarker
{
    fn kind(&self) -> ExprKind {
        M::EXPR_KIND
    }
}

impl<M> HasArity for ComparisonExpr<M> {
    fn arity(&self) -> usize {
        2
    }
}

mod marker {
    use ast::prelude::*;
    use ast::terms::ExprMarker;

    macro_rules! gen_expr_marker {
        ($name:ident, $kind:expr) => {
            #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
            pub struct $name;
            impl ExprMarker for $name {
                const EXPR_KIND: ExprKind = $kind;
            }
        };
    }

    gen_expr_marker!(SignedGreaterEqualsMarker, ExprKind::SignedGreaterEquals);
    gen_expr_marker!(SignedGreaterThanMarker, ExprKind::SignedGreaterThan);
    gen_expr_marker!(SignedLessEqualsMarker, ExprKind::SignedLessEquals);
    gen_expr_marker!(SignedLessThanMarker, ExprKind::SignedLessThan);
    gen_expr_marker!(UnsignedGreaterEqualsMarker, ExprKind::UnsignedGreaterEquals);
    gen_expr_marker!(UnsignedGreaterThanMarker, ExprKind::UnsignedGreaterThan);
    gen_expr_marker!(UnsignedLessEqualsMarker, ExprKind::UnsignedLessEquals);
    gen_expr_marker!(UnsignedLessThanMarker, ExprKind::UnsignedLessThan);
}

/// Binary signed greater-than-or-equals term expression.
///
/// # Note
///
/// Greater equals comparison is different for signed and unsigned parameters.
pub type SignedGreaterEquals = ComparisonExpr<marker::SignedGreaterEqualsMarker>;

/// Binary signed greater-than term expression.
/// 
/// # Note
/// 
/// Greater equals comparison is different for signed and unsigned parameters.
pub type SignedGreaterThan = ComparisonExpr<marker::SignedGreaterThanMarker>;

/// Binary signed less-than-or-equals term expression.
/// 
/// # Note
/// 
/// Less equals comparison is different for signed and unsigned parameters.
pub type SignedLessEquals = ComparisonExpr<marker::SignedLessEqualsMarker>;

/// Binary signed less-than term expression.
/// 
/// # Note
/// 
/// Less equals comparison is different for signed and unsigned parameters.
pub type SignedLessThan = ComparisonExpr<marker::SignedLessThanMarker>;

/// Binary signed greater-than-or-equals term expression.
///
/// # Note
///
/// Greater equals comparison is different for signed and unsigned parameters.
pub type UnsignedGreaterEquals = ComparisonExpr<marker::UnsignedGreaterEqualsMarker>;

/// Binary unsigned greater-than term expression.
/// 
/// # Note
/// 
/// Greater equals comparison is different for signed and unsigned parameters.
pub type UnsignedGreaterThan = ComparisonExpr<marker::UnsignedGreaterThanMarker>;

/// Binary unsigned less-than-or-equals term expression.
/// 
/// # Note
/// 
/// Less equals comparison is different for signed and unsigned parameters.
pub type UnsignedLessEquals = ComparisonExpr<marker::UnsignedLessEqualsMarker>;

/// Binary unsigned less-than term expression.
/// 
/// # Note
/// 
/// Less equals comparison is different for signed and unsigned parameters.
pub type UnsignedLessThan = ComparisonExpr<marker::UnsignedLessThanMarker>;

macro_rules! gen_into_anyexpr_impl {
    ($name:ident) => {
        impl From<$name> for AnyExpr {
            fn from(expr: $name) -> AnyExpr {
                AnyExpr::$name(expr)
            }
        }
    };
}

gen_into_anyexpr_impl!(SignedGreaterEquals);
gen_into_anyexpr_impl!(SignedGreaterThan);
gen_into_anyexpr_impl!(SignedLessEquals);
gen_into_anyexpr_impl!(SignedLessThan);
gen_into_anyexpr_impl!(UnsignedGreaterEquals);
gen_into_anyexpr_impl!(UnsignedGreaterThan);
gen_into_anyexpr_impl!(UnsignedLessEquals);
gen_into_anyexpr_impl!(UnsignedLessThan);
