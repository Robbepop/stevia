use ast::prelude::*;
use ast::ExprMarker;

use std::marker::PhantomData;

pub mod prelude {
    pub use super::{
        ComparisonExpr,
        SignedGreaterEquals,
        SignedGreaterThan,
        SignedLessEquals,
        SignedLessThan,
        UnsignedGreaterEquals,
        UnsignedGreaterThan,
        UnsignedLessEquals,
        UnsignedLessThan,
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
    pub children: P<BinExprChildren>,
    /// The bit width of this expression.
    ///
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub children_bitvec_ty: BitvecTy,
    /// Marker to differentiate bool expressions from each
    /// other using the type system.
    marker: PhantomData<M>,
}

impl<M> ComparisonExpr<M>
where
    M: ExprMarker,
{
    /// Returns a new comparison expression for the given two child expressions.
    ///
    /// # Note
    ///
    /// Infers the concrete bitvector type of the resulting expression from its children.
    ///
    /// # Errors
    ///
    /// - If `lhs` or `rhs` do not share a common bitvec type.
    pub fn new<E1, E2>(lhs: E1, rhs: E2) -> ExprResult<Self>
    where
        E1: Into<AnyExpr>,
        E2: Into<AnyExpr>,
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        let common_ty = expect_common_bitvec_ty(&lhs, &rhs).map_err(|e| {
            e.context(format!(
                "Expect common type among children of comparison expression of type {}.",
                M::EXPR_KIND.camel_name()
            ))
        })?;
        Ok(Self {
            children_bitvec_ty: common_ty,
            children: BinExprChildren::new_boxed(lhs, rhs),
            marker: PhantomData,
        })
    }

    /// Creates a new comparison expression from the given raw parts.
    ///
    /// # Safety
    ///
    /// This is unsafe since it does not check the type requirements for the given child expressions
    /// thus allowing users of this API to break invariants of this type which could ultimatively
    /// lead to undefined behaviour indirectly in code depending on those invariants.
    pub unsafe fn new_unchecked(bitvec_ty: BitvecTy, children: P<BinExprChildren>) -> Self {
        Self {
            children_bitvec_ty: bitvec_ty,
            children,
            marker: PhantomData,
        }
    }
}

impl<M> BoolExpr for ComparisonExpr<M>
where
    Self: Into<AnyExpr>,
{
}

impl<M> Children for ComparisonExpr<M> {
    fn children(&self) -> ChildrenIter {
        self.children.children()
    }
}

impl<M> ChildrenMut for ComparisonExpr<M> {
    fn children_mut(&mut self) -> ChildrenIterMut {
        self.children.children_mut()
    }
}

impl<M> IntoChildren for ComparisonExpr<M> {
    fn into_children(self) -> IntoChildrenIter {
        self.children.into_children()
    }
}

impl<M> HasType for ComparisonExpr<M> {
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl<M> HasKind for ComparisonExpr<M>
where
    M: ExprMarker,
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

impl<M> BinaryExpr for ComparisonExpr<M> {
    fn lhs_child(&self) -> &AnyExpr {
        self.children.lhs_child()
    }
    fn rhs_child(&self) -> &AnyExpr {
        self.children.rhs_child()
    }
}

mod marker {
    use ast::prelude::*;
    use ast::ExprMarker;

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
