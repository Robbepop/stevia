use ast2::prelude::*;
use ast2::terms::prelude::*;
use ast2::terms::checks;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::Add;
}

/// Add term expression for adding a number of bitvector expressions.
///
/// Arithmetically sums up all child term expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Add {
    /// The child bitvector expressions.
    pub childs: Vec<Expr>,
    /// The bit width of this expression.
    ///
    /// All child expressions must respect this bit width.
    /// This is also used to verify integrity of the bit width.
    pub width: BitWidth,
}

impl Add {
    /// Creates a new bitvector Add term expression for all of the child
    /// expressions yielded by the given iterator and with the given bit width.
    ///
    /// # Errors
    ///
    /// - If the given iterator yields less than two child expressions.
    /// - If not all yielded child expressions are of bitvec type with
    ///   the required bit width.
    pub fn new<I>(width: BitWidth, childs: I) -> Result<Add, String>
    where
        I: IntoIterator<Item = Expr>,
    {
        let childs = childs.into_iter().collect::<Vec<_>>();
        if childs.len() < 2 {
            return Err(
                "Requires at least two child expressions to create an Add term expression.".into(),
            );
        }
        if childs
            .iter()
            .any(|c| checks::expect_bitvec_ty_and_width(c, width).is_err())
        {
            return Err(
                "Requires all child expressions to be of bitvec type with the expected bit width."
                    .into(),
            );
        }
        Ok(Add { width, childs })
    }
}

impl_traits_for_nary_term_expr!(Add);
