use crate::prelude::*;

use std::cmp::Ordering;

/// Re-exports all commonly used items of this module.
pub mod prelude {
    pub use super::BitvecEquals;
}

/// N-ary equality expression for bitvectors.
///
/// Evaluates to `true` if all child bitvec expressions evalute
/// to the same value, else evaluates to `false`.
///
/// # Note
///
/// - All child bitvec expressions must have the same bit width.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitvecEquals {
    /// The child expressions.
    pub children: Vec<AnyExpr>,
    /// The common bit width of all child bitvec expressions.
    pub children_bitvec_ty: BitvecTy,
}

impl BitvecEquals {
    /// Returns a new binary `BitvecEquals` expression for the given two child expressions.
    ///
    /// # Note
    ///
    /// Infers the concrete bitvector type of the resulting expression from its children.
    ///
    /// # Errors
    ///
    /// - If `lhs` or `rhs` do not share a common bitvec type.
    pub fn binary<E1, E2>(lhs: E1, rhs: E2) -> ExprResult<BitvecEquals>
    where
        E1: Into<AnyExpr>,
        E2: Into<AnyExpr>,
    {
        let lhs = lhs.into();
        let rhs = rhs.into();
        let common_ty = expect_common_bitvec_ty(&lhs, &rhs)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(
                    "Expected both child expressions of the binary bitvector \
                    equality expression to be of the same bitvector type.",
                )
            })?;
        Ok(BitvecEquals {
            children_bitvec_ty: common_ty,
            children: vec![lhs, rhs],
        })
    }

    /// Creates a new n-ary `BitvecEquals` expression from the given iterator over expressions.
    ///
    /// This automatically infers the common bitvector type of its given child expressions.
    ///
    /// # Errors
    ///
    /// - If the given iterator yields less than two expressions.
    /// - If not all yielded expressions are of the same bitvec type.
    pub fn nary<E>(exprs: E) -> ExprResult<BitvecEquals>
    where
        E: IntoIterator<Item = AnyExpr>,
    {
        let children = exprs.into_iter().collect::<Vec<_>>();
        if children.len() < 2 {
            return Err(ExprError::too_few_children(2, children.len()).context_msg(
                "Expected at least 2 child expressions for the n-ary \
                 bitvector equality expression.",
            ));
        }
        let children_bitvec_ty = expect_common_bitvec_ty_n(&children)
			.map_err(ExprError::from)
            .map_err(|e| {
                e.context_msg(
                    "Expected all child expressions of the n-ary bitvector \
                    equality expression to be of the same bitvector type.",
                )
            })?;
        let bveq = BitvecEquals {
            children_bitvec_ty: children_bitvec_ty.unwrap(),
            children,
        };
        Ok(bveq)
    }
}

impl HasType for BitvecEquals {
	#[inline]
    fn ty(&self) -> Type {
        Type::Bool
    }
}

impl HasKind for BitvecEquals {
    fn kind(&self) -> ExprKind {
        ExprKind::BitvecEquals
    }
}

impl HasArity for BitvecEquals {
    fn arity(&self) -> usize {
        self.children.len()
    }
}

impl From<BitvecEquals> for AnyExpr {
    fn from(bitvec_equals: BitvecEquals) -> AnyExpr {
        AnyExpr::BitvecEquals(bitvec_equals)
    }
}

impl Children for BitvecEquals {
	#[inline]
	fn children_slice(&self) -> &[AnyExpr] {
		&self.children
	}
}

impl ChildrenMut for BitvecEquals {
	#[inline]
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		&mut self.children
	}
}

impl IntoChildren for BitvecEquals {
    fn into_children_vec(self) -> Vec<AnyExpr> {
        self.children
    }
}

impl DedupChildren for BitvecEquals {
    fn dedup_children(&mut self) {
        self.children.dedup()
    }
}

impl SortChildren for BitvecEquals {
    fn sort_children_by<F>(&mut self, comparator: F)
    where
        F: FnMut(&AnyExpr, &AnyExpr) -> Ordering,
    {
        self.children.sort_unstable_by(comparator)
    }
}

impl RetainChildren for BitvecEquals {
    fn retain_children<P>(&mut self, predicate: P)
    where
        P: FnMut(&AnyExpr) -> bool,
    {
        self.children.retain(predicate);
    }
}
