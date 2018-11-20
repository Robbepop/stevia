use crate::prelude::*;

/// The If-Then-Else expression.
/// 
/// # Note
/// 
/// - This has a `Type` that is dependend on its children.
/// - Its condition is always of boolean type.
/// - Its `then_case` and `else_case` children are asserted
///   to be of same `Type` as their parent `IfThenElse` expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IfThenElse{
    /// The children of this expression.
	pub children: P<IfThenElseChildren>,
    /// The type of this expression.
	pub ty: Type
}

/// The data of an `IfThenElse` expression.
/// 
/// # Detail
/// 
/// This is an implementation detail for the `IfThenElse`
/// expression and required to create an indirection to
/// its child expressions to break infinite dependency.
/// This also has the positive effect of storing all child
/// expressions densely in the memory.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct IfThenElseChildren {
    /// The condition of the parent `IfThenElse` expression.
    /// 
    /// This must always be of boolean type.
	pub cond: AnyExpr,
    /// The then case of the parent `IfThenElse` expression.
    /// 
    /// This must always have the same type as its parent
    /// `IfThenElse` expresssion and thus the sibling
    /// `else_case` expression.
	pub then_case: AnyExpr,
    /// The else case of the parent `IfThenElse` expression.
    /// 
    /// This must always have the same type as its parent
    /// `IfThenElse` expresssion and thus the sibling
    /// `then_case` expression.
	pub else_case: AnyExpr
}

impl IfThenElseChildren {
    /// Consumes `self` and returns both of its children as tuple.
    pub fn into_children_tuple(self) -> (AnyExpr, AnyExpr, AnyExpr) {
        (self.cond, self.then_case, self.else_case)
    }

    /// Returns a tuple of mutable references to the child expressions.
    pub fn as_children_tuple_mut(&mut self) -> (&mut AnyExpr, &mut AnyExpr, &mut AnyExpr) {
        (&mut self.cond, &mut self.then_case, &mut self.else_case)
    }

    /// Swaps then and else case child expressions.
    pub fn swap_then_else(&mut self) {
        ::std::mem::swap(&mut self.then_case, &mut self.else_case)
    }

	pub fn as_children_slice(&self) -> &[AnyExpr] {
		self.as_children_array()
	}

	pub fn as_children_slice_mut(&mut self) -> &mut [AnyExpr] {
		self.as_children_array_mut()
	}

	pub fn as_children_array(&self) -> &[AnyExpr; 3] {
		unsafe {
			std::mem::transmute::<&Self, &[AnyExpr; 3]>(self)
		}
	}

	pub fn as_children_array_mut(&mut self) -> &mut [AnyExpr; 3] {
		unsafe {
			std::mem::transmute::<&mut Self, &mut [AnyExpr; 3]>(self)
		}
	}
}

impl IfThenElse {
    /// Returns a new `IfThenElse` expression from the given condition, then-case and else-case.
    /// 
    /// # Errors
    /// 
    /// - If the given condition is not of boolean type.
    /// - If the given then-case and else-case do not have a common type.
    pub fn new<E1, E2, E3>(cond: E1, then_case: E2, else_case: E3) -> ExprResult<IfThenElse>
        where E1: Into<AnyExpr>,
              E2: Into<AnyExpr>,
              E3: Into<AnyExpr>
    {
        let cond = cond.into();
        let then_case = then_case.into();
        let else_case = else_case.into();
        expect_type(Type::Bool, &cond)
            .map_err(ExprError::from)
            .map_err(|e| e.context_msg(
                "The condition of an if-then-else expression must be of boolean type."
            ))?;
        expect_common_ty(&then_case, &else_case)
            .map_err(ExprError::from)
            .map_err(|e| e.context_msg(
                "The types of the then-case and else-case of an if-then-else expression must be the same."
            ))?;
        Ok(unsafe{IfThenElse::new_unchecked(cond, then_case, else_case)})
    }

    /// Returns a new `IfThenElse` expression from the given condition, then-case and else-case.
    /// 
    /// # Note
    /// 
    /// - The resulting `IfThenElse` has the type of the then-case expression child.
    /// - This function is unsafe since it does not perform some checks to secure invariants.
    ///   Use it if you already asserted the nessecary invariants.
    pub unsafe fn new_unchecked(cond: AnyExpr, then_case: AnyExpr, else_case: AnyExpr) -> IfThenElse {
        debug_assert_eq!(Ok(()), expect_type(Type::Bool, &cond));
        debug_assert!(expect_common_ty(&then_case, &else_case).is_ok());
        IfThenElse{
            ty: then_case.ty(),
            children: P::new(IfThenElseChildren{cond, then_case, else_case})
        }
    }

    /// Swaps then and else case child expressions.
    pub fn swap_then_else(&mut self) {
        self.children.swap_then_else()
    }

    /// Returns a tuple of mutable references to the child expressions.
    pub fn as_children_tuple_mut(&mut self) -> (&mut AnyExpr, &mut AnyExpr, &mut AnyExpr) {
        self.children.as_children_tuple_mut()
    }

    /// Returns the tuple of child expressions.
    /// 
    /// Note: Consumes this if-then-else expression.
    pub fn into_children_tuple(self) -> (AnyExpr, AnyExpr, AnyExpr) {
        self.children.into_children_tuple()
    }
}

impl Children for IfThenElseChildren {
	#[inline]
	fn children_slice(&self) -> &[AnyExpr] {
		self.as_children_slice()
	}
}

impl ChildrenMut for IfThenElseChildren {
	#[inline]
	fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
		self.as_children_slice_mut()
	}
}

impl HasType for IfThenElse {
    fn ty(&self) -> Type {
        self.ty
    }
}

impl HasKind for IfThenElse {
	#[inline]
    fn kind(&self) -> ExprKind {
        ExprKind::IfThenElse
    }
}

impl HasArity for IfThenElse {
	#[inline]
    fn arity(&self) -> usize {
        3
    }
}

impl From<IfThenElse> for AnyExpr {
    fn from(ite: IfThenElse) -> AnyExpr {
        AnyExpr::IfThenElse(ite)
    }
}

impl Children for IfThenElse {
	#[inline]
    fn children_slice(&self) -> &[AnyExpr] {
        self.children.children_slice()
    }
}

impl ChildrenMut for IfThenElse {
	#[inline]
    fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
        self.children.children_slice_mut()
    }
}

impl IntoChildren for IfThenElse {
    fn into_children_vec(self) -> Vec<AnyExpr> {
		let ptr = Box::leak(self.children) as *mut IfThenElseChildren as *mut AnyExpr;
		unsafe {
			Vec::from_raw_parts(ptr, 3, 3)
		}
    }
}
