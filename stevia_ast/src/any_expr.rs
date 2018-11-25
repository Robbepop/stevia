use crate::prelude::*;

/// Utility trait to transform `AnyExpr` or `Box<AnyExpr>` into `Box<AnyExpr>` and
/// without unboxing the input in the `Box<AnyExpr>` case.
pub trait IntoBoxedAnyExpr {
    /// Puts `self` into a `Box` if it isn't already boxed.
    fn into_boxed_any_expr(self) -> Box<AnyExpr>;
}

impl IntoBoxedAnyExpr for Box<AnyExpr> {
    /// Simply forwards the boxed `T`.
    /// 
    /// This is the "cheap" static case.
    fn into_boxed_any_expr(self) -> Box<AnyExpr> {
        self
    }
}

impl<T> IntoBoxedAnyExpr for T
    where T: Into<AnyExpr>
{
    /// Converts `T` into the respective `AnyExpr` and puts it into a box.
    /// 
    /// This is the "expensive" static case.
    fn into_boxed_any_expr(self) -> Box<AnyExpr> {
        Box::new(self.into())
    }
}

impl AnyExpr {
    /// Returns `true` if the given boolean expression is a constant boolean
    /// expression with the given boolean value, returns `false` otherwise.
    pub fn is_bool_const(&self, req_value: bool) -> bool {
        match *self {
            AnyExpr::BoolConst(ref bool_const) => bool_const.val == req_value,
            _ => false
        }
    }

    /// Checks if `self` is a constant boolean expression and returns its
    /// value if it is and nothing otherwise.
    pub fn get_if_bool_const(&self) -> Option<bool> {
        match *self {
            AnyExpr::BoolConst(ref bool_const) => Some(bool_const.val),
            _ => None
        }
    }

    /// Checks if `self` is a constant bitvector expression and returns its
    /// value if it is and nothing otherwise.
    pub fn get_if_bitvec_const(&self) -> Option<&Bitvec> {
        match *self {
            AnyExpr::BitvecConst(ref bitvec_const) => Some(&bitvec_const.val),
            _ => None
        }
    }
}

macro_rules! forall_expr_kinds {
	( $mac:ident ) => {
		$mac!{
            IfThenElse,
            Symbol,

            BoolConst,
            BoolEquals,
            Not,
            And,
            Or,
            Implies,
            Xor,

            BitvecConst,
            BitvecEquals,
            Neg,
            Add,
            Mul,
            Sub,
            UnsignedDiv,
            SignedDiv,
            SignedModulo,
            UnsignedRemainder,
            SignedRemainder,

            BitNot,
            BitAnd,
            BitOr,
            BitXor,

            SignedGreaterEquals,
            SignedGreaterThan,
            SignedLessEquals,
            SignedLessThan,
            UnsignedGreaterEquals,
            UnsignedGreaterThan,
            UnsignedLessEquals,
            UnsignedLessThan,

            ShiftLeft,
            LogicalShiftRight,
            ArithmeticShiftRight,

            Concat,
            Extract,
            SignExtend,
            ZeroExtend,

            ArrayRead,
            ArrayWrite
        }
    }
}

macro_rules! impl_expr_kinds {
	( $($names:ident),* ) => {
        /// Any expression.
        /// 
        /// There are different kinds of expressions and `AnyExpr`
        /// represents any one of them.
		#[derive(Debug, Clone, PartialEq, Eq, Hash)]
		pub enum AnyExpr {
			$($names(expr::$names)),*
		}

        impl HasType for AnyExpr {
            fn ty(&self) -> Type {
				match self {
					$(AnyExpr::$names(expr) => expr.ty()),*
                }
            }
        }

        impl HasArity for AnyExpr {
            fn arity(&self) -> usize {
				match self {
					$(AnyExpr::$names(expr) => expr.arity()),*
                }
            }
        }

        impl HasKind for AnyExpr {
            fn kind(&self) -> ExprKind {
				match self {
					$(AnyExpr::$names(expr) => expr.kind()),*
                }
            }
        }

        impl Children for AnyExpr {
			fn children_slice(&self) -> &[AnyExpr] {
				match self {
					$(AnyExpr::$names(expr) => expr.children_slice()),*
				}
			}
        }

        impl ChildrenMut for AnyExpr {
			fn children_slice_mut(&mut self) -> &mut [AnyExpr] {
				match self {
					$(AnyExpr::$names(expr) => expr.children_slice_mut()),*
				}
			}
        }

        impl IntoChildren for AnyExpr {
            fn into_children_vec(self) -> Vec<AnyExpr> {
				match self {
					$(AnyExpr::$names(expr) => expr.into_children_vec()),*
                }
            }
        }

        impl AssertConsistency for AnyExpr {
            fn assert_consistency(&self, ctx: &Context) -> ExprResult<()> {
                match self {
                    $(AnyExpr::$names(expr) => expr.assert_consistency(ctx)),*
                }
            }
        }
    }
}

forall_expr_kinds!(impl_expr_kinds);
