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

use std::num::NonZeroU32;

/// The priority of an expression kind.
/// 
/// This is used in order to improve normalization of symmetric
/// expression by sorting their child expressions in a static ordering.
/// 
/// The priority of an expression kind decides this ordering.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Priority(NonZeroU32);

/// Expression kinds do need to implement this trait in order
/// to improve expression normalization.
pub trait HasPriority {
    /// Returns the priority of `self`.
    fn priority(&self) -> Priority;
}

mod priorities {
	pub const FORMULA_BASE: u32    = 100;
	pub const ARITHMETIC_BASE: u32 = 200;
	pub const BITWISE_BASE: u32    = 300;
	pub const COMPARISON_BASE: u32 = 400;
	pub const SHIFT_BASE: u32      = 500;
	pub const CAST_BASE: u32       = 600;
	pub const ARRAY_BASE: u32      = 700;
	pub const GENERIC_BASE: u32    = 800;
}

macro_rules! forall_expr_kinds {
	( $mac:ident ) => {
		$mac!{
			/// The if-then-else expression kind
			#.[priority(priorities::GENERIC_BASE + 0)]
			IfThenElse,
			/// The symbol expression kind
			#.[priority(priorities::GENERIC_BASE + 1)]
			Symbol,

			/// The constant boolean expression kind
			#.[priority(priorities::FORMULA_BASE + 0)]
			BoolConst,
			/// The boolean equality (also known as if-and-only-if) expression kind
			#.[priority(priorities::FORMULA_BASE + 1)]
			BoolEquals,
			/// The not boolean expression kind
			#.[priority(priorities::FORMULA_BASE + 2)]
			Not,
			/// The and boolean expression kind
			#.[priority(priorities::FORMULA_BASE + 3)]
			And,
			/// The or boolean expression kind
			#.[priority(priorities::FORMULA_BASE + 4)]
			Or,
			/// The implies boolean expression kind
			#.[priority(priorities::FORMULA_BASE + 5)]
			Implies,
			/// The xor (either-or) expression kind
			#.[priority(priorities::FORMULA_BASE + 6)]
			Xor,

			/// The constant bitvec term expression kind
			#.[priority(priorities::ARITHMETIC_BASE + 0)]
			BitvecConst,
			// /// The bitvec equality term expression kind
			#.[priority(priorities::ARITHMETIC_BASE + 1)]
			BitvecEquals,
			/// The bitvec negation term expression kind
			#.[priority(priorities::ARITHMETIC_BASE + 2)]
			Neg,
			/// The bitvec add term expression kind
			#.[priority(priorities::ARITHMETIC_BASE + 3)]
			Add,
			/// The bitvec mul term expression kind
			#.[priority(priorities::ARITHMETIC_BASE + 4)]
			Mul,
			/// The bitvec sub term expression kind
			#.[priority(priorities::ARITHMETIC_BASE + 5)]
			Sub,
			/// The bitvec udiv (unsigned division) term expression kind
			#.[priority(priorities::ARITHMETIC_BASE + 6)]
			UnsignedDiv,
			/// The bitvec sdiv (signed division) term expression kind
			#.[priority(priorities::ARITHMETIC_BASE + 7)]
			SignedDiv,
			/// The bitvec smod (signed remainder + sign match) term expression kind
			#.[priority(priorities::ARITHMETIC_BASE + 8)]
			SignedModulo,
			/// The bitvec urem (unsigned remainder) term expression kind
			#.[priority(priorities::ARITHMETIC_BASE + 9)]
			UnsignedRemainder,
			/// The bitvec srem (signed remainder) term expression kind
			#.[priority(priorities::ARITHMETIC_BASE + 10)]
			SignedRemainder,

			/// The bitwise-not term expression kind
			#.[priority(priorities::BITWISE_BASE + 0)]
			BitNot,
			/// The bitwise-and term expression kind
			#.[priority(priorities::BITWISE_BASE + 1)]
			BitAnd,
			/// The bitwise-or term expression kind
			#.[priority(priorities::BITWISE_BASE + 2)]
			BitOr,
			/// The bitwise-xor term expression kind
			#.[priority(priorities::BITWISE_BASE + 3)]
			BitXor,

			/// The signed greater-than-or-equals term expression kind
			#.[priority(priorities::COMPARISON_BASE + 0)]
			SignedGreaterEquals,
			/// The signed greater-than term expression kind
			#.[priority(priorities::COMPARISON_BASE + 1)]
			SignedGreaterThan,
			/// The signed less-than-or-equals term expression kind
			#.[priority(priorities::COMPARISON_BASE + 2)]
			SignedLessEquals,
			/// The signed less-than term expression kind
			#.[priority(priorities::COMPARISON_BASE + 3)]
			SignedLessThan,
			/// The unsigned greater-than-or-equals term expression kind
			#.[priority(priorities::COMPARISON_BASE + 4)]
			UnsignedGreaterEquals,
			/// The unsigned greater-than term expression kind
			#.[priority(priorities::COMPARISON_BASE + 5)]
			UnsignedGreaterThan,
			/// The unsigned less-than-or-equals term expression kind
			#.[priority(priorities::COMPARISON_BASE + 6)]
			UnsignedLessEquals,
			/// The unsigned less-than term expression kind
			#.[priority(priorities::COMPARISON_BASE + 7)]
			UnsignedLessThan,

			/// The shift-left term expression kind
			#.[priority(priorities::SHIFT_BASE + 0)]
			ShiftLeft,
			/// The logical shift-right term expression kind
			#.[priority(priorities::SHIFT_BASE + 1)]
			LogicalShiftRight,
			/// The arithmetic shift-right term expression kind
			#.[priority(priorities::SHIFT_BASE + 2)]
			ArithmeticShiftRight,

			/// The bitvec concatenate term expression kind
			#.[priority(priorities::CAST_BASE + 0)]
			Concat,
			/// The bitvec extraction term expression kind
			#.[priority(priorities::CAST_BASE + 1)]
			Extract,
			/// The bitvec sign-extension term expression kind
			#.[priority(priorities::CAST_BASE + 2)]
			SignExtend,
			/// The bitvec zero-extension term expression kind
			#.[priority(priorities::CAST_BASE + 3)]
			ZeroExtend,

			/// The array-read expression kind
			#.[priority(priorities::ARRAY_BASE + 0)]
			ArrayRead,
			/// The array-write expression kind
			#.[priority(priorities::ARRAY_BASE + 1)]
			ArrayWrite,
        }
    }
}

/// This trait should be implemented by all expressions and structures that
/// represent an expression kind.
/// 
/// This is obviously true for `ExprKind` itself but also for all concrete expression types.
pub trait HasKind {
    /// Returns the kind of `self`.
    fn kind(&self) -> ExprKind;
}

macro_rules! impl_expr_kinds {
	( $( $(#[$attr:meta])* #.[priority($prio:expr)] $names:ident,)* ) => {
        /// Any expression.
        /// 
        /// There are different kinds of expressions and `AnyExpr`
        /// represents any one of them.
		#[derive(Debug, Clone, PartialEq, Eq, Hash)]
		pub enum AnyExpr {
			$(
				$(#[$attr])*
				$names(crate::expr::$names)
			),*
		}

		/// The kind of an expression.
		#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
		pub enum ExprKind {
			$(
				$(#[$attr])*
				$names
			),*
		}

		impl HasKind for ExprKind {
			fn kind(&self) -> ExprKind {
				*self
			}
		}

		impl ExprKind {
			/// Returns the camel-case name of the expression kind.
			pub fn camel_name(self) -> &'static str {
				match self {
					$(
						ExprKind::$names => stringify!($names)
					),*
				}
			}
		}

		impl HasPriority for ExprKind {
			fn priority(&self) -> Priority {
				match *self {
					$(
						ExprKind::$names => Priority(
							unsafe {
								NonZeroU32::new_unchecked($prio)
							}
						)
					),*
				}
			}
		}

		$(
			impl From<crate::expr::$names> for AnyExpr {
				fn from(expr: crate::expr::$names) -> Self {
					AnyExpr::$names(expr)
				}
			}
		)*

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
