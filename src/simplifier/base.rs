use ast2::prelude::*;

use std::mem;
use std::ops::BitOrAssign;

pub mod prelude {
    pub use super::{
        Transformer,
        TransformResult,
        AnyTransformer,
        AnyExprAndTransformResult,
        AutoImplAnyTransformer
    };
}

/// Describes whether the result of a transformation actually transformed
/// the input or did nothing to it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TransformResult {
    /// States that the transformation had no effect on the input.
    Identity,
    /// States that the transformation transformed the input.
    Transformed
}

impl BitOrAssign for TransformResult {
    /// Assigns this `TransformResult` to `rhs`.
    /// 
    /// This works equivalent to boolean or-assign
    /// where `Identity` is equal to `false` and
    /// `Transformed` is equal to `true`.
    fn bitor_assign(&mut self, rhs: TransformResult) {
        match rhs {
            TransformResult::Transformed => *self = rhs,
            TransformResult::Identity    => ()
        }
    }
}

/// Simple struct to store a transformed expression
/// and a state indicating if it was actually transformed.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AnyExprAndTransformResult {
    /// States if `expr` actually got transformed.
    pub result: TransformResult,
    /// The (probably) transformed expression.
    pub expr: AnyExpr
}

impl AnyExprAndTransformResult {
    /// Creates a new `AnyExprAndTransformResult` with the given expression and state.
    pub fn new(result: TransformResult, expr: AnyExpr) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult{expr, result}
    }

    /// Creates a new non-transformed `AnyExprAndTransformResult` for the given expression.
    pub fn identity<E>(expr: E) -> AnyExprAndTransformResult
        where E: Into<AnyExpr>
    {
        AnyExprAndTransformResult::new(TransformResult::Identity, expr.into())
    }

    /// Creates a new transformed `AnyExprAndTransformResult` for the given expression.
    pub fn transformed<E>(expr: E) -> AnyExprAndTransformResult
        where E: Into<AnyExpr>
    {
        AnyExprAndTransformResult::new(TransformResult::Transformed, expr.into())
    }
}

pub trait Transformer: Copy {
    fn transform_cond(self, cond: expr::IfThenElse) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(cond)
    }

    fn transform_var(self, bool_const: expr::Symbol) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(bool_const)
    }

    fn transform_bool_const(self, bool_const: expr::BoolConst) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(bool_const)
    }

    fn transform_bool_equals(self, bool_equals: expr::BoolEquals) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(bool_equals)
    }

    fn transform_and(self, and: expr::And) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(and)
    }

    fn transform_or(self, or: expr::Or) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(or)
    }

    fn transform_not(self, not: expr::Not) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(not)
    }

    fn transform_xor(self, xor: expr::Xor) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(xor)
    }

    fn transform_implies(self, implies: expr::Implies) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(implies)
    }

    fn transform_array_equals(self, array_equals: expr::ArrayEquals) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(array_equals)
    }

    fn transform_array_read(self, array_read: expr::ArrayRead) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(array_read)
    }

    fn transform_array_write(self, array_write: expr::ArrayWrite) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(array_write)
    }

    fn transform_bitvec_const(self, bitvec_const: expr::BitvecConst) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(bitvec_const)
    }

    fn transform_add(self, add: expr::Add) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(add)
    }

    fn transform_mul(self, mul: expr::Mul) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(mul)
    }

    fn transform_neg(self, neg: expr::Neg) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(neg)
    }

    fn transform_sdiv(self, sdiv: expr::SignedDiv) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(sdiv)
    }

    fn transform_smod(self, smod: expr::SignedModulo) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(smod)
    }

    fn transform_srem(self, srem: expr::SignedRemainder) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(srem)
    }

    fn transform_sub(self, sub: expr::Sub) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(sub)
    }

    fn transform_udiv(self, udiv: expr::UnsignedDiv) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(udiv)
    }

    fn transform_urem(self, urem: expr::UnsignedRemainder) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(urem)
    }

    fn transform_bitand(self, bitand: expr::BitAnd) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(bitand)
    }

    fn transform_bitnot(self, bitnot: expr::BitNot) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(bitnot)
    }

    fn transform_bitor(self, bitor: expr::BitOr) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(bitor)
    }

    fn transform_bitxor(self, bitxor: expr::BitXor) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(bitxor)
    }

    fn transform_concat(self, concat: expr::Concat) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(concat)
    }

    fn transform_extract(self, extract: expr::Extract) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(extract)
    }

    fn transform_sext(self, sext: expr::SignExtend) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(sext)
    }

    fn transform_zext(self, zext: expr::ZeroExtend) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(zext)
    }

    fn transform_bitvec_equals(self, bitvec_equals: expr::BitvecEquals) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(bitvec_equals)
    }

    fn transform_sge(self, sge: expr::SignedGreaterEquals) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(sge)
    }

    fn transform_sgt(self, sgt: expr::SignedGreaterThan) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(sgt)
    }

    fn transform_sle(self, sle: expr::SignedLessEquals) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(sle)
    }

    fn transform_slt(self, slt: expr::SignedLessThan) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(slt)
    }

    fn transform_uge(self, uge: expr::UnsignedGreaterEquals) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(uge)
    }

    fn transform_ugt(self, ugt: expr::UnsignedGreaterThan) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(ugt)
    }

    fn transform_ule(self, ule: expr::UnsignedLessEquals) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(ule)
    }

    fn transform_ult(self, ult: expr::UnsignedLessThan) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(ult)
    }

    fn transform_ashr(self, ashr: expr::ArithmeticShiftRight) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(ashr)
    }

    fn transform_lshr(self, lshr: expr::LogicalShiftRight) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(lshr)
    }

    fn transform_shl(self, shl: expr::ShiftLeft) -> AnyExprAndTransformResult {
        AnyExprAndTransformResult::identity(shl)
    }
}

/// Simple transformer that does nothing.
/// 
/// This is useful for testing as long as there are no other
/// real transformers to test the system.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct NoopTransformer;
impl Transformer for NoopTransformer {}
impl AutoImplAnyTransformer for NoopTransformer {}
impl Default for NoopTransformer {
    fn default() -> Self {
        NoopTransformer
    }
}

/// Expression transformers that may transform `AnyExpr` instances.
pub trait AnyTransformer: Copy {
    /// Transforms the given mutable `AnyExpr` inplace.
    /// 
    /// Returns a state indicating whether the given expression was actually transformed.
    fn transform_any_expr(self, expr: &mut AnyExpr) -> TransformResult;

    /// Consumed the given `AnyExpr` and transforms it.
    /// 
    /// Returns the resulting expression after the transformation and a state
    /// indicating whether the consumed expression was actually transformed.
    fn into_transform_any_expr(self, expr: AnyExpr) -> AnyExprAndTransformResult;
}

/// Implement this to activate automatic default implementation
/// of the `AnyTransformer` trait.
pub trait AutoImplAnyTransformer {}

impl<T> AnyTransformer for T where T: Transformer + AutoImplAnyTransformer {
    fn transform_any_expr(self, expr: &mut AnyExpr) -> TransformResult {
        let temp = AnyExpr::from(expr::BoolConst::f());
		let input = mem::replace(expr, temp);
		let AnyExprAndTransformResult{result, expr: transformed} =
            self.into_transform_any_expr(input);
        mem::replace(expr, transformed);
        result
    }

    fn into_transform_any_expr(self, expr: AnyExpr) -> AnyExprAndTransformResult {
        use self::AnyExpr::*;
        match expr {
            IfThenElse(expr) => self.transform_cond(expr),
            Symbol(expr) => self.transform_var(expr),
            BoolConst(expr) => self.transform_bool_const(expr),
            BoolEquals(expr) => self.transform_bool_equals(expr),
            Not(expr) => self.transform_not(expr),
            And(expr) => self.transform_and(expr),
            Or(expr) => self.transform_or(expr),

            Xor(expr) => self.transform_xor(expr),
            Implies(expr) => self.transform_implies(expr),
            ArrayEquals(expr) => self.transform_array_equals(expr),
            ArrayRead(expr) => self.transform_array_read(expr),
            ArrayWrite(expr) => self.transform_array_write(expr),
            Add(expr) => self.transform_add(expr),
            BitvecConst(expr) => self.transform_bitvec_const(expr),
            Mul(expr) => self.transform_mul(expr),
            Neg(expr) => self.transform_neg(expr),
            SignedDiv(expr) => self.transform_sdiv(expr),
            SignedModulo(expr) => self.transform_smod(expr),
            SignedRemainder(expr) => self.transform_srem(expr),
            Sub(expr) => self.transform_sub(expr),
            UnsignedDiv(expr) => self.transform_udiv(expr),
            UnsignedRemainder(expr) => self.transform_urem(expr),
            BitAnd(expr) => self.transform_bitand(expr),
            BitNot(expr) => self.transform_bitnot(expr),
            BitOr(expr) => self.transform_bitor(expr),
            BitXor(expr) => self.transform_bitxor(expr),
            Concat(expr) => self.transform_concat(expr),
            Extract(expr) => self.transform_extract(expr),
            SignExtend(expr) => self.transform_sext(expr),
            ZeroExtend(expr) => self.transform_zext(expr),
            BitvecEquals(expr) => self.transform_bitvec_equals(expr),
            SignedGreaterEquals(expr) => self.transform_sge(expr),
            SignedGreaterThan(expr) => self.transform_sgt(expr),
            SignedLessEquals(expr) => self.transform_sle(expr),
            SignedLessThan(expr) => self.transform_slt(expr),
            UnsignedGreaterEquals(expr) => self.transform_uge(expr),
            UnsignedGreaterThan(expr) => self.transform_ugt(expr),
            UnsignedLessEquals(expr) => self.transform_ule(expr),
            UnsignedLessThan(expr) => self.transform_ult(expr),
            ArithmeticShiftRight(expr) => self.transform_ashr(expr),
            LogicalShiftRight(expr) => self.transform_lshr(expr),
            ShiftLeft(expr) => self.transform_shl(expr)
        }
    }
}

#[macro_export]
macro_rules! create_base_transformer {
    (struct $name:ident; $(($id:ident, $trans:ty)),+) => {
        /// The base transformer including a collection of sub-transformers.
        /// 
        /// This traverses the expression tree and performs transformations
        /// using all given transformers.
        #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
        pub struct $name {
            $($id: $trans),*
        }

        impl $name {
            pub fn new($($id: $trans),*) -> Self {
                $name{
                    $($id),*
                }
            }

            fn forward_transform_any_expr(self, expr: &mut AnyExpr) -> TransformResult {
                let mut result = TransformResult::Identity;
                $(result |= self.$id.transform_any_expr(expr));*;
                result
            }

            pub fn traverse_transform_any_expr(self, expr: &mut AnyExpr) -> TransformResult {
                let mut result = TransformResult::Identity;
                for child in expr.childs_mut() {
                    result |= self.traverse_transform_any_expr(child);
                }
                result |= self.forward_transform_any_expr(expr);
                result
            }
        }

        impl AnyTransformer for $name {
            fn transform_any_expr(self, expr: &mut AnyExpr) -> TransformResult {
                self.traverse_transform_any_expr(expr)
            }

            fn into_transform_any_expr(self, expr: AnyExpr) -> AnyExprAndTransformResult {
                let mut expr = expr;
                let result = self.transform_any_expr(&mut expr);
                AnyExprAndTransformResult::new(result, expr)
            }
        }
    }
}
