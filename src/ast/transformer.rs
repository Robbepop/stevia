use ast::prelude::*;

use std::mem;
use std::ops::BitOrAssign;

pub mod prelude {
    pub use super::{
        TransformEffect,
        TransformOutcome,
        Transformer,
        AnyExprTransformer,
        AutoImplAnyExprTransformer,
        TraverseTransformer
    };
}

/// Describes whether the result of a transformation actually transformed
/// the input or did nothing to it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TransformEffect {
    /// States that the transformation had no effect on the input.
    Identity,
    /// States that the transformation transformed the input.
    Transformed
}

impl BitOrAssign for TransformEffect {
    /// Assigns this `TransformEffect` to `rhs`.
    /// 
    /// This works equivalent to boolean or-assign
    /// where `Identity` is equal to `false` and
    /// `Transformed` is equal to `true`.
    fn bitor_assign(&mut self, rhs: TransformEffect) {
        match rhs {
            TransformEffect::Transformed => *self = rhs,
            TransformEffect::Identity    => ()
        }
    }
}

/// Simple struct to store a transformed expression
/// and a state indicating if it was actually transformed.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TransformOutcome {
    /// States if `expr` actually got transformed.
    pub result: TransformEffect,
    /// The (probably) transformed expression.
    pub expr: AnyExpr
}

impl TransformOutcome {
    /// Creates a new `TransformOutcome` with the given expression and state.
    pub fn new(result: TransformEffect, expr: AnyExpr) -> TransformOutcome {
        TransformOutcome{expr, result}
    }

    /// Creates a new non-transformed `TransformOutcome` for the given expression.
    pub fn identity<E>(expr: E) -> TransformOutcome
        where E: Into<AnyExpr>
    {
        TransformOutcome::new(TransformEffect::Identity, expr.into())
    }

    /// Creates a new transformed `TransformOutcome` for the given expression.
    pub fn transformed<E>(expr: E) -> TransformOutcome
        where E: Into<AnyExpr>
    {
        TransformOutcome::new(TransformEffect::Transformed, expr.into())
    }
}

/// Types implementing this trait are capable to modify any concrete expression type.
/// 
/// All transformation routines return a `TransformOutcome` that can be used by
/// a process that drives the transformations to check whether transformations
/// have been applied or not. This is useful for exhaustive transformations that
/// apply transform steps until nothing is left that can be further processed.
pub trait Transformer {
    fn transform_cond(&self, cond: expr::IfThenElse) -> TransformOutcome {
        TransformOutcome::identity(cond)
    }

    fn transform_var(&self, bool_var: expr::Symbol) -> TransformOutcome {
        TransformOutcome::identity(bool_var)
    }

    fn transform_bool_const(&self, bool_const: expr::BoolConst) -> TransformOutcome {
        TransformOutcome::identity(bool_const)
    }

    fn transform_bool_equals(&self, bool_equals: expr::BoolEquals) -> TransformOutcome {
        TransformOutcome::identity(bool_equals)
    }

    fn transform_and(&self, and: expr::And) -> TransformOutcome {
        TransformOutcome::identity(and)
    }

    fn transform_or(&self, or: expr::Or) -> TransformOutcome {
        TransformOutcome::identity(or)
    }

    fn transform_not(&self, not: expr::Not) -> TransformOutcome {
        TransformOutcome::identity(not)
    }

    fn transform_xor(&self, xor: expr::Xor) -> TransformOutcome {
        TransformOutcome::identity(xor)
    }

    fn transform_implies(&self, implies: expr::Implies) -> TransformOutcome {
        TransformOutcome::identity(implies)
    }

    fn transform_array_read(&self, array_read: expr::ArrayRead) -> TransformOutcome {
        TransformOutcome::identity(array_read)
    }

    fn transform_array_write(&self, array_write: expr::ArrayWrite) -> TransformOutcome {
        TransformOutcome::identity(array_write)
    }

    fn transform_bitvec_const(&self, bitvec_const: expr::BitvecConst) -> TransformOutcome {
        TransformOutcome::identity(bitvec_const)
    }

    fn transform_add(&self, add: expr::Add) -> TransformOutcome {
        TransformOutcome::identity(add)
    }

    fn transform_mul(&self, mul: expr::Mul) -> TransformOutcome {
        TransformOutcome::identity(mul)
    }

    fn transform_neg(&self, neg: expr::Neg) -> TransformOutcome {
        TransformOutcome::identity(neg)
    }

    fn transform_sdiv(&self, sdiv: expr::SignedDiv) -> TransformOutcome {
        TransformOutcome::identity(sdiv)
    }

    fn transform_smod(&self, smod: expr::SignedModulo) -> TransformOutcome {
        TransformOutcome::identity(smod)
    }

    fn transform_srem(&self, srem: expr::SignedRemainder) -> TransformOutcome {
        TransformOutcome::identity(srem)
    }

    fn transform_sub(&self, sub: expr::Sub) -> TransformOutcome {
        TransformOutcome::identity(sub)
    }

    fn transform_udiv(&self, udiv: expr::UnsignedDiv) -> TransformOutcome {
        TransformOutcome::identity(udiv)
    }

    fn transform_urem(&self, urem: expr::UnsignedRemainder) -> TransformOutcome {
        TransformOutcome::identity(urem)
    }

    fn transform_bitnot(&self, bitnot: expr::BitNot) -> TransformOutcome {
        TransformOutcome::identity(bitnot)
    }

    fn transform_bitand(&self, bitand: expr::BitAnd) -> TransformOutcome {
        TransformOutcome::identity(bitand)
    }

    fn transform_bitor(&self, bitor: expr::BitOr) -> TransformOutcome {
        TransformOutcome::identity(bitor)
    }

    fn transform_bitxor(&self, bitxor: expr::BitXor) -> TransformOutcome {
        TransformOutcome::identity(bitxor)
    }

    fn transform_concat(&self, concat: expr::Concat) -> TransformOutcome {
        TransformOutcome::identity(concat)
    }

    fn transform_extract(&self, extract: expr::Extract) -> TransformOutcome {
        TransformOutcome::identity(extract)
    }

    fn transform_sext(&self, sext: expr::SignExtend) -> TransformOutcome {
        TransformOutcome::identity(sext)
    }

    fn transform_zext(&self, zext: expr::ZeroExtend) -> TransformOutcome {
        TransformOutcome::identity(zext)
    }

    fn transform_bitvec_equals(&self, bitvec_equals: expr::BitvecEquals) -> TransformOutcome {
        TransformOutcome::identity(bitvec_equals)
    }

    fn transform_sge(&self, sge: expr::SignedGreaterEquals) -> TransformOutcome {
        TransformOutcome::identity(sge)
    }

    fn transform_sgt(&self, sgt: expr::SignedGreaterThan) -> TransformOutcome {
        TransformOutcome::identity(sgt)
    }

    fn transform_sle(&self, sle: expr::SignedLessEquals) -> TransformOutcome {
        TransformOutcome::identity(sle)
    }

    fn transform_slt(&self, slt: expr::SignedLessThan) -> TransformOutcome {
        TransformOutcome::identity(slt)
    }

    fn transform_uge(&self, uge: expr::UnsignedGreaterEquals) -> TransformOutcome {
        TransformOutcome::identity(uge)
    }

    fn transform_ugt(&self, ugt: expr::UnsignedGreaterThan) -> TransformOutcome {
        TransformOutcome::identity(ugt)
    }

    fn transform_ule(&self, ule: expr::UnsignedLessEquals) -> TransformOutcome {
        TransformOutcome::identity(ule)
    }

    fn transform_ult(&self, ult: expr::UnsignedLessThan) -> TransformOutcome {
        TransformOutcome::identity(ult)
    }

    fn transform_ashr(&self, ashr: expr::ArithmeticShiftRight) -> TransformOutcome {
        TransformOutcome::identity(ashr)
    }

    fn transform_lshr(&self, lshr: expr::LogicalShiftRight) -> TransformOutcome {
        TransformOutcome::identity(lshr)
    }

    fn transform_shl(&self, shl: expr::ShiftLeft) -> TransformOutcome {
        TransformOutcome::identity(shl)
    }
}

/// Expression transformers that may transform `AnyExpr` instances.
pub trait AnyExprTransformer {
    /// Transforms the given mutable `AnyExpr` inplace.
    /// 
    /// Returns a state indicating whether the given expression was actually transformed.
    fn transform_any_expr(&self, expr: &mut AnyExpr) -> TransformEffect;

    /// Consumed the given `AnyExpr` and transforms it.
    /// 
    /// Returns the resulting expression after the transformation and a state
    /// indicating whether the consumed expression was actually transformed.
    fn transform_any_expr_into(&self, expr: AnyExpr) -> TransformOutcome;
}

/// Implement this to activate automatic default implementation
/// of the `AnyTransformer` trait.
pub trait AutoImplAnyExprTransformer: Transformer {}

impl<T> AnyExprTransformer for T where T: Transformer + AutoImplAnyExprTransformer {
    fn transform_any_expr(&self, expr: &mut AnyExpr) -> TransformEffect {
        let temp = AnyExpr::from(expr::BoolConst::f());
		let input = mem::replace(expr, temp);
		let TransformOutcome{result, expr: transformed} =
            self.transform_any_expr_into(input);
        mem::replace(expr, transformed);
        result
    }

    fn transform_any_expr_into(&self, expr: AnyExpr) -> TransformOutcome {
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

/// Can traverse any expression and all of its child expressions recursively
/// and apply the given transformation pass on them.
/// 
/// Note that the internal AST transformer may be a modular transfomer that
/// combines several AST transformers into one.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TraverseTransformer<T>
    where T: AnyExprTransformer
{
    transformer: T
}

impl<T> TraverseTransformer<T>
    where T: AnyExprTransformer
{
    /// Traverse the given expression and all of its child expressions recursively
    /// and apply a transformation on them.
    pub fn traverse_transform(&self, expr: &mut AnyExpr) -> TransformEffect {
        let mut result = TransformEffect::Identity;
        // Transform the current expression before all of its children.
        result |= self.transformer.transform_any_expr(expr);
        for child in expr.children_mut() {
            result |= self.traverse_transform(child);
        }
        // Transform the current expression again after all of its children.
        result |= self.transformer.transform_any_expr(expr);
        result
    }

    /// Consumes the given expression and traverse it and all of its child
    /// expressions recursively and apply a transformation pass on them.
    pub fn traverse_transform_into(&self, expr: AnyExpr) -> TransformOutcome {
        let mut expr = expr;
        let result = self.traverse_transform(&mut expr);
        TransformOutcome::new(result, expr)
    }
}

macro_rules! modular_ast_transformer {
    ($(#[$attr:meta])* struct $name:ident { $($trans_id:ident: $trans_ty:ty),+ } ) => {
        $(#[$attr])*
        #[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
        pub struct $name {
            $($trans_id: $trans_ty),*
        }

        impl AnyExprTransformer for $name {
            fn transform_any_expr(&self, expr: &mut AnyExpr) -> TransformEffect {
                let mut result = TransformEffect::Identity;
                $(result |= self.$trans_id.transform_any_expr(expr));*;
                result
            }

            fn transform_any_expr_into(&self, expr: AnyExpr) -> TransformOutcome {
                let mut expr = expr;
                let result = self.transform_any_expr(&mut expr);
                TransformOutcome::new(result, expr)
            }
        }
    }
}
