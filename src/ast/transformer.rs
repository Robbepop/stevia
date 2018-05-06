use ast::prelude::*;

use std::mem;
use std::ops::BitOrAssign;

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

/// An event information that is attached to transformations.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TransformEvent {
    /// When the expression is initially visited by the transformer for a given simplification step.
    /// 
    /// This happens before visitng the expression's children.
    Entering,
    /// When the expression is visited the second time by the transformer for a given simplification step.
    ///
    /// This happens after visiting the expression's children.
    Leaving,
    /// After all simplifications have been made there is a post-processing sweep starting from the
    /// root expressions for all transformations.
    /// 
    /// Some transformations require a post processing step to finalize their simplifications.
    PostProcessing
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

    fn transform_cond_with_event(&self, cond: expr::IfThenElse, _: TransformEvent) -> TransformOutcome {
        self.transform_cond(cond)
    }

    fn transform_var(&self, bool_var: expr::Symbol) -> TransformOutcome {
        TransformOutcome::identity(bool_var)
    }

    fn transform_var_with_event(&self, bool_var: expr::Symbol, _: TransformEvent) -> TransformOutcome {
        self.transform_var(bool_var)
    }

    fn transform_bool_const(&self, bool_const: expr::BoolConst) -> TransformOutcome {
        TransformOutcome::identity(bool_const)
    }

    fn transform_bool_const_with_event(&self, bool_const: expr::BoolConst, _: TransformEvent) -> TransformOutcome {
        self.transform_bool_const(bool_const)
    }

    fn transform_bool_equals(&self, bool_equals: expr::BoolEquals) -> TransformOutcome {
        TransformOutcome::identity(bool_equals)
    }

    fn transform_bool_equals_with_event(&self, bool_equals: expr::BoolEquals, _: TransformEvent) -> TransformOutcome {
        self.transform_bool_equals(bool_equals)
    }

    fn transform_and(&self, and: expr::And) -> TransformOutcome {
        TransformOutcome::identity(and)
    }

    fn transform_and_with_event(&self, and: expr::And, _: TransformEvent) -> TransformOutcome {
        self.transform_and(and)
    }

    fn transform_or(&self, or: expr::Or) -> TransformOutcome {
        TransformOutcome::identity(or)
    }

    fn transform_or_with_event(&self, or: expr::Or, _: TransformEvent) -> TransformOutcome {
        self.transform_or(or)
    }

    fn transform_not(&self, not: expr::Not) -> TransformOutcome {
        TransformOutcome::identity(not)
    }

    fn transform_not_with_event(&self, not: expr::Not, _: TransformEvent) -> TransformOutcome {
        self.transform_not(not)
    }

    fn transform_xor(&self, xor: expr::Xor) -> TransformOutcome {
        TransformOutcome::identity(xor)
    }

    fn transform_xor_with_event(&self, xor: expr::Xor, _: TransformEvent) -> TransformOutcome {
        self.transform_xor(xor)
    }

    fn transform_implies(&self, implies: expr::Implies) -> TransformOutcome {
        TransformOutcome::identity(implies)
    }

    fn transform_implies_with_event(&self, implies: expr::Implies, _: TransformEvent) -> TransformOutcome {
        self.transform_implies(implies)
    }

    fn transform_array_read(&self, array_read: expr::ArrayRead) -> TransformOutcome {
        TransformOutcome::identity(array_read)
    }

    fn transform_array_read_with_event(&self, array_read: expr::ArrayRead, _: TransformEvent) -> TransformOutcome {
        self.transform_array_read(array_read)
    }

    fn transform_array_write(&self, array_write: expr::ArrayWrite) -> TransformOutcome {
        TransformOutcome::identity(array_write)
    }

    fn transform_array_write_with_event(&self, array_write: expr::ArrayWrite, _: TransformEvent) -> TransformOutcome {
        self.transform_array_write(array_write)
    }

    fn transform_bitvec_const(&self, bitvec_const: expr::BitvecConst) -> TransformOutcome {
        TransformOutcome::identity(bitvec_const)
    }

    fn transform_bitvec_const_with_event(&self, bitvec_const: expr::BitvecConst, _: TransformEvent) -> TransformOutcome {
        self.transform_bitvec_const(bitvec_const)
    }

    fn transform_add(&self, add: expr::Add) -> TransformOutcome {
        TransformOutcome::identity(add)
    }

    fn transform_add_with_event(&self, add: expr::Add, _: TransformEvent) -> TransformOutcome {
        self.transform_add(add)
    }

    fn transform_mul(&self, mul: expr::Mul) -> TransformOutcome {
        TransformOutcome::identity(mul)
    }

    fn transform_mul_with_event(&self, mul: expr::Mul, _: TransformEvent) -> TransformOutcome {
        self.transform_mul(mul)
    }

    fn transform_neg(&self, neg: expr::Neg) -> TransformOutcome {
        TransformOutcome::identity(neg)
    }

    fn transform_neg_with_event(&self, neg: expr::Neg, _: TransformEvent) -> TransformOutcome {
        self.transform_neg(neg)
    }

    fn transform_sdiv(&self, sdiv: expr::SignedDiv) -> TransformOutcome {
        TransformOutcome::identity(sdiv)
    }

    fn transform_sdiv_with_event(&self, sdiv: expr::SignedDiv, _: TransformEvent) -> TransformOutcome {
        self.transform_sdiv(sdiv)
    }

    fn transform_smod(&self, smod: expr::SignedModulo) -> TransformOutcome {
        TransformOutcome::identity(smod)
    }

    fn transform_smod_with_event(&self, smod: expr::SignedModulo, _: TransformEvent) -> TransformOutcome {
        self.transform_smod(smod)
    }

    fn transform_srem(&self, srem: expr::SignedRemainder) -> TransformOutcome {
        TransformOutcome::identity(srem)
    }

    fn transform_srem_with_event(&self, srem: expr::SignedRemainder, _: TransformEvent) -> TransformOutcome {
        self.transform_srem(srem)
    }

    fn transform_sub(&self, sub: expr::Sub) -> TransformOutcome {
        TransformOutcome::identity(sub)
    }

    fn transform_sub_with_event(&self, sub: expr::Sub, _: TransformEvent) -> TransformOutcome {
        self.transform_sub(sub)
    }

    fn transform_udiv(&self, udiv: expr::UnsignedDiv) -> TransformOutcome {
        TransformOutcome::identity(udiv)
    }

    fn transform_udiv_with_event(&self, udiv: expr::UnsignedDiv, _: TransformEvent) -> TransformOutcome {
        self.transform_udiv(udiv)
    }

    fn transform_urem(&self, urem: expr::UnsignedRemainder) -> TransformOutcome {
        TransformOutcome::identity(urem)
    }

    fn transform_urem_with_event(&self, urem: expr::UnsignedRemainder, _: TransformEvent) -> TransformOutcome {
        self.transform_urem(urem)
    }

    fn transform_bitnot(&self, bitnot: expr::BitNot) -> TransformOutcome {
        TransformOutcome::identity(bitnot)
    }

    fn transform_bitnot_with_event(&self, bitnot: expr::BitNot, _: TransformEvent) -> TransformOutcome {
        self.transform_bitnot(bitnot)
    }

    fn transform_bitand(&self, bitand: expr::BitAnd) -> TransformOutcome {
        TransformOutcome::identity(bitand)
    }

    fn transform_bitand_with_event(&self, bitand: expr::BitAnd, _: TransformEvent) -> TransformOutcome {
        self.transform_bitand(bitand)
    }

    fn transform_bitor(&self, bitor: expr::BitOr) -> TransformOutcome {
        TransformOutcome::identity(bitor)
    }

    fn transform_bitor_with_event(&self, bitor: expr::BitOr, _: TransformEvent) -> TransformOutcome {
        self.transform_bitor(bitor)
    }

    fn transform_bitxor(&self, bitxor: expr::BitXor) -> TransformOutcome {
        TransformOutcome::identity(bitxor)
    }

    fn transform_bitxor_with_event(&self, bitxor: expr::BitXor, _: TransformEvent) -> TransformOutcome {
        self.transform_bitxor(bitxor)
    }

    fn transform_concat(&self, concat: expr::Concat) -> TransformOutcome {
        TransformOutcome::identity(concat)
    }

    fn transform_concat_with_event(&self, concat: expr::Concat, _: TransformEvent) -> TransformOutcome {
        self.transform_concat(concat)
    }

    fn transform_extract(&self, extract: expr::Extract) -> TransformOutcome {
        TransformOutcome::identity(extract)
    }

    fn transform_extract_with_event(&self, extract: expr::Extract, _: TransformEvent) -> TransformOutcome {
        self.transform_extract(extract)
    }

    fn transform_sext(&self, sext: expr::SignExtend) -> TransformOutcome {
        TransformOutcome::identity(sext)
    }

    fn transform_sext_with_event(&self, sext: expr::SignExtend, _: TransformEvent) -> TransformOutcome {
        self.transform_sext(sext)
    }

    fn transform_zext(&self, zext: expr::ZeroExtend) -> TransformOutcome {
        TransformOutcome::identity(zext)
    }

    fn transform_zext_with_event(&self, zext: expr::ZeroExtend, _: TransformEvent) -> TransformOutcome {
        self.transform_zext(zext)
    }

    fn transform_bitvec_equals(&self, bitvec_equals: expr::BitvecEquals) -> TransformOutcome {
        TransformOutcome::identity(bitvec_equals)
    }

    fn transform_bitvec_equals_with_event(&self, bitvec_equals: expr::BitvecEquals, _: TransformEvent) -> TransformOutcome {
        self.transform_bitvec_equals(bitvec_equals)
    }

    fn transform_sge(&self, sge: expr::SignedGreaterEquals) -> TransformOutcome {
        TransformOutcome::identity(sge)
    }

    fn transform_sge_with_event(&self, sge: expr::SignedGreaterEquals, _: TransformEvent) -> TransformOutcome {
        self.transform_sge(sge)
    }

    fn transform_sgt(&self, sgt: expr::SignedGreaterThan) -> TransformOutcome {
        TransformOutcome::identity(sgt)
    }

    fn transform_sgt_with_event(&self, sgt: expr::SignedGreaterThan, _: TransformEvent) -> TransformOutcome {
        self.transform_sgt(sgt)
    }

    fn transform_sle(&self, sle: expr::SignedLessEquals) -> TransformOutcome {
        TransformOutcome::identity(sle)
    }

    fn transform_sle_with_event(&self, sle: expr::SignedLessEquals, _: TransformEvent) -> TransformOutcome {
        self.transform_sle(sle)
    }

    fn transform_slt(&self, slt: expr::SignedLessThan) -> TransformOutcome {
        TransformOutcome::identity(slt)
    }

    fn transform_slt_with_event(&self, slt: expr::SignedLessThan, _: TransformEvent) -> TransformOutcome {
        self.transform_slt(slt)
    }

    fn transform_uge(&self, uge: expr::UnsignedGreaterEquals) -> TransformOutcome {
        TransformOutcome::identity(uge)
    }

    fn transform_uge_with_event(&self, uge: expr::UnsignedGreaterEquals, _: TransformEvent) -> TransformOutcome {
        self.transform_uge(uge)
    }

    fn transform_ugt(&self, ugt: expr::UnsignedGreaterThan) -> TransformOutcome {
        TransformOutcome::identity(ugt)
    }

    fn transform_ugt_with_event(&self, ugt: expr::UnsignedGreaterThan, _: TransformEvent) -> TransformOutcome {
        self.transform_ugt(ugt)
    }

    fn transform_ule(&self, ule: expr::UnsignedLessEquals) -> TransformOutcome {
        TransformOutcome::identity(ule)
    }

    fn transform_ule_with_event(&self, ule: expr::UnsignedLessEquals, _: TransformEvent) -> TransformOutcome {
        self.transform_ule(ule)
    }

    fn transform_ult(&self, ult: expr::UnsignedLessThan) -> TransformOutcome {
        TransformOutcome::identity(ult)
    }

    fn transform_ult_with_event(&self, ult: expr::UnsignedLessThan, _: TransformEvent) -> TransformOutcome {
        self.transform_ult(ult)
    }

    fn transform_ashr(&self, ashr: expr::ArithmeticShiftRight) -> TransformOutcome {
        TransformOutcome::identity(ashr)
    }

    fn transform_ashr_with_event(&self, ashr: expr::ArithmeticShiftRight, _: TransformEvent) -> TransformOutcome {
        self.transform_ashr(ashr)
    }

    fn transform_lshr(&self, lshr: expr::LogicalShiftRight) -> TransformOutcome {
        TransformOutcome::identity(lshr)
    }

    fn transform_lshr_with_event(&self, lshr: expr::LogicalShiftRight, _: TransformEvent) -> TransformOutcome {
        self.transform_lshr(lshr)
    }

    fn transform_shl(&self, shl: expr::ShiftLeft) -> TransformOutcome {
        TransformOutcome::identity(shl)
    }

    fn transform_shl_with_event(&self, shl: expr::ShiftLeft, _: TransformEvent) -> TransformOutcome {
        self.transform_shl(shl)
    }
}

/// Expression transformers that may transform `AnyExpr` instances.
pub trait AnyExprTransformer {
    /// Transforms the given mutable `AnyExpr` inplace.
    /// 
    /// Returns a state indicating whether the given expression was actually transformed.
    fn transform_any_expr(&self, expr: &mut AnyExpr, event: TransformEvent) -> TransformEffect;

    /// Consumed the given `AnyExpr` and transforms it.
    /// 
    /// Returns the resulting expression after the transformation and a state
    /// indicating whether the consumed expression was actually transformed.
    fn transform_any_expr_into(&self, expr: AnyExpr, event: TransformEvent) -> TransformOutcome;
}

/// Implement this to activate automatic default implementation
/// of the `AnyTransformer` trait.
pub trait AutoImplAnyExprTransformer: Transformer {}

pub fn forward_transform_any_expr_into<T>(transformer: &T, expr: AnyExpr, event: TransformEvent) -> TransformOutcome
    where T: Transformer
{
    use self::AnyExpr::*;
    match expr {
        IfThenElse(expr) => transformer.transform_cond_with_event(expr, event),
        Symbol(expr) => transformer.transform_var_with_event(expr, event),
        BoolConst(expr) => transformer.transform_bool_const_with_event(expr, event),
        BoolEquals(expr) => transformer.transform_bool_equals_with_event(expr, event),
        Not(expr) => transformer.transform_not_with_event(expr, event),
        And(expr) => transformer.transform_and_with_event(expr, event),
        Or(expr) => transformer.transform_or_with_event(expr, event),
        Xor(expr) => transformer.transform_xor_with_event(expr, event),
        Implies(expr) => transformer.transform_implies_with_event(expr, event),
        ArrayRead(expr) => transformer.transform_array_read_with_event(expr, event),
        ArrayWrite(expr) => transformer.transform_array_write_with_event(expr, event),
        Add(expr) => transformer.transform_add_with_event(expr, event),
        BitvecConst(expr) => transformer.transform_bitvec_const_with_event(expr, event),
        Mul(expr) => transformer.transform_mul_with_event(expr, event),
        Neg(expr) => transformer.transform_neg_with_event(expr, event),
        SignedDiv(expr) => transformer.transform_sdiv_with_event(expr, event),
        SignedModulo(expr) => transformer.transform_smod_with_event(expr, event),
        SignedRemainder(expr) => transformer.transform_srem_with_event(expr, event),
        Sub(expr) => transformer.transform_sub_with_event(expr, event),
        UnsignedDiv(expr) => transformer.transform_udiv_with_event(expr, event),
        UnsignedRemainder(expr) => transformer.transform_urem_with_event(expr, event),
        BitAnd(expr) => transformer.transform_bitand_with_event(expr, event),
        BitNot(expr) => transformer.transform_bitnot_with_event(expr, event),
        BitOr(expr) => transformer.transform_bitor_with_event(expr, event),
        BitXor(expr) => transformer.transform_bitxor_with_event(expr, event),
        Concat(expr) => transformer.transform_concat_with_event(expr, event),
        Extract(expr) => transformer.transform_extract_with_event(expr, event),
        SignExtend(expr) => transformer.transform_sext_with_event(expr, event),
        ZeroExtend(expr) => transformer.transform_zext_with_event(expr, event),
        BitvecEquals(expr) => transformer.transform_bitvec_equals_with_event(expr, event),
        SignedGreaterEquals(expr) => transformer.transform_sge_with_event(expr, event),
        SignedGreaterThan(expr) => transformer.transform_sgt_with_event(expr, event),
        SignedLessEquals(expr) => transformer.transform_sle_with_event(expr, event),
        SignedLessThan(expr) => transformer.transform_slt_with_event(expr, event),
        UnsignedGreaterEquals(expr) => transformer.transform_uge_with_event(expr, event),
        UnsignedGreaterThan(expr) => transformer.transform_ugt_with_event(expr, event),
        UnsignedLessEquals(expr) => transformer.transform_ule_with_event(expr, event),
        UnsignedLessThan(expr) => transformer.transform_ult_with_event(expr, event),
        ArithmeticShiftRight(expr) => transformer.transform_ashr_with_event(expr, event),
        LogicalShiftRight(expr) => transformer.transform_lshr_with_event(expr, event),
        ShiftLeft(expr) => transformer.transform_shl_with_event(expr, event)
    }
}

impl<T> AnyExprTransformer for T where T: AutoImplAnyExprTransformer {
    fn transform_any_expr(&self, expr: &mut AnyExpr, event: TransformEvent) -> TransformEffect {
        let temp = AnyExpr::from(expr::BoolConst::f());
		let input = mem::replace(expr, temp);
		let TransformOutcome{result, expr: transformed} =
            self.transform_any_expr_into(input, event);
        mem::replace(expr, transformed);
        result
    }

    fn transform_any_expr_into(&self, expr: AnyExpr, event: TransformEvent) -> TransformOutcome {
        forward_transform_any_expr_into(self, expr, event)
    }
}

/// Can traverse any expression and all of its child expressions recursively
/// and apply the given transformation pass on them.
/// 
/// Note that the internal AST transformer may be a modular transfomer that
/// combines several AST transformers into one.
#[derive(Debug, Default)]
pub struct TraverseTransformer<T>
    where T: AnyExprTransformer
{
    transformer: T
}

impl<T> From<ArcContext> for TraverseTransformer<T>
where
    T: AnyExprTransformer + From<ArcContext>
{
    fn from(ctx: ArcContext) -> Self {
        Self{ transformer: T::from(ctx) }
    }
}

impl<'ctx, T> From<&'ctx Context> for TraverseTransformer<T>
where
    T: AnyExprTransformer + From<&'ctx Context>
{
    fn from(ctx: &'ctx Context) -> Self {
        Self{ transformer: T::from(ctx) }
    }
}

impl<T> TraverseTransformer<T>
    where T: AnyExprTransformer
{
    /// Traverses the given expression and all of its child expressions recursively and
    /// applies a transformation process upon entering and leaving any expression node.
    fn recursive_traverse_transform(&self, expr: &mut AnyExpr) -> TransformEffect {
        let mut result = TransformEffect::Identity;
        // Transform the current expression before all of its children.
        result |= self.transformer.transform_any_expr(expr, TransformEvent::Entering);
        for child in expr.children_mut() {
            result |= self.traverse_transform(child);
        }
        // Transform the current expression again after all of its children.
        result |= self.transformer.transform_any_expr(expr, TransformEvent::Leaving);
        result
    }

    /// Forwards to recursively traverse and transform the given expression and also
    /// performs a post-processing step for the given root node.
    pub fn traverse_transform(&self, root: &mut AnyExpr) -> TransformEffect {
        let mut effect = self.recursive_traverse_transform(root);
        effect |= self.transformer.transform_any_expr(root, TransformEvent::PostProcessing);
        effect
    }

    /// Consumes the given expression and traverse it and all of its child
    /// expressions recursively and apply a transformation pass on them.
    pub fn traverse_transform_into(&self, root: AnyExpr) -> TransformOutcome {
        let mut root = root;
        let result = self.traverse_transform(&mut root);
        TransformOutcome::new(result, root)
    }
}

macro_rules! modular_ast_transformer {
    ($(#[$attr:meta])* struct $name:ident { $($trans_id:ident: $trans_ty:ty),+ } ) => {
        $(#[$attr])*
        #[derive(Debug, Clone)]
        pub struct $name {
            $($trans_id: $trans_ty),*
        }

        impl From<ArcContext> for $name {
            fn from(ctx: ArcContext) -> Self {
                Self{
                    $($trans_id: ctx.clone().into()),*
                }
            }
        }

        impl<'ctx> From<&'ctx Context> for $name {
            fn from(ctx: &'ctx Context) -> Self {
                Self{
                    $($trans_id: ctx.into()),*
                }
            }
        }

        impl AnyExprTransformer for $name {
            fn transform_any_expr(&self, expr: &mut AnyExpr, event: TransformEvent) -> TransformEffect {
                let mut result = TransformEffect::Identity;
                $(result |= self.$trans_id.transform_any_expr(expr, event));*;
                result
            }

            fn transform_any_expr_into(&self, expr: AnyExpr, event: TransformEvent) -> TransformOutcome {
                let mut expr = expr;
                let result = self.transform_any_expr(&mut expr, event);
                TransformOutcome::new(result, expr)
            }
        }
    }
}
