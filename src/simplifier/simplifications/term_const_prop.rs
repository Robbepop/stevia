use ast::prelude::*;

use apint::{ShiftAmount, Width};
use either::Either;

use itertools::Itertools;

pub mod prelude {
    pub use super::TermConstPropagator;
}

/// This simplification procedure propagates constant values through boolean expressions.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TermConstPropagator;

impl AutoImplAnyExprTransformer for TermConstPropagator {}

fn simplify_neg(neg: expr::Neg) -> TransformOutcome {
    // If the child expression is a constant value, simply negate it.
    if let box AnyExpr::BitvecConst(mut bv_const) = neg.child {
        bv_const.val.negate();
        return TransformOutcome::transformed(bv_const)
    }
    TransformOutcome::identity(neg)
}

fn simplify_bitvec_equals(equals: expr::BitvecEquals) -> TransformOutcome {
    // If there exist at least two constant child expressions we can compare
    // them in order to either merge them or simplify the entire equality to false.
    if equals.children().filter(|c| c.get_if_bitvec_const().is_some()).count() >= 2 {
        // Split const and non-const child expressions.
        let (mut consts, mut rest): (Vec<_>, Vec<_>) = equals.into_children().partition_map(|c| {
            match c {
                AnyExpr::BitvecConst(c) => Either::Left(c.val),
                other                   => Either::Right(other)
            }
        });
        assert!(!consts.is_empty());
        // Do not remove duplicates since this is already done by normalization.
        // Just look for unequal constant elements.
        if consts.iter().all_equal() {
            // We can simply put one of the constant elements back into the rest
            // and return it if the rest is not empty.
            if !rest.is_empty() {
                rest.push(consts.pop().map(expr::BitvecConst::from).map(AnyExpr::from).unwrap());
                return TransformOutcome::transformed(expr::BitvecEquals::nary(rest).unwrap())
            }
            // If the rest was empty we have shown that all elements compared equal
            // and thus the entire bitvector equality expression evaluates to true.
            else {
                return TransformOutcome::transformed(expr::BoolConst::t())
            }
        }
        // Some constant elements where unequal and thus the entire bitvector
        // equality comparison evaluates to false.
        else {
            return TransformOutcome::transformed(expr::BoolConst::f())
        }
    }
    TransformOutcome::identity(equals)
}

fn simplify_bitnot(bitnot: expr::BitNot) -> TransformOutcome {
    // If the child expression is a constant value, simply bit-negate it.
    if let box AnyExpr::BitvecConst(mut bv_const) = bitnot.child {
        bv_const.val.bitnot();
        return TransformOutcome::transformed(bv_const)
    }
    TransformOutcome::identity(bitnot)
}

fn simplify_add(add: expr::Add) -> TransformOutcome {
    // We need to mutate add perhaps.
    let mut add = add;
    // Remove all zeros from this add as their are the additive neutral element and have
    // no effect besides wasting memory.
    if add.children().filter_map(|c| c.get_if_bitvec_const()).filter(|c| c.is_zero()).count() > 0 {
        add.retain_children(|c| c.get_if_bitvec_const().map_or(true, |c| !c.is_zero()));
        match add.arity() {
            0 => return TransformOutcome::transformed(expr::BitvecConst::zero(add.bitvec_ty)),
            1 => return TransformOutcome::transformed(add.into_children().next().unwrap()),
            _ => ()
        }
    }
    // If there exist at least two constant child expressions within this and expression
    // we can evaluate their sum and replace the constant child expressions with it.
    if add.children().filter(|c| c.get_if_bitvec_const().is_some()).count() >= 2 {
        // Split const and non-const child expressions.
        let (consts, mut rest): (Vec<_>, Vec<_>) = add.into_children().partition_map(|c| {
            match c {
                AnyExpr::BitvecConst(c) => Either::Left(c.val),
                other                   => Either::Right(other)
            }
        });
        assert!(!consts.is_empty());
        use itertools::Itertools;
        // Evalute the sum of all constant expressions.
        let sum = consts.into_iter().fold1(|mut lhs, rhs| { lhs += &rhs; lhs }).unwrap();
        // If the rest is empty and thus the sum is the only child expression remaining
        // we can replace the entire and with the sum. Otherwise we just reconstruct the
        // and expression with the new sum.
        let result = if rest.is_empty() {
            AnyExpr::from(expr::BitvecConst::from(sum))
        }
        else {
            rest.push(AnyExpr::from(expr::BitvecConst::from(sum)));
            AnyExpr::from(expr::Add::nary(rest).unwrap())
        };
        return TransformOutcome::transformed(result)
    }
    TransformOutcome::identity(add)
}

fn simplify_sub(sub: expr::Sub) -> TransformOutcome {
    // If both child expressions are const bitvectors we can simplify this to
    // the result of their subtraction.
    if let box BinExprChildren{ lhs: AnyExpr::BitvecConst(lhs), rhs: AnyExpr::BitvecConst(rhs) } = sub.children {
        let result_udiv = lhs.val.into_checked_sub(&rhs.val).unwrap();
        return TransformOutcome::transformed(expr::BitvecConst::from(result_udiv))
    }
    // If the left-hand side is constant zero we can simplify this subtraction
    // to the negated right-hand side.
    if let Some(lval) = sub.children.lhs.get_if_bitvec_const() {
        if lval.is_zero() {
            let negated_rhs = expr::Neg::new(sub.children.rhs).unwrap();
            return TransformOutcome::transformed(negated_rhs)
        }
    }
    // If the right-hand side is constant zero we can simplify this subtraction
    // to the left-hand side.
    if let Some(rval) = sub.children.rhs.get_if_bitvec_const() {
        if rval.is_zero() {
            return TransformOutcome::transformed(sub.children.lhs)
        }
    }
    TransformOutcome::identity(sub)
}

fn simplify_mul(mul: expr::Mul) -> TransformOutcome {
    // If there exist a const zero child expression the entire multiplication is zero.
    if mul.children().filter_map(|c| c.get_if_bitvec_const()).filter(|c| c.is_zero()).count() > 0 {
        return TransformOutcome::transformed(expr::BitvecConst::zero(mul.bitvec_ty))
    }
    // We need to mutate mul perhaps.
    let mut mul = mul;
    // Remove all ones from this mul as they are the multiplicative neutral element and have
    // no effect besides wasting memory.
    if mul.children().filter_map(|c| c.get_if_bitvec_const()).filter(|c| c.is_one()).count() > 0 {
        mul.retain_children(|c| c.get_if_bitvec_const().map_or(true, |c| !c.is_one()));
        match mul.arity() {
            0 => return TransformOutcome::transformed(expr::BitvecConst::one(mul.bitvec_ty)),
            1 => return TransformOutcome::transformed(mul.into_children().next().unwrap()),
            _ => ()
        }
    }
    // If there exist at least two constant child expressions within this and expression
    // we can evaluate their product and replace the constant child expressions with it.
    if mul.children().filter(|c| c.get_if_bitvec_const().is_some()).count() >= 2 {
        // Split const and non-const child expressions.
        let (consts, mut rest): (Vec<_>, Vec<_>) = mul.into_children().partition_map(|c| {
            match c {
                AnyExpr::BitvecConst(c) => Either::Left(c.val),
                other                   => Either::Right(other)
            }
        });
        assert!(!consts.is_empty());
        use itertools::Itertools;
        // Evalute the product of all constant expressions.
        let product = consts.into_iter().fold1(|mut lhs, rhs| { lhs *= &rhs; lhs }).unwrap();
        // If the rest is empty and thus the sum is the only child expression remaining
        // we can replace the entire and with the sum. Otherwise we just reconstruct the
        // and expression with the new sum.
        let result = if rest.is_empty() {
            AnyExpr::from(expr::BitvecConst::from(product))
        }
        else {
            rest.push(AnyExpr::from(expr::BitvecConst::from(product)));
            AnyExpr::from(expr::Mul::nary(rest).unwrap())
        };
        return TransformOutcome::transformed(result)
    }
    TransformOutcome::identity(mul)
}

macro_rules! transform_div_impl {
    ($varname:ident, $into_checked:ident) => {{
        // If both child expressions are constant bitvectors we can evaluate the division
        // and replace this division expression by the result.
        if let box BinExprChildren{ lhs: AnyExpr::BitvecConst(lhs), rhs: AnyExpr::BitvecConst(rhs) } = $varname.children {
            let result = lhs.val.$into_checked(&rhs.val).unwrap();
            return TransformOutcome::transformed(expr::BitvecConst::from(result))
        }
        if let Some(rhs) = $varname.children.rhs.get_if_bitvec_const() {
            // Encountered a division by zero. Stevia simply returns the left-hand side in this case.
            if rhs.is_zero() {
                warn!("Encountered a division by zero with: {:?}. \
                       Stevia simply returns the left-hand side in this case.", $varname);
                return TransformOutcome::transformed($varname.children.lhs)
            }
            // Division by one can be replace by the left-hand side expression.
            if rhs.is_one() {
                return TransformOutcome::transformed($varname.children.lhs)
            }
        }
        // If the left-hand side is zero the entire division can only result to zero.
        if let Some(lhs) = $varname.children.lhs.get_if_bitvec_const() {
            // Since the left-hand side is already a zero constant we can simply take it.
            if lhs.is_zero() {
                return TransformOutcome::transformed($varname.children.lhs)
            }
        }
        TransformOutcome::identity($varname)
    }};
}

fn simplify_udiv(udiv: expr::UnsignedDiv) -> TransformOutcome {
    transform_div_impl!(udiv, into_checked_udiv)
}

fn simplify_sdiv(sdiv: expr::SignedDiv) -> TransformOutcome {
    transform_div_impl!(sdiv, into_checked_sdiv)
}

macro_rules! transform_rem_impl {
    ($varname:ident, $into_checked:ident) => {{
        // If both child expressions are constant bitvectors we can evaluate the remainder
        // and replace this remainder expression by the result.
        if let box BinExprChildren{ lhs: AnyExpr::BitvecConst(lhs), rhs: AnyExpr::BitvecConst(rhs) } = $varname.children {
            let result = lhs.val.$into_checked(&rhs.val).unwrap();
            return TransformOutcome::transformed(expr::BitvecConst::from(result))
        }
        if let Some(rhs) = $varname.children.rhs.get_if_bitvec_const() {
            // Encountered a division (remainder) by zero. Stevia simply returns the left-hand side in this case.
            if rhs.is_zero() {
                warn!("Encountered a division (remainder) by zero with: {:?}. \
                       Stevia simply returns the left-hand side in this case.", $varname);
                return TransformOutcome::transformed($varname.children.lhs)
            }
            // Remainder of one can be replaced by constant zero.
            if rhs.is_one() {
                return TransformOutcome::transformed(expr::BitvecConst::zero($varname.bitvec_ty))
            }
        }
        // If the left-hand side is zero the entire division can only result to zero.
        if let Some(lhs) = $varname.children.lhs.get_if_bitvec_const() {
            // Since the left-hand side is already a zero constant we can simply take it.
            if lhs.is_zero() {
                return TransformOutcome::transformed($varname.children.lhs)
            }
        }
        TransformOutcome::identity($varname)
    }};
}

fn simplify_urem(urem: expr::UnsignedRemainder) -> TransformOutcome {
    transform_rem_impl!(urem, into_checked_urem)
}

fn simplify_srem(srem: expr::SignedRemainder) -> TransformOutcome {
    transform_rem_impl!(srem, into_checked_srem)
}

fn simplify_bitand(bitand: expr::BitAnd) -> TransformOutcome {
    // If there exist a const zero child expression the entire bit-and is zero.
    if bitand.children().filter_map(|c| c.get_if_bitvec_const()).filter(|c| c.is_zero()).count() > 0 {
        return TransformOutcome::transformed(expr::BitvecConst::zero(bitand.bitvec_ty))
    }
    // We need to mutate bitand perhaps.
    let mut bitand = bitand;
    // Remove all const bitvector child expressions that have all their bits set from this bit-and
    // as they are the bit-and neutral element and have no effect besides wasting memory.
    if bitand.children().filter_map(|c| c.get_if_bitvec_const()).filter(|c| c.is_all_set()).count() > 0 {
        bitand.retain_children(|c| c.get_if_bitvec_const().map_or(true, |c| !c.is_all_set()));
        match bitand.arity() {
            0 => return TransformOutcome::transformed(expr::BitvecConst::all_set(bitand.bitvec_ty)),
            1 => return TransformOutcome::transformed(bitand.into_children().next().unwrap()),
            _ => ()
        }
    }
    // If there exist at least two constant child expressions within this bit-and expression
    // we can evaluate their bit-and result and replace the constant child expressions with it.
    if bitand.children().filter(|c| c.get_if_bitvec_const().is_some()).count() >= 2 {
        // Split const and non-const child expressions.
        let (consts, mut rest): (Vec<_>, Vec<_>) = bitand.into_children().partition_map(|c| {
            match c {
                AnyExpr::BitvecConst(c) => Either::Left(c.val),
                other                   => Either::Right(other)
            }
        });
        assert!(!consts.is_empty());
        use itertools::Itertools;
        // Evalute the bit-and result of all constant expressions.
        let accumulated = consts.into_iter().fold1(|mut lhs, rhs| { lhs &= &rhs; lhs }).unwrap();
        // If the rest is empty and thus the accumulated bit-and is the only child expression remaining
        // we can replace the entire bit-and with the result. Otherwise we just reconstruct the
        // and expression with the accumulated bit-and.
        let result = if rest.is_empty() {
            AnyExpr::from(expr::BitvecConst::from(accumulated))
        }
        else {
            rest.push(AnyExpr::from(expr::BitvecConst::from(accumulated)));
            AnyExpr::from(expr::BitAnd::nary(rest).unwrap())
        };
        return TransformOutcome::transformed(result)
    }
    TransformOutcome::identity(bitand)
}

fn simplify_bitor(bitor: expr::BitOr) -> TransformOutcome {
    // If there exist a const all-set child expression the entire bit-or is all-set.
    if bitor.children().filter_map(|c| c.get_if_bitvec_const()).filter(|c| c.is_all_set()).count() > 0 {
        return TransformOutcome::transformed(expr::BitvecConst::all_set(bitor.bitvec_ty))
    }
    // We need to mutate bitor perhaps.
    let mut bitor = bitor;
    // Remove all const bitvector child expressions that have all their bits unset from this bit-or
    // as they are the bit-or neutral element and have no effect besides wasting memory.
    if bitor.children().filter_map(|c| c.get_if_bitvec_const()).filter(|c| c.is_all_unset()).count() > 0 {
        bitor.retain_children(|c| c.get_if_bitvec_const().map_or(true, |c| !c.is_all_unset()));
        match bitor.arity() {
            0 => return TransformOutcome::transformed(expr::BitvecConst::all_set(bitor.bitvec_ty)),
            1 => return TransformOutcome::transformed(bitor.into_children().next().unwrap()),
            _ => ()
        }
    }
    // If there exist at least two constant child expressions within this bit-or expression
    // we can evaluate their bit-or result and replace the constant child expressions with it.
    if bitor.children().filter(|c| c.get_if_bitvec_const().is_some()).count() >= 2 {
        // Split const and non-const child expressions.
        let (consts, mut rest): (Vec<_>, Vec<_>) = bitor.into_children().partition_map(|c| {
            match c {
                AnyExpr::BitvecConst(c) => Either::Left(c.val),
                other                   => Either::Right(other)
            }
        });
        assert!(!consts.is_empty());
        use itertools::Itertools;
        // Evalute the bit-or result of all constant expressions.
        let accumulated = consts.into_iter().fold1(|mut lhs, rhs| { lhs |= &rhs; lhs }).unwrap();
        // If the rest is empty and thus the accumulated bit-or is the only child expression remaining
        // we can replace the entire bit-or with the result. Otherwise we just reconstruct the
        // and expression with the accumulated bit-and.
        let result = if rest.is_empty() {
            AnyExpr::from(expr::BitvecConst::from(accumulated))
        }
        else {
            rest.push(AnyExpr::from(expr::BitvecConst::from(accumulated)));
            AnyExpr::from(expr::BitOr::nary(rest).unwrap())
        };
        return TransformOutcome::transformed(result)
    }
    TransformOutcome::identity(bitor)
}

fn simplify_bitxor(bitxor: expr::BitXor) -> TransformOutcome {
    // If both child expressions are constant bitvectors we can simply evaluate the result.
    if let box BinExprChildren{ lhs: AnyExpr::BitvecConst(lhs), rhs: AnyExpr::BitvecConst(rhs) } = bitxor.children {
        let result = lhs.val.into_checked_bitxor(&rhs.val).unwrap();
        return TransformOutcome::transformed(expr::BitvecConst::from(result))
    }
    if let Some(lval) = bitxor.children.lhs.get_if_bitvec_const() {
        // If the left-hand side is constant zero we can simplify this bit-xor
        // to the right-hand side.
        if lval.is_zero() {
            return TransformOutcome::transformed(bitxor.children.rhs)
        }
        // If the left-hand side is constant all-set we can simplify this bit-xor
        // to the negated right-hand side.
        if lval.is_all_set() {
            let negated_rhs = expr::BitNot::new(bitxor.children.rhs).unwrap();
            return TransformOutcome::transformed(negated_rhs)
        }
    }
    if let Some(rval) = bitxor.children.rhs.get_if_bitvec_const() {
        // If the right-hand side is constant zero we can simplify this bit-xor
        // to the left-hand side.
        if rval.is_zero() {
            return TransformOutcome::transformed(bitxor.children.lhs)
        }
        // If the right-hand side is constant all-set we can simplify this bit-xor
        // to the negated left-hand side.
        if rval.is_all_set() {
            let negated_rhs = expr::BitNot::new(bitxor.children.lhs).unwrap();
            return TransformOutcome::transformed(negated_rhs)
        }
    }
    TransformOutcome::identity(bitxor)
}

fn simplify_shl(shl: expr::ShiftLeft) -> TransformOutcome {
    // If the left-hand side is constant zero the entire shift-left evaluates to zero.
    if let Some(lval) = shl.children.lhs.get_if_bitvec_const() {
        if lval.is_zero() {
            return TransformOutcome::transformed(expr::BitvecConst::zero(lval.width().into()))
        }
    }
    // If the right-hand side is constant zero the entire shift-left evaluates to the left-hand side.
    if let Some(rval) = shl.children.rhs.get_if_bitvec_const() {
        let width = shl.bitvec_ty.width();
        if rval.is_zero() {
            return TransformOutcome::transformed(shl.children.lhs)
        }
        match rval.try_to_u32() {
            Err(_) => {
                warn!("Encountered right-hand side left-shift shift-amount that is larger than 2^32 in: {:?} \n\
                       Stevia handles this by returning constant zero.", shl);
                return TransformOutcome::transformed(expr::BitvecConst::zero(shl.bitvec_ty))
            }
            Ok(val) => {
                let shamt = ShiftAmount::from(val as usize);
                // TODO in crate apint: make ShiftAmount::to_usize public
                if shamt.to_usize() >= width.to_usize() {
                    warn!("Encountered right-hand side left-shift overflow with child expressions in: {:?} \n\
                           Stevia handles this by returning constant zero.", shl);
                    return TransformOutcome::transformed(expr::BitvecConst::zero(shl.bitvec_ty))
                }
            }
        }
    }
    // If both child expressions are constant bitvectors we can simply evaluate the result.
    if let box BinExprChildren{ lhs: AnyExpr::BitvecConst(lhs), rhs: AnyExpr::BitvecConst(rhs) } = shl.children {
        let rval = rhs.val.try_to_u32().unwrap();
        let shamt = ShiftAmount::from(rval as usize);
        let result = lhs.val.into_checked_shl(shamt).unwrap();
        return TransformOutcome::transformed(expr::BitvecConst::from(result))
    }
    TransformOutcome::identity(shl)
}

fn simplify_lshr(lshr: expr::LogicalShiftRight) -> TransformOutcome {
    // If the left-hand side is constant zero the entire shift-right evaluates to zero.
    if let Some(lval) = lshr.children.lhs.get_if_bitvec_const() {
        if lval.is_zero() {
            return TransformOutcome::transformed(expr::BitvecConst::zero(lval.width().into()))
        }
    }
    if let Some(rval) = lshr.children.rhs.get_if_bitvec_const() {
        let width = lshr.bitvec_ty.width();
        // If the right-hand side is constant zero the entire shift-left evaluates to the left-hand side.
        if rval.is_zero() {
            return TransformOutcome::transformed(lshr.children.lhs)
        }
        // If the right-hand side represents an invalid shift amount the result is zero.
        match rval.try_to_u32() {
            Err(_) => {
                warn!("Encountered right-hand side logical right-shift shift-amount that is larger than 2^32 in: {:?} \n\
                       Stevia handles this by returning constant zero.", lshr);
                return TransformOutcome::transformed(expr::BitvecConst::zero(lshr.bitvec_ty))
            }
            Ok(val) => {
                let shamt = ShiftAmount::from(val as usize);
                // TODO in crate apint: make ShiftAmount::to_usize public
                if shamt.to_usize() >= width.to_usize() {
                    warn!("Encountered right-hand side logical right-shift overflow with child expressions in: {:?} \n\
                           Stevia handles this by returning constant zero.", lshr);
                    return TransformOutcome::transformed(expr::BitvecConst::zero(lshr.bitvec_ty))
                }
            }
        }
    }
    // If both child expressions are constant bitvectors we can simply evaluate the result.
    if let box BinExprChildren{ lhs: AnyExpr::BitvecConst(lhs), rhs: AnyExpr::BitvecConst(rhs) } = lshr.children {
        let rval = rhs.val.try_to_u32().unwrap();
        let shamt = ShiftAmount::from(rval as usize);
        let result = lhs.val.into_checked_lshr(shamt).unwrap();
        return TransformOutcome::transformed(expr::BitvecConst::from(result))
    }
    TransformOutcome::identity(lshr)
}

fn simplify_ashr(ashr: expr::ArithmeticShiftRight) -> TransformOutcome {
    if let Some(lval) = ashr.children.lhs.get_if_bitvec_const() {
        // If the left-hand side is constant zero the entire shift-right evaluates to zero.
        if lval.is_zero() {
            return TransformOutcome::transformed(expr::BitvecConst::zero(lval.width().into()))
        }
        // If the left-hand side is constant all-bits-set the entire arithmetical shift-right
        // always evaluates to zero.
        if lval.is_all_set() {
            return TransformOutcome::transformed(expr::BitvecConst::all_set(lval.width().into()))
        }
    }
    if let Some(rval) = ashr.children.rhs.get_if_bitvec_const() {
        // If the right-hand side is constant zero the entire arithmetical shift-left evaluates to the left-hand side.
        if rval.is_zero() {
            return TransformOutcome::transformed(ashr.children.lhs)
        }
    }
    // If both child expressions are constant bitvectors we can simply evaluate the result.
    if let box BinExprChildren{ lhs: AnyExpr::BitvecConst(lhs), rhs: AnyExpr::BitvecConst(rhs) } = ashr.children {
        let rval = rhs.val.try_to_u32().unwrap();
        let shamt = ShiftAmount::from(rval as usize);
        let result = lhs.val.into_checked_ashr(shamt).unwrap();
        return TransformOutcome::transformed(expr::BitvecConst::from(result))
    }
    TransformOutcome::identity(ashr)
}

fn simplify_slt(slt: expr::SignedLessThan) -> TransformOutcome {
    // If both child expressions are constant we can compute the result.
    if let box BinExprChildren{ lhs: AnyExpr::BitvecConst(lhs), rhs: AnyExpr::BitvecConst(rhs) } = slt.children {
        let result = lhs.val.checked_slt(&rhs.val).unwrap();
        return TransformOutcome::transformed(expr::BoolConst::from(result))
    }
    TransformOutcome::identity(slt)
}

fn simplify_ult(ult: expr::UnsignedLessThan) -> TransformOutcome {
    // If both child expressions are constant we can compute the result.
    if let box BinExprChildren{ lhs: AnyExpr::BitvecConst(lhs), rhs: AnyExpr::BitvecConst(rhs) } = ult.children {
        let result = lhs.val.checked_ult(&rhs.val).unwrap();
        return TransformOutcome::transformed(expr::BoolConst::from(result))
    }
    TransformOutcome::identity(ult)
}

fn simplify_zext(zext: expr::ZeroExtend) -> TransformOutcome {
    // If the target bitwidth is equal to the current bitwidth we can simplify this to its child.
    if zext.ty() == zext.src.ty() {
        return TransformOutcome::transformed(*zext.src)
    }
    // If child expression is constant we can compute the result.
    let target_width = zext.bitvec_ty.width().raw_width();
    if let box AnyExpr::BitvecConst(child) = zext.src {
        let result = child.val.into_zero_extend(target_width).unwrap();
        return TransformOutcome::transformed(expr::BitvecConst::from(result))
    }
    TransformOutcome::identity(zext)
}

fn simplify_sext(sext: expr::SignExtend) -> TransformOutcome {
    // If the target bitwidth is equal to the current bitwidth we can simplify this to its child.
    if sext.ty() == sext.src.ty() {
        return TransformOutcome::transformed(*sext.src)
    }
    // If child expression is constant we can compute the result.
    let target_width = sext.bitvec_ty.width().raw_width();
    if let box AnyExpr::BitvecConst(child) = sext.src {
        let result = child.val.into_sign_extend(target_width).unwrap();
        return TransformOutcome::transformed(expr::BitvecConst::from(result))
    }
    TransformOutcome::identity(sext)
}

fn simplify_concat(concat: expr::Concat) -> TransformOutcome {
    // If the left-hand side is constant zero we can transform this concatenation expression
    // into an equisatisfiable zero-extend expression with the same target bit width.
    if let Some(c) = concat.children.lhs.get_if_bitvec_const() {
        if c.is_zero() {
            return TransformOutcome::transformed(
                expr::ZeroExtend::new(concat.bitvec_ty.width(), concat.children.rhs).unwrap())
        }
    }
    // If both child expressions are constant bitvectors we can simply evaluate the result.
    let target_width = concat.bitvec_ty.width();
    if let box BinExprChildren{ lhs: AnyExpr::BitvecConst(mut lhs), rhs: AnyExpr::BitvecConst(mut rhs) } = concat.children {
        lhs.val.zero_extend(target_width.raw_width()).unwrap();
        rhs.val.zero_extend(target_width.raw_width()).unwrap();
        let shamt = ShiftAmount::from(rhs.bitvec_ty.width().to_usize());
        lhs.val.checked_shl_assign(shamt).unwrap();
        lhs.val.checked_add_assign(&rhs.val).unwrap();
        return TransformOutcome::transformed(expr::BitvecConst::from(lhs.val))
    }
    TransformOutcome::identity(concat)
}

fn simplify_extract(extract: expr::Extract) -> TransformOutcome {
    // If the lo and hi range is equal to the full range this is equal to the child expression.
    if extract.ty() == extract.src.ty() {
        return TransformOutcome::transformed(*extract.src)
    }
    // If the child expression is a constant bitvector we can simply evaluate the result.
    let lo = extract.lo;
    let target_bitvec_ty = extract.bitvec_ty();
    if let box AnyExpr::BitvecConst(mut child) = extract.src {
        child.val.checked_lshr_assign(ShiftAmount::from(lo)).unwrap();
        child.val.truncate(target_bitvec_ty.width().raw_width()).unwrap();
        return TransformOutcome::transformed(expr::BitvecConst::from(child.val))
    }
    TransformOutcome::identity(extract)
}

impl Transformer for TermConstPropagator {
    fn transform_neg(&self, neg: expr::Neg) -> TransformOutcome {
        simplify_neg(neg)
    }

    fn transform_bitvec_equals(&self, bitvec_equals: expr::BitvecEquals) -> TransformOutcome {
        simplify_bitvec_equals(bitvec_equals)
    }

    fn transform_add(&self, add: expr::Add) -> TransformOutcome {
        simplify_add(add)
    }

    fn transform_sub(&self, sub: expr::Sub) -> TransformOutcome {
        simplify_sub(sub)
    }

    fn transform_mul(&self, mul: expr::Mul) -> TransformOutcome {
        simplify_mul(mul)
    }

    fn transform_udiv(&self, udiv: expr::UnsignedDiv) -> TransformOutcome {
        simplify_udiv(udiv)
    }

    fn transform_sdiv(&self, sdiv: expr::SignedDiv) -> TransformOutcome {
        simplify_sdiv(sdiv)
    }

    fn transform_urem(&self, urem: expr::UnsignedRemainder) -> TransformOutcome {
        simplify_urem(urem)
    }

    fn transform_srem(&self, srem: expr::SignedRemainder) -> TransformOutcome {
        simplify_srem(srem)
    }

    fn transform_bitnot(&self, bitnot: expr::BitNot) -> TransformOutcome {
        simplify_bitnot(bitnot)
    }

    fn transform_bitand(&self, bitand: expr::BitAnd) -> TransformOutcome {
        simplify_bitand(bitand)
    }

    fn transform_bitor(&self, bitor: expr::BitOr) -> TransformOutcome {
        simplify_bitor(bitor)
    }

    fn transform_bitxor(&self, bitxor: expr::BitXor) -> TransformOutcome {
        simplify_bitxor(bitxor)
    }

    fn transform_shl(&self, shl: expr::ShiftLeft) -> TransformOutcome {
        simplify_shl(shl)
    }

    fn transform_lshr(&self, lshr: expr::LogicalShiftRight) -> TransformOutcome {
        simplify_lshr(lshr)
    }

    fn transform_ashr(&self, ashr: expr::ArithmeticShiftRight) -> TransformOutcome {
        simplify_ashr(ashr)
    }

    fn transform_slt(&self, slt: expr::SignedLessThan) -> TransformOutcome {
        simplify_slt(slt)
    }

    fn transform_ult(&self, ult: expr::UnsignedLessThan) -> TransformOutcome {
        simplify_ult(ult)
    }

    fn transform_zext(&self, sext: expr::ZeroExtend) -> TransformOutcome {
        simplify_zext(sext)
    }

    fn transform_sext(&self, sext: expr::SignExtend) -> TransformOutcome {
        simplify_sext(sext)
    }

    fn transform_concat(&self, concat: expr::Concat) -> TransformOutcome {
        simplify_concat(concat)
    }

    fn transform_extract(&self, extract: expr::Extract) -> TransformOutcome {
        simplify_extract(extract)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplifier::prelude::*;

    modular_ast_transformer! {
        struct TermConstPropagatorTransformer {
            _0: TermConstPropagator
        }
    }
    type TermConstPropagatorSimplifier = BaseSimplifier<TermConstPropagatorTransformer>;

    fn create_simplifier() -> TermConstPropagatorSimplifier {
        TermConstPropagatorSimplifier::default()
    }

    fn simplify(expr: &mut AnyExpr) -> TransformEffect {
        create_simplifier().simplify(expr)
    }

    fn assert_simplified<E1, E2>(input: E1, expected: E2)
        where E1: IntoAnyExprOrError,
              E2: IntoAnyExprOrError
    {
        let mut input = input.into_any_expr_or_error().unwrap();
        let expected = expected.into_any_expr_or_error().unwrap();
        simplify(&mut input);
        assert_eq!(input, expected);
    }

    fn new_builder() -> PlainExprTreeBuilder {
        PlainExprTreeBuilder::default()
    }

    mod neg {
        use super::*;

        #[test]
        fn simple() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_neg(b.bitvec_const(BitvecTy::w32(), 42)),
                b.bitvec_const(BitvecTy::w32(), -42)
            )
        }
    }

    mod bitnot {
        use super::*;

        #[test]
        fn simple() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_not(b.bitvec_const(BitvecTy::w8(), 0b0110_1100_u8)),
                b.bitvec_const(BitvecTy::w8(), 0b1001_0011_u8)
            )
        }
    }

    mod bitvec_equals {
        use super::*;

        #[test]
        fn all_const_equal() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_equals_n(vec![
                    b.bitvec_const(BitvecTy::w32(), 5),
                    b.bitvec_const(BitvecTy::w32(), 5),
                    b.bitvec_const(BitvecTy::w32(), 5)
                ]),
                b.bool_const(true)
            )
        }

        #[test]
        fn all_unequal() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_equals(
                    b.bitvec_const(BitvecTy::w32(), 5),
                    b.bitvec_const(BitvecTy::w32(), 7)
                ),
                b.bool_const(false)
            )
        }

        #[test]
        fn some_unequal() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_equals_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 42),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 1337),
                    b.bitvec_var(BitvecTy::w32(), "z")
                ]),
                b.bool_const(false)
            )
        }

        #[test]
        fn some_equal_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_equals_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 42),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 42),
                    b.bitvec_var(BitvecTy::w32(), "z")
                ]),
                b.bitvec_equals_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_var(BitvecTy::w32(), "z"),
                    b.bitvec_const(BitvecTy::w32(), 42) // reinserted at the end
                ])
            )
        }
    }

    mod add {
        use super::*;

        #[test]
        fn all_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_add_n(vec![
                    b.bitvec_const(BitvecTy::w32(), 5),
                    b.bitvec_const(BitvecTy::w32(), 7),
                    b.bitvec_const(BitvecTy::w32(), 3)
                ]),
                b.bitvec_const(BitvecTy::w32(), 15)
            )
        }

        #[test]
        fn some_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_add_n(vec![
                    b.bitvec_const(BitvecTy::w32(), 1337),
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 42)
                ]),
                b.bitvec_add(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 1379) // swapped since pushed back
                )
            )
        }

        #[test]
        fn some_const_with_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_add_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 42)
                ]),
                b.bitvec_add_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 42)
                ])
            )
        }

        #[test]
        fn binary_with_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_add_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0),
                ]),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        }

        #[test]
        fn eliminate_zeros() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_add_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 0)
                ]),
                b.bitvec_add(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                )
            )
        }
    }

    mod sub {
        use super::*;

        #[test]
        fn both_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_sub(
                    b.bitvec_const(BitvecTy::w32(), 12),
                    b.bitvec_const(BitvecTy::w32(), 5)
                ),
                b.bitvec_const(BitvecTy::w32(), 7)
            )
        }

        #[test]
        fn lhs_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_sub(
                    b.bitvec_const(BitvecTy::w32(), 0),
                    b.bitvec_var(BitvecTy::w32(), "x")
                ),
                b.bitvec_neg(b.bitvec_var(BitvecTy::w32(), "x"))
            )
        }

        #[test]
        fn rhs_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_sub(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0)
                ),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        }
    }

    mod mul {
        use super::*;

        #[test]
        fn identify_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_mul_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0),
                    b.bitvec_var(BitvecTy::w32(), "y")
                ]),
                b.bitvec_const(BitvecTy::w32(), 0)
            )
        }

        #[test]
        fn identify_zero_with_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_mul_n(vec![
                    b.bitvec_const(BitvecTy::w32(), 42),
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0)
                ]),
                b.bitvec_const(BitvecTy::w32(), 0)
            )
        }

        #[test]
        fn binary_with_one() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_mul_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 1),
                ]),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        }

        #[test]
        fn eliminate_ones() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_mul_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 1),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 1)
                ]),
                b.bitvec_mul(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                )
            )
        }

        #[test]
        fn all_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_mul_n(vec![
                    b.bitvec_const(BitvecTy::w32(), 5),
                    b.bitvec_const(BitvecTy::w32(), 7),
                    b.bitvec_const(BitvecTy::w32(), 3)
                ]),
                b.bitvec_const(BitvecTy::w32(), 105)
            )
        }

        #[test]
        fn some_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_mul_n(vec![
                    b.bitvec_const(BitvecTy::w32(), 11),
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 7)
                ]),
                b.bitvec_mul(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 77) // swapped since pushed back
                )
            )
        }

        #[test]
        fn some_const_with_one() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_mul_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 1),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 42)
                ]),
                b.bitvec_mul_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 42)
                ])
            )
        }
    }

    macro_rules! div_test_impls {
        ($name:ident, $bitvec_div:ident) => {
            #[test]
            fn division_by_zero() {
                let b = new_builder();
                assert_simplified(
                    b.$bitvec_div(
                        b.bitvec_var(BitvecTy::w32(), "x"),
                        b.bitvec_const(BitvecTy::w32(), 0)
                    ),
                    b.bitvec_var(BitvecTy::w32(), "x")
                )
            }

            #[test]
            fn division_by_one() {
                let b = new_builder();
                assert_simplified(
                    b.$bitvec_div(
                        b.bitvec_var(BitvecTy::w32(), "x"),
                        b.bitvec_const(BitvecTy::w32(), 1)
                    ),
                    b.bitvec_var(BitvecTy::w32(), "x")
                )
            }

            #[test]
            fn lhs_is_zero() {
                let b = new_builder();
                assert_simplified(
                    b.$bitvec_div(
                        b.bitvec_const(BitvecTy::w32(), 0),
                        b.bitvec_var(BitvecTy::w32(), "x")
                    ),
                    b.bitvec_const(BitvecTy::w32(), 0)
                )
            }

            #[test]
            fn both_const() {
                fn test_for(lhs: u32, rhs: u32, result: u32) {
                    let b = new_builder();
                    assert_simplified(
                        b.$bitvec_div(
                            b.bitvec_const(BitvecTy::w32(), lhs),
                            b.bitvec_const(BitvecTy::w32(), rhs)
                        ),
                        b.bitvec_const(BitvecTy::w32(), result)
                    )
                }
                test_for(35, 7, 5);
                test_for(41, 3, 13);
            }
        };
    }

    mod udiv {
        use super::*;

        div_test_impls!(udiv, bitvec_udiv);
    }

    mod sdiv {
        use super::*;

        div_test_impls!(sdiv, bitvec_sdiv);
    }

    macro_rules! rem_test_impls {
        ($name:ident, $bitvec_div:ident) => {
            #[test]
            fn division_by_zero() {
                let b = new_builder();
                assert_simplified(
                    b.$bitvec_div(
                        b.bitvec_var(BitvecTy::w32(), "x"),
                        b.bitvec_const(BitvecTy::w32(), 0)
                    ),
                    b.bitvec_var(BitvecTy::w32(), "x")
                )
            }

            #[test]
            fn rhs_is_one() {
                let b = new_builder();
                assert_simplified(
                    b.$bitvec_div(
                        b.bitvec_var(BitvecTy::w32(), "x"),
                        b.bitvec_const(BitvecTy::w32(), 1)
                    ),
                    b.bitvec_const(BitvecTy::w32(), 0)
                )
            }

            #[test]
            fn lhs_is_zero() {
                let b = new_builder();
                assert_simplified(
                    b.$bitvec_div(
                        b.bitvec_const(BitvecTy::w32(), 0),
                        b.bitvec_var(BitvecTy::w32(), "x")
                    ),
                    b.bitvec_const(BitvecTy::w32(), 0)
                )
            }

            #[test]
            fn both_const() {
                fn test_for(lhs: u32, rhs: u32, result: u32) {
                    let b = new_builder();
                    assert_simplified(
                        b.$bitvec_div(
                            b.bitvec_const(BitvecTy::w32(), lhs),
                            b.bitvec_const(BitvecTy::w32(), rhs)
                        ),
                        b.bitvec_const(BitvecTy::w32(), result)
                    )
                }
                test_for(35, 7, 0);
                test_for(41, 3, 2);
            }
        };
    }

    mod urem {
        use super::*;

        rem_test_impls!(urem, bitvec_urem);
    }

    mod srem {
        use super::*;

        rem_test_impls!(srem, bitvec_srem);
    }

    mod shl {
        use super::*;

        #[test]
        fn both_const() {
            fn test_for(lhs: i32, rhs: u32) {
                let b = new_builder();
                assert_simplified(
                    b.bitvec_shl(
                        b.bitvec_const(BitvecTy::w32(), lhs),
                        b.bitvec_const(BitvecTy::w32(), rhs)
                    ),
                    b.bitvec_const(BitvecTy::w32(), lhs.wrapping_shl(rhs))
                )
            }
            test_for(1, 10);
            test_for(-1, 10);
            test_for(i32::max_value(), 2);
            test_for(42, 5);
            test_for(3, 3);
        }

        #[test]
        fn lhs_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_shl(
                    b.bitvec_const(BitvecTy::w32(), 0),
                    b.bitvec_var(BitvecTy::w32(), "x")
                ),
                b.bitvec_const(BitvecTy::w32(), 0)
            )
        }

        #[test]
        fn rhs_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_shl(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0)
                ),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        }

        #[test]
        fn rhs_overflow() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_shl(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 33)
                ),
                b.bitvec_const(BitvecTy::w32(), 0)
            )
        }

        #[test]
        fn rhs_too_large_for_u32() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_shl(
                    b.bitvec_var(BitvecTy::w64(), "x_w64"),
                    b.bitvec_const(BitvecTy::w64(), u64::max_value() / 2)
                ),
                b.bitvec_const(BitvecTy::w64(), 0_u64)
            )
        }
    }

    mod lshr {
        use super::*;

        #[test]
        fn both_const() {
            fn test_for(lhs: u32, rhs: u32) {
                let b = new_builder();
                assert_simplified(
                    b.bitvec_lshr(
                        b.bitvec_const(BitvecTy::w32(), lhs),
                        b.bitvec_const(BitvecTy::w32(), rhs)
                    ),
                    b.bitvec_const(BitvecTy::w32(), lhs.wrapping_shr(rhs))
                )
            }
            test_for(1, 10);
            test_for(1337, 6);
            test_for(-1_i32 as u32, 10);
            test_for(u32::max_value(), 2); 
            test_for(42, 5);
            test_for(3, 3);
        }

        #[test]
        fn lhs_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_lshr(
                    b.bitvec_const(BitvecTy::w32(), 0),
                    b.bitvec_var(BitvecTy::w32(), "x")
                ),
                b.bitvec_const(BitvecTy::w32(), 0)
            )
        }

        #[test]
        fn rhs_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_lshr(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0)
                ),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        }

        #[test]
        fn rhs_overflow() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_lshr(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 33)
                ),
                b.bitvec_const(BitvecTy::w32(), 0)
            )
        }

        #[test]
        fn rhs_too_large_for_u32() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_lshr(
                    b.bitvec_var(BitvecTy::w64(), "x_w64"),
                    b.bitvec_const(BitvecTy::w64(), u64::max_value() / 2)
                ),
                b.bitvec_const(BitvecTy::w64(), 0_u64)
            )
        }
    }

    mod ashr {
        use super::*;

        #[test]
        fn both_const() {
            fn test_for(lhs: i32, rhs: u32) {
                let b = new_builder();
                assert_simplified(
                    b.bitvec_ashr(
                        b.bitvec_const(BitvecTy::w32(), lhs),
                        b.bitvec_const(BitvecTy::w32(), rhs)
                    ),
                    b.bitvec_const(BitvecTy::w32(), lhs.wrapping_shr(rhs))
                )
            }
            test_for(1, 10);
            test_for(1337, 6);
            test_for(-1, 10);
            test_for(i32::max_value(), 2);
            test_for(-8, 2);
            test_for(-42, 5);
            test_for(-3, 3);
        }

        #[test]
        fn lhs_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_ashr(
                    b.bitvec_const(BitvecTy::w32(), 0),
                    b.bitvec_var(BitvecTy::w32(), "x")
                ),
                b.bitvec_const(BitvecTy::w32(), 0)
            )
        }

        #[test]
        fn lhs_all_set() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_ashr(
                    b.bitvec_const(BitvecTy::w32(), 0x_FFFF_FFFF_u32),
                    b.bitvec_var(BitvecTy::w32(), "x")
                ),
                b.bitvec_const(BitvecTy::w32(), 0x_FFFF_FFFF_u32)
            )
        }

        #[test]
        fn rhs_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_ashr(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0)
                ),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        }

    }

    mod slt {
        use super::*;

        #[test]
        fn both_const() {
            fn test_for(lhs: i32, rhs: i32) {
                let b = new_builder();
                assert_simplified(
                    b.bitvec_slt(
                        b.bitvec_const(BitvecTy::w32(), lhs),
                        b.bitvec_const(BitvecTy::w32(), rhs),
                    ),
                    b.bool_const(lhs < rhs)
                )
            }
            test_for(0, 1337);
            test_for(15, 16);
            test_for(15, -16);
            test_for(42, 41);
            test_for(7, 7);
            test_for(-1, 0);
            test_for(10, -10);
        }
    }

    mod ult {
        use super::*;

        #[test]
        fn both_const() {
            fn test_for(lhs: u32, rhs: u32) {
                let b = new_builder();
                assert_simplified(
                    b.bitvec_ult(
                        b.bitvec_const(BitvecTy::w32(), lhs),
                        b.bitvec_const(BitvecTy::w32(), rhs),
                    ),
                    b.bool_const(lhs < rhs)
                )
            }
            test_for(0, 1337);
            test_for(15, 16);
            test_for(42, 41);
            test_for(7, 7);
        }
    }

    mod bitand {
        use super::*;

        #[test]
        fn identify_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_and_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0),
                    b.bitvec_var(BitvecTy::w32(), "y")
                ]),
                b.bitvec_const(BitvecTy::w32(), 0)
            )
        }

        #[test]
        fn identify_zero_with_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_and_n(vec![
                    b.bitvec_const(BitvecTy::w32(), 42),
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0)
                ]),
                b.bitvec_const(BitvecTy::w32(), 0)
            )
        }

        #[test]
        fn binary_with_all_set() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_and_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0xFFFF_FFFF_u32),
                ]),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        }

        #[test]
        fn eliminate_all_set() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_and_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0xFFFF_FFFF_u32),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 0xFFFF_FFFF_u32)
                ]),
                b.bitvec_and(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                )
            )
        }

        #[test]
        fn all_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_and_n(vec![
                    b.bitvec_const(BitvecTy::w16(), 0b_0001_0010_0100_1000_u16),
                    b.bitvec_const(BitvecTy::w16(), 0b_0011_0110_1100_0011_u16),
                    b.bitvec_const(BitvecTy::w16(), 0b_1111_1111_0000_0000_u16)
                ]),
                b.bitvec_const(BitvecTy::w16(), 0b_0001_0010_0000_0000_u16)
            )
        }

        #[test]
        fn some_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_and_n(vec![
                    b.bitvec_const(BitvecTy::w16(), 0b_1110_1101_1011_0111_u16),
                    b.bitvec_var(BitvecTy::w16(), "x_w16"), // FIXME: we want an own symbol store per test
                    b.bitvec_const(BitvecTy::w16(), 0b_0110_0110_0110_0110_u16)
                ]),
                b.bitvec_and(
                    b.bitvec_var(BitvecTy::w16(), "x_w16"), // FIXME: we want an own symbol store per test
                    b.bitvec_const(BitvecTy::w16(), 0b_0110_0100_0010_0110_u16) // swapped since pushed back
                )
            )
        }

        #[test]
        fn some_const_with_all_set() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_and_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0xFFFF_FFFF_u32),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 42)
                ]),
                b.bitvec_and_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 42)
                ])
            )
        }
    }

    mod bitor {
        use super::*;

        #[test]
        fn identify_all_set() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_or_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0xFFFF_FFFF_u32),
                    b.bitvec_var(BitvecTy::w32(), "y")
                ]),
                b.bitvec_const(BitvecTy::w32(), 0xFFFF_FFFF_u32)
            )
        }

        #[test]
        fn identify_all_set_with_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_or_n(vec![
                    b.bitvec_const(BitvecTy::w32(), 42),
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0xFFFF_FFFF_u32)
                ]),
                b.bitvec_const(BitvecTy::w32(), 0xFFFF_FFFF_u32)
            )
        }

        #[test]
        fn binary_with_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_or_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0),
                ]),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        }

        #[test]
        fn eliminate_zeros() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_or_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 0)
                ]),
                b.bitvec_or(
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                )
            )
        }

        #[test]
        fn all_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_or_n(vec![
                    b.bitvec_const(BitvecTy::w16(), 0b_0001_0010_0100_1000_u16),
                    b.bitvec_const(BitvecTy::w16(), 0b_0011_0110_1100_0011_u16),
                    b.bitvec_const(BitvecTy::w16(), 0b_1011_1011_0000_0000_u16)
                ]),
                b.bitvec_const(BitvecTy::w16(), 0b_1011_1111_1100_1011_u16)
            )
        }

        #[test]
        fn some_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_or_n(vec![
                    b.bitvec_const(BitvecTy::w16(), 0b_1110_1101_1011_0111_u16),
                    b.bitvec_var(BitvecTy::w16(), "x_w16"), // FIXME: we want an own symbol store per test
                    b.bitvec_const(BitvecTy::w16(), 0b_0110_0100_0110_0110_u16)
                ]),
                b.bitvec_or(
                    b.bitvec_var(BitvecTy::w16(), "x_w16"), // FIXME: we want an own symbol store per test
                    b.bitvec_const(BitvecTy::w16(), 0b_1110_1101_1111_0111_u16) // swapped since pushed back
                )
            )
        }

        #[test]
        fn some_const_with_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_or_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_const(BitvecTy::w32(), 0),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 42)
                ]),
                b.bitvec_or_n(vec![
                    b.bitvec_var(BitvecTy::w32(), "x"),
                    b.bitvec_var(BitvecTy::w32(), "y"),
                    b.bitvec_const(BitvecTy::w32(), 42)
                ])
            )
        }
    }

    mod bitxor {
        use super::*;

        #[test]
        fn both_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_xor(
                    b.bitvec_const(BitvecTy::w16(), 0b_1011_1001_1010_1111_u16),
                    b.bitvec_const(BitvecTy::w16(), 0b_1001_0111_0101_1100_u16)
                ),
                b.bitvec_const(BitvecTy::w16(), 0b_0010_1110_1111_0011_u16)
            )
        }

        #[test]
        fn lhs_or_rhs_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_xor(
                    b.bitvec_const(BitvecTy::w16(), 0_u16),
                    b.bitvec_var(BitvecTy::w16(), "x_w16")
                ),
                b.bitvec_var(BitvecTy::w16(), "x_w16")
            );
            assert_simplified(
                b.bitvec_xor(
                    b.bitvec_var(BitvecTy::w16(), "x_w16"),
                    b.bitvec_const(BitvecTy::w16(), 0_u16)
                ),
                b.bitvec_var(BitvecTy::w16(), "x_w16")
            )
        }

        #[test]
        fn lhs_or_rhs_all_set() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_xor(
                    b.bitvec_const(BitvecTy::w16(), 0x_FFFF_u16),
                    b.bitvec_var(BitvecTy::w16(), "x_w16")
                ),
                b.bitvec_not(b.bitvec_var(BitvecTy::w16(), "x_w16"))
            );
            assert_simplified(
                b.bitvec_xor(
                    b.bitvec_var(BitvecTy::w16(), "x_w16"),
                    b.bitvec_const(BitvecTy::w16(), 0x_FFFF_u16)
                ),
                b.bitvec_not(b.bitvec_var(BitvecTy::w16(), "x_w16"))
            )
        }
    }

    mod zext {
        use super::*;

        #[test]
        fn const_child() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_zext(
                    BitWidth::w64(),
                    b.bitvec_const(BitvecTy::w32(), 42)
                ),
                b.bitvec_const(BitvecTy::w64(), 42_u64)
            )
        }

        #[test]
        fn same_width() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_zext(
                    BitWidth::w32(),
                    b.bitvec_var(BitvecTy::w32(), "x")
                ),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        }
    }

    mod sext {
        use super::*;

        #[test]
        fn const_child() {
            fn test_for(val: i32) {
                let b = new_builder();
                assert_simplified(
                    b.bitvec_sext(
                        BitWidth::w64(),
                        b.bitvec_const(BitvecTy::w32(), val)
                    ),
                    b.bitvec_const(BitvecTy::w64(), val as i64)
                )
            }
            test_for(42);
            // test_for(-1337); // TODO in crate apint: fix bug
            // test_for(-1);    // TODO in crate apint: fix bug
            test_for(0);
        }

        #[test]
        fn same_width() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_sext(
                    BitWidth::w32(),
                    b.bitvec_var(BitvecTy::w32(), "x")
                ),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        }
    }

    mod concat {
        use super::*;

        #[test]
        fn lhs_zero() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_concat(
                    b.bitvec_const(BitvecTy::w32(), 0),
                    b.bitvec_var(BitvecTy::w32(), "x")
                ),
                b.bitvec_zext(
                    BitWidth::w64(),
                    b.bitvec_var(BitvecTy::w32(), "x")
                )
            )
        }

        #[test]
        fn both_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_concat(
                    b.bitvec_const(BitvecTy::w16(), 0x_ABCD_u16),
                    b.bitvec_const(BitvecTy::w16(), 0x_EF01_u16)
                ),
                b.bitvec_const(BitvecTy::w32(), 0x_ABCD_EF01_u32)
            )
        }
    }

    mod extract {
        use super::*;

        #[test]
        fn same_target_width() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_extract_hi_lo(
                    32, // hi
                    0,  // lo
                    b.bitvec_var(BitvecTy::w32(), "x")
                ),
                b.bitvec_var(BitvecTy::w32(), "x")
            )
        }

        #[test]
        fn both_const() {
            let b = new_builder();
            assert_simplified(
                b.bitvec_extract_hi_lo(
                    32, // hi
                    16, // lo
                    b.bitvec_const(BitvecTy::w32(), 0x_ABCD_EF01_u32)
                ),
                b.bitvec_const(BitvecTy::w16(), 0x_ABCD_u16)
            )
        }
    }
}
