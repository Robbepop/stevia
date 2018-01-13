use ast2::*;

use std::result;

pub mod prelude {
    pub use super::{
        PlainExprTreeFactory,
        PlainExprTreeBuilder
    };
}

type Result<T> = result::Result<T, String>;

pub type PlainExprTreeBuilder = ExprTreeBuilder<PlainExprTreeFactory>;

impl Default for PlainExprTreeBuilder {
    fn default() -> Self {
        ExprTreeBuilder::new(PlainExprTreeFactory)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct PlainExprTreeFactory;

impl ExprTreeFactory for PlainExprTreeFactory {
    fn cond(self, cond: AnyExpr, then_case: AnyExpr, else_case: AnyExpr) -> Result<AnyExpr> {
		expr::IfThenElse::new(cond, then_case, else_case).map(AnyExpr::from)
	}

    fn bool_var<S>(self, name: S) -> Result<AnyExpr>
        where S: Into<String> + AsRef<str>
    {
        expr::Symbol::new(name, Type::Bool).map(AnyExpr::from)
    }

    fn bitvec_var<S>(self, ty: BitvecTy, name: S) -> Result<AnyExpr>
        where S: Into<String> + AsRef<str>
    {
        expr::Symbol::new(name, ty.ty()).map(AnyExpr::from)
    }

    fn array_var<S>(self, ty: ArrayTy, name: S) -> Result<AnyExpr>
        where S: Into<String> + AsRef<str>
    {
        expr::Symbol::new(name, ty.ty()).map(AnyExpr::from)
    }

    fn bool_const(self, val: bool) -> Result<AnyExpr> {
		Ok(AnyExpr::from(expr::BoolConst::from(val)))
	}

    fn and(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		expr::And::binary(lhs, rhs).map(AnyExpr::from)
	}

    fn and_n(self, childs: Vec<AnyExpr>) -> Result<AnyExpr> {
		expr::And::nary(childs).map(AnyExpr::from)
	}

    fn bool_equals(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		expr::BoolEquals::binary(lhs, rhs).map(AnyExpr::from)
	}

    fn bool_equals_n(self, childs: Vec<AnyExpr>) -> Result<AnyExpr> {
		expr::BoolEquals::nary(childs).map(AnyExpr::from)
	}

    fn implies(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		expr::Implies::new(lhs, rhs).map(AnyExpr::from)
	}

    fn not(self, inner: AnyExpr) -> Result<AnyExpr> {
		expr::Not::new(inner).map(AnyExpr::from)
	}

    fn or(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		expr::Or::binary(lhs, rhs).map(AnyExpr::from)
	}

    fn or_n(self, childs: Vec<AnyExpr>) -> Result<AnyExpr> {
		expr::Or::nary(childs).map(AnyExpr::from)
	}

    fn xor(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		expr::Xor::new(lhs, rhs).map(AnyExpr::from)
	}

    fn array_equals(self, _lhs: AnyExpr, _rhs: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn array_equals_n(self, _childs: Vec<AnyExpr>) -> Result<AnyExpr> {
		unimplemented!()
	}
    
    fn array_read(self, _array: AnyExpr, _index: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}
    
    fn array_write(self, _array: AnyExpr, _index: AnyExpr, _value: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_const<V>(self, _ty: BitvecTy, _value: V) -> Result<AnyExpr>
        where V: Into<expr::BitvecConst>
    {
		unimplemented!()
    }

    fn bitvec_neg(self, inner: AnyExpr) -> Result<AnyExpr> {
		expr::Neg::new_infer(inner).map(AnyExpr::from)
	}

    fn bitvec_add(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		expr::Add::binary_infer(lhs, rhs).map(AnyExpr::from)
	}

    fn bitvec_add_n(self, _childs: Vec<AnyExpr>) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_sub(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		expr::Sub::new_infer(lhs, rhs).map(AnyExpr::from)
	}

    fn bitvec_mul(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		expr::Mul::binary_infer(lhs, rhs).map(AnyExpr::from)
	}

    fn bitvec_mul_n(self, _childs: Vec<AnyExpr>) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_sdiv(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		expr::SignedDiv::new_infer(lhs, rhs).map(AnyExpr::from)
	}

    fn bitvec_smod(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		expr::SignedModulo::new_infer(lhs, rhs).map(AnyExpr::from)
	}

    fn bitvec_srem(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		expr::SignedRemainder::new_infer(lhs, rhs).map(AnyExpr::from)
	}

    fn bitvec_udiv(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		expr::UnsignedDiv::new_infer(lhs, rhs).map(AnyExpr::from)
	}

    fn bitvec_urem(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		expr::UnsignedRemainder::new_infer(lhs, rhs).map(AnyExpr::from)
	}

    fn bitvec_not(self, inner: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_and(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_and_n(self, childs: Vec<AnyExpr>) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_or(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_or_n(self, childs: Vec<AnyExpr>) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_xor(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_concat(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_extract_hi_lo(self, hi: usize, lo: usize, inner: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_sext(self, target_width: BitWidth, inner: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_zext(self, target_width: BitWidth, inner: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_sge(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_sgt(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_sle(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_slt(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_uge(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_ugt(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_ule(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}

    fn bitvec_ult(self, lhs: AnyExpr, rhs: AnyExpr) -> Result<AnyExpr> {
		unimplemented!()
	}
}