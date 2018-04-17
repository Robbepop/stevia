use ast::*;

pub type PlainExprTreeBuilder = ExprTreeBuilder<PlainExprTreeFactory>;

impl Default for PlainExprTreeBuilder {
	fn default() -> Self {
		ExprTreeBuilder::new(PlainExprTreeFactory)
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct PlainExprTreeFactory;

impl ExprTreeFactory for PlainExprTreeFactory {
	fn cond(&self, cond: AnyExpr, then_case: AnyExpr, else_case: AnyExpr) -> ExprResult<AnyExpr> {
		expr::IfThenElse::new(cond, then_case, else_case).map(AnyExpr::from)
	}

	fn bool_var<S>(&self, name: S) -> ExprResult<AnyExpr>
	where
		S: Into<String> + AsRef<str>,
	{
		expr::Symbol::new(name, Type::Bool).map(AnyExpr::from)
	}

	fn bitvec_var<S>(&self, ty: BitvecTy, name: S) -> ExprResult<AnyExpr>
	where
		S: Into<String> + AsRef<str>,
	{
		expr::Symbol::new(name, ty.ty()).map(AnyExpr::from)
	}

	fn array_var<S>(&self, ty: ArrayTy, name: S) -> ExprResult<AnyExpr>
	where
		S: Into<String> + AsRef<str>,
	{
		expr::Symbol::new(name, ty.ty()).map(AnyExpr::from)
	}

	fn bool_const(&self, val: bool) -> ExprResult<AnyExpr> {
		Ok(AnyExpr::from(expr::BoolConst::from(val)))
	}

	fn and(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::And::binary(lhs, rhs).map(AnyExpr::from)
	}

	fn and_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr> {
		expr::And::nary(children).map(AnyExpr::from)
	}

	fn bool_equals(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::BoolEquals::binary(lhs, rhs).map(AnyExpr::from)
	}

	fn bool_equals_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr> {
		expr::BoolEquals::nary(children).map(AnyExpr::from)
	}

	fn implies(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::Implies::new(lhs, rhs).map(AnyExpr::from)
	}

	fn not(&self, inner: AnyExpr) -> ExprResult<AnyExpr> {
		expr::Not::new(inner).map(AnyExpr::from)
	}

	fn or(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::Or::binary(lhs, rhs).map(AnyExpr::from)
	}

	fn or_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr> {
		expr::Or::nary(children).map(AnyExpr::from)
	}

	fn xor(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::Xor::new(lhs, rhs).map(AnyExpr::from)
	}

	fn array_read(&self, array: AnyExpr, index: AnyExpr) -> ExprResult<AnyExpr> {
		expr::ArrayRead::new(array, index).map(AnyExpr::from)
	}

	fn array_write(&self, array: AnyExpr, index: AnyExpr, value: AnyExpr) -> ExprResult<AnyExpr> {
		expr::ArrayWrite::new(array, index, value).map(AnyExpr::from)
	}

	fn bitvec_equals(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::BitvecEquals::binary(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_equals_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr> {
		expr::BitvecEquals::nary(children).map(AnyExpr::from)
	}

	fn bitvec_const<V>(&self, ty: BitvecTy, value: V) -> ExprResult<AnyExpr>
	where
		V: Into<expr::BitvecConst>,
	{
		let result = AnyExpr::from(value.into());
		expect_concrete_bitvec_ty(&result, ty).map_err(|e| {
			e.context(format!(
			"Encountered incompatible bitwidth of {:?} upon construction of a new BitvecConst expression: {:?}",
			ty, result))
		})?;
		Ok(result)
	}

	fn bitvec_neg(&self, inner: AnyExpr) -> ExprResult<AnyExpr> {
		expr::Neg::new(inner).map(AnyExpr::from)
	}

	fn bitvec_add(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::Add::binary(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_add_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr> {
		expr::Add::nary(children).map(AnyExpr::from)
	}

	fn bitvec_sub(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::Sub::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_mul(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::Mul::binary(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_mul_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr> {
		expr::Mul::nary(children).map(AnyExpr::from)
	}

	fn bitvec_sdiv(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::SignedDiv::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_smod(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::SignedModulo::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_srem(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::SignedRemainder::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_udiv(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::UnsignedDiv::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_urem(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::UnsignedRemainder::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_not(&self, inner: AnyExpr) -> ExprResult<AnyExpr> {
		expr::BitNot::new(inner).map(AnyExpr::from)
	}

	fn bitvec_and(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::BitAnd::binary(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_and_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr> {
		expr::BitAnd::nary(children).map(AnyExpr::from)
	}

	fn bitvec_or(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::BitOr::binary(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_or_n(&self, children: Vec<AnyExpr>) -> ExprResult<AnyExpr> {
		expr::BitOr::nary(children).map(AnyExpr::from)
	}

	fn bitvec_xor(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::BitXor::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_concat(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::Concat::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_extract_hi_lo(&self, hi: usize, lo: usize, inner: AnyExpr) -> ExprResult<AnyExpr> {
		expr::Extract::new(inner, hi, lo).map(AnyExpr::from)
	}

	fn bitvec_sext(&self, target_width: BitWidth, inner: AnyExpr) -> ExprResult<AnyExpr> {
		expr::SignExtend::new(target_width, inner).map(AnyExpr::from)
	}

	fn bitvec_zext(&self, target_width: BitWidth, inner: AnyExpr) -> ExprResult<AnyExpr> {
		expr::ZeroExtend::new(target_width, inner).map(AnyExpr::from)
	}

	fn bitvec_sge(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::SignedGreaterEquals::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_sgt(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::SignedGreaterThan::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_sle(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::SignedLessEquals::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_slt(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::SignedLessThan::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_uge(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::UnsignedGreaterEquals::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_ugt(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::UnsignedGreaterThan::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_ule(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::UnsignedLessEquals::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_ult(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::UnsignedLessThan::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_ashr(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::ArithmeticShiftRight::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_lshr(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::LogicalShiftRight::new(lhs, rhs).map(AnyExpr::from)
	}

	fn bitvec_shl(&self, lhs: AnyExpr, rhs: AnyExpr) -> ExprResult<AnyExpr> {
		expr::ShiftLeft::new(lhs, rhs).map(AnyExpr::from)
	}
}
