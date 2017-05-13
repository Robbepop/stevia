use ast::prelude::*;
use ast::expr::*;
use ast::P;

/// Four main traits that all build up on each other.
/// 
/// Implementors only need to implement `TransformerImpl`
/// in order to make all other traits automatically just work out of the box.
/// 
/// The four traits and their responsibilities are:
/// 
/// - RecursiveTransformer
///     - fn recursive_transform(&mut RecursiveTransformer, expr: Expr) -> Expr;
///       Calls `recursive_transform_*` for the correct `ExprKind`.
///       Gets auto implemented for all types that implement `RecursiveTransformerImpl`.
/// 
/// - RecursiveTransformerImpl
///     - fn recursive_transform_add(&mut RecursiveTransformerImpl, expr: Add) -> Expr;
///       fn recursive_transform_mul(&mut RecursiveTransformerImpl, expr: Mul) -> Expr;
///       etc. ...
///       Calls `transform` and recursively calls it for the expression's children.
///       Gets auto implemented for all types that implement `Transformer`.
///       This is done so complicated since every `Expr` has to be transformed in a certain way
///       that cannot be easily generalized.
/// 
/// - Transformer
///     - fn transform(&mut Transformer: expr: Expr) -> Expr;
///       Calls `transform_*` for the correct `ExprKind`.
///       Gets auto implemented for all types that implement `TransformerImpl`.
/// 
/// - TransformerImpl
///     - fn transform_add(&mut TransformerImpl, expr: Add) -> Expr;
///       fn transform_mul(&mut TransformerImpl, expr: Mul) -> Expr;
/// 

pub trait TransformerImpl: Sized {
	fn transform_bvconst(&mut self, expr: BitVecConst) -> Expr;
	fn transform_bvneg(&mut self, expr: Neg) -> Expr;
	fn transform_bvadd(&mut self, expr: Add) -> Expr;
	fn transform_bvmul(&mut self, expr: Mul) -> Expr;
	fn transform_bvsub(&mut self, expr: Sub) -> Expr;
	fn transform_bvudiv(&mut self, expr: Div) -> Expr;
	fn transform_bvumod(&mut self, expr: Mod) -> Expr;
	fn transform_bvsdiv(&mut self, expr: SignedDiv) -> Expr;
	fn transform_bvsmod(&mut self, expr: SignedMod) -> Expr;
	fn transform_bvsrem(&mut self, expr: SignedRem) -> Expr;

	fn transform_bvnot(&mut self, expr: BitNot) -> Expr;
	fn transform_bvand(&mut self, expr: BitAnd) -> Expr;
	fn transform_bvor(&mut self, expr: BitOr) -> Expr;
	fn transform_bvxor(&mut self, expr: BitXor) -> Expr;
	fn transform_bvnand(&mut self, expr: BitNand) -> Expr;
	fn transform_bvnor(&mut self, expr: BitNor) -> Expr;
	fn transform_bvxnor(&mut self, expr: BitXnor) -> Expr;

	fn transform_bvult(&mut self, expr: Lt) -> Expr;
	fn transform_bvule(&mut self, expr: Le) -> Expr;
	fn transform_bvugt(&mut self, expr: Gt) -> Expr;
	fn transform_bvuge(&mut self, expr: Ge) -> Expr;
	fn transform_bvslt(&mut self, expr: SignedLt) -> Expr;
	fn transform_bvsle(&mut self, expr: SignedLe) -> Expr;
	fn transform_bvsgt(&mut self, expr: SignedGt) -> Expr;
	fn transform_bvsge(&mut self, expr: SignedGe) -> Expr;

	fn transform_bvushl(&mut self, expr: Shl) -> Expr;
	fn transform_bvushr(&mut self, expr: Shr) -> Expr;
	fn transform_bvsshr(&mut self, expr: SignedShr) -> Expr;

	fn transform_concat(&mut self, expr: Concat) -> Expr;
	fn transform_extract(&mut self, expr: Extract) -> Expr;
	fn transform_uextend(&mut self, expr: Extend) -> Expr;
	fn transform_sextend(&mut self, expr: SignedExtend) -> Expr;

	fn transform_read(&mut self, expr: Read) -> Expr;
	fn transform_write(&mut self, expr: Write) -> Expr;

	fn transform_boolconst(&mut self, expr: BoolConst) -> Expr;

	fn transform_not(&mut self, expr: Not) -> Expr;

	fn transform_and(&mut self, expr: And) -> Expr;
	fn transform_or(&mut self, expr: Or) -> Expr;
	fn transform_xor(&mut self, expr: Xor) -> Expr;
	fn transform_iff(&mut self, expr: Iff) -> Expr;
	fn transform_implies(&mut self, expr: Implies) -> Expr;

	fn transform_param_bool(&mut self, expr: ParamBool) -> Expr;

	fn transform_equals(&mut self, expr: Equals) -> Expr;
	fn transform_ite(&mut self, expr: IfThenElse) -> Expr;
	fn transform_symbol(&mut self, expr: Symbol) -> Expr;
}

pub trait Transformer: Sized {
	/// Very useful to avoid unnecesary dynamic memory allocation
	/// by reusing the given box'es dynamic memory while computing the transformation
	/// steps on the stack instead of throwing it away and re-allocating a new box 
	/// for the final result.
	/// 
	/// This expects a boxed expression as input and returns the same box with
	/// the simplified expression.
	fn boxed_transform(&mut self, boxed: P<Expr>) -> P<Expr>;

	fn transform(&mut self, expr: Expr) -> Expr;
}

impl<ConcTransformer> Transformer for ConcTransformer where ConcTransformer: TransformerImpl {
	fn boxed_transform(&mut self, mut boxed: P<Expr>) -> P<Expr> {
        // replace dummy with the boxes content
        let inner = ::std::mem::replace(&mut* boxed, Expr::BoolConst(BoolConst{value: false}));
        // do the simplifying computation that performs on the stack
        let transformed = self.transform(inner);
        // replace the temporary dummy with the simplified expression
        ::std::mem::replace(&mut* boxed, transformed);
        // return p without (re-)allocating dynamic memory
        boxed
	}

	fn transform(&mut self, expr: Expr) -> Expr {
		use self::Expr::*;
		match expr {
			BitVecConst(expr) => self.transform_bvconst(expr),
			Neg(expr) => self.transform_bvneg(expr),
			Add(expr) => self.transform_bvadd(expr),
			Mul(expr) => self.transform_bvmul(expr),
			Sub(expr) => self.transform_bvsub(expr),
			Div(expr) => self.transform_bvudiv(expr),
			Mod(expr) => self.transform_bvumod(expr),
			SignedDiv(expr) => self.transform_bvsdiv(expr),
			SignedMod(expr) => self.transform_bvsmod(expr),
			SignedRem(expr) => self.transform_bvsrem(expr),

			BitNot(expr) => self.transform_bvnot(expr),
			BitAnd(expr) => self.transform_bvand(expr),
			BitOr(expr) => self.transform_bvor(expr),
			BitXor(expr) => self.transform_bvxor(expr),
			BitNand(expr) => self.transform_bvnand(expr),
			BitNor(expr) => self.transform_bvnor(expr),
			BitXnor(expr) => self.transform_bvxnor(expr),

			Lt(expr) => self.transform_bvult(expr),
			Le(expr) => self.transform_bvule(expr),
			Gt(expr) => self.transform_bvugt(expr),
			Ge(expr) => self.transform_bvuge(expr),
			SignedLt(expr) => self.transform_bvslt(expr),
			SignedLe(expr) => self.transform_bvsle(expr),
			SignedGt(expr) => self.transform_bvsgt(expr),
			SignedGe(expr) => self.transform_bvsge(expr),

			Shl(expr) => self.transform_bvushl(expr),
			Shr(expr) => self.transform_bvushr(expr),
			SignedShr(expr) => self.transform_bvsshr(expr),

			Concat(expr) => self.transform_concat(expr),
			Extract(expr) => self.transform_extract(expr),
			Extend(expr) => self.transform_uextend(expr),
			SignedExtend(expr) => self.transform_sextend(expr),

			Read(expr) => self.transform_read(expr),
			Write(expr) => self.transform_write(expr),

			BoolConst(expr) => self.transform_boolconst(expr),

			Not(expr) => self.transform_not(expr),

			And(expr) => self.transform_and(expr),
			Or(expr) => self.transform_or(expr),
			Xor(expr) => self.transform_xor(expr),
			Iff(expr) => self.transform_iff(expr),
			Implies(expr) => self.transform_implies(expr),

			ParamBool(expr) => self.transform_param_bool(expr),

			Equals(expr) => self.transform_equals(expr),
			IfThenElse(expr) => self.transform_ite(expr),
			Symbol(expr) => self.transform_symbol(expr)
		}
	}
}

// pub trait RecursiveTransformerImpl: Sized {

// 	fn recursive_transform_bvconst(&mut self, expr: BitVecConst) -> Expr;
// 	fn recursive_transform_bvneg(&mut self, expr: Neg) -> Expr;
// 	fn recursive_transform_bvadd(&mut self, expr: Add) -> Expr;
// 	fn recursive_transform_bvmul(&mut self, expr: Mul) -> Expr;
// 	fn recursive_transform_bvsub(&mut self, expr: Sub) -> Expr;
// 	fn recursive_transform_bvudiv(&mut self, expr: Div) -> Expr;
// 	fn recursive_transform_bvumod(&mut self, expr: Mod) -> Expr;
// 	fn recursive_transform_bvsdiv(&mut self, expr: SignedDiv) -> Expr;
// 	fn recursive_transform_bvsmod(&mut self, expr: SignedMod) -> Expr;
// 	fn recursive_transform_bvsrem(&mut self, expr: SignedRem) -> Expr;

// 	fn recursive_transform_bvnot(&mut self, expr: BitNot) -> Expr;
// 	fn recursive_transform_bvand(&mut self, expr: BitAnd) -> Expr;
// 	fn recursive_transform_bvor(&mut self, expr: BitOr) -> Expr;
// 	fn recursive_transform_bvxor(&mut self, expr: BitXor) -> Expr;
// 	fn recursive_transform_bvnand(&mut self, expr: BitNand) -> Expr;
// 	fn recursive_transform_bvnor(&mut self, expr: BitNor) -> Expr;
// 	fn recursive_transform_bvxnor(&mut self, expr: BitXnor) -> Expr;

// 	fn recursive_transform_bvult(&mut self, expr: Lt) -> Expr;
// 	fn recursive_transform_bvule(&mut self, expr: Le) -> Expr;
// 	fn recursive_transform_bvugt(&mut self, expr: Gt) -> Expr;
// 	fn recursive_transform_bvuge(&mut self, expr: Ge) -> Expr;
// 	fn recursive_transform_bvslt(&mut self, expr: SignedLt) -> Expr;
// 	fn recursive_transform_bvsle(&mut self, expr: SignedLe) -> Expr;
// 	fn recursive_transform_bvsgt(&mut self, expr: SignedGt) -> Expr;
// 	fn recursive_transform_bvsge(&mut self, expr: SignedGe) -> Expr;

// 	fn recursive_transform_bvushl(&mut self, expr: Shl) -> Expr;
// 	fn recursive_transform_bvushr(&mut self, expr: Shr) -> Expr;
// 	fn recursive_transform_bvsshr(&mut self, expr: SignedShr) -> Expr;

// 	fn recursive_transform_concat(&mut self, expr: Concat) -> Expr;
// 	fn recursive_transform_extract(&mut self, expr: Extract) -> Expr;
// 	fn recursive_transform_uextend(&mut self, expr: Extend) -> Expr;
// 	fn recursive_transform_sextend(&mut self, expr: SignedExtend) -> Expr;

// 	fn recursive_transform_read(&mut self, expr: Read) -> Expr;
// 	fn recursive_transform_write(&mut self, expr: Write) -> Expr;

// 	fn recursive_transform_boolconst(&mut self, expr: BoolConst) -> Expr;

// 	fn recursive_transform_not(&mut self, expr: Not) -> Expr;

// 	fn recursive_transform_and(&mut self, expr: And) -> Expr;
// 	fn recursive_transform_or(&mut self, expr: Or) -> Expr;
// 	fn recursive_transform_xor(&mut self, expr: Xor) -> Expr;
// 	fn recursive_transform_iff(&mut self, expr: Iff) -> Expr;
// 	fn recursive_transform_implies(&mut self, expr: Implies) -> Expr;

// 	fn recursive_transform_param_bool(&mut self, expr: ParamBool) -> Expr;

// 	fn recursive_transform_equals(&mut self, expr: Equals) -> Expr;
// 	fn recursive_transform_ite(&mut self, expr: IfThenElse) -> Expr;
// 	fn recursive_transform_symbol(&mut self, expr: Symbol) -> Expr;
// }

// impl<ConcRecTransformer> RecursiveTransformerImpl for ConcRecTransformer where ConcRecTransformer: Transformer + TransformerImpl {

// 	fn recursive_transform_bvconst(&mut self, mut expr: BitVecConst) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvneg(&mut self, mut expr: Neg) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvadd(&mut self, mut expr: Add) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvmul(&mut self, mut expr: Mul) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvsub(&mut self, mut expr: Sub) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvudiv(&mut self, mut expr: Div) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvumod(&mut self, mut expr: Mod) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvsdiv(&mut self, mut expr: SignedDiv) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvsmod(&mut self, mut expr: SignedMod) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvsrem(&mut self, mut expr: SignedRem) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvnot(&mut self, mut expr: BitNot) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvand(&mut self, mut expr: BitAnd) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvor(&mut self, mut expr: BitOr) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvxor(&mut self, mut expr: BitXor) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvnand(&mut self, mut expr: BitNand) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvnor(&mut self, mut expr: BitNor) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvxnor(&mut self, mut expr: BitXnor) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvult(&mut self, mut expr: Lt) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvule(&mut self, mut expr: Le) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvugt(&mut self, mut expr: Gt) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvuge(&mut self, mut expr: Ge) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvslt(&mut self, mut expr: SignedLt) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvsle(&mut self, mut expr: SignedLe) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvsgt(&mut self, mut expr: SignedGt) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvsge(&mut self, mut expr: SignedGe) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvushl(&mut self, mut expr: Shl) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvushr(&mut self, mut expr: Shr) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_bvsshr(&mut self, mut expr: SignedShr) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_concat(&mut self, mut expr: Concat) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_extract(&mut self, mut expr: Extract) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_uextend(&mut self, mut expr: Extend) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_sextend(&mut self, mut expr: SignedExtend) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_read(&mut self, mut expr: Read) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_write(&mut self, mut expr: Write) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_boolconst(&mut self, mut expr: BoolConst) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_not(&mut self, mut expr: Not) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_and(&mut self, mut expr: And) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_or(&mut self, mut expr: Or) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_xor(&mut self, mut expr: Xor) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_iff(&mut self, mut expr: Iff) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_implies(&mut self, mut expr: Implies) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_param_bool(&mut self, mut expr: ParamBool) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_equals(&mut self, mut expr: Equals) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// 	fn recursive_transform_ite(&mut self, mut expr: IfThenElse) -> Expr {
// 		expr = self.transform_ite(expr);
// 		let cond = Box::new(self.recursive_transform(*expr.cond));
// 		expr = self.transform_ite(expr);
// 		let then_expr = self.recursive_transform(expr.then_case);
// 		let else_expr = self.recursive_transform(expr.else_case);
// 		self.transform_ite(expr)
// 	}

// 	fn recursive_transform_symbol(&mut self, mut expr: Symbol) -> Expr {
// 		Expr::BoolConst(BoolConst{value: false})
// 	}

// }

// trait RecursiveTransformer: Sized {
// 	fn recursive_transform(&mut self, expr: Expr) -> Expr;
// }

// impl<ConcRecTransformer> RecursiveTransformer for ConcRecTransformer where ConcRecTransformer: RecursiveTransformerImpl {
// 	fn recursive_transform(&mut self, expr: Expr) -> Expr {
// 		use self::Expr::*;
// 		match *expr {
// 			BitVecConst(expr) => self.recursive_transform_bvconst(expr),
// 			Neg(expr) => self.recursive_transform_bvneg(expr),
// 			Add(expr) => self.recursive_transform_bvadd(expr),
// 			Mul(expr) => self.recursive_transform_bvmul(expr),
// 			Sub(expr) => self.recursive_transform_bvsub(expr),
// 			Div(expr) => self.recursive_transform_bvudiv(expr),
// 			Mod(expr) => self.recursive_transform_bvumod(expr),
// 			SignedDiv(expr) => self.recursive_transform_bvsdiv(expr),
// 			SignedMod(expr) => self.recursive_transform_bvsmod(expr),
// 			SignedRem(expr) => self.recursive_transform_bvsrem(expr),

// 			BitNot(expr) => self.recursive_transform_bvnot(expr),
// 			BitAnd(expr) => self.recursive_transform_bvand(expr),
// 			BitOr(expr) => self.recursive_transform_bvor(expr),
// 			BitXor(expr) => self.recursive_transform_bvxor(expr),
// 			BitNand(expr) => self.recursive_transform_bvnand(expr),
// 			BitNor(expr) => self.recursive_transform_bvnor(expr),
// 			BitXnor(expr) => self.recursive_transform_bvxnor(expr),

// 			Lt(expr) => self.recursive_transform_bvult(expr),
// 			Le(expr) => self.recursive_transform_bvule(expr),
// 			Gt(expr) => self.recursive_transform_bvugt(expr),
// 			Ge(expr) => self.recursive_transform_bvuge(expr),
// 			SignedLt(expr) => self.recursive_transform_bvslt(expr),
// 			SignedLe(expr) => self.recursive_transform_bvsle(expr),
// 			SignedGt(expr) => self.recursive_transform_bvsgt(expr),
// 			SignedGe(expr) => self.recursive_transform_bvsge(expr),

// 			Shl(expr) => self.recursive_transform_bvushl(expr),
// 			Shr(expr) => self.recursive_transform_bvushr(expr),
// 			SignedShr(expr) => self.recursive_transform_bvsshr(expr),

// 			Concat(expr) => self.recursive_transform_concat(expr),
// 			Extract(expr) => self.recursive_transform_extract(expr),
// 			Extend(expr) => self.recursive_transform_uextend(expr),
// 			SignedExtend(expr) => self.recursive_transform_sextend(expr),

// 			Read(expr) => self.recursive_transform_read(expr),
// 			Write(expr) => self.recursive_transform_write(expr),

// 			BoolConst(expr) => self.recursive_transform_boolconst(expr),

// 			Not(expr) => self.recursive_transform_not(expr),

// 			And(expr) => self.recursive_transform_and(expr),
// 			Or(expr) => self.recursive_transform_or(expr),
// 			Xor(expr) => self.recursive_transform_xor(expr),
// 			Iff(expr) => self.recursive_transform_iff(expr),
// 			Implies(expr) => self.recursive_transform_implies(expr),

// 			ParamBool(expr) => self.recursive_transform_param_bool(expr),

// 			Equals(expr) => self.recursive_transform_equals(expr),
// 			IfThenElse(expr) => self.recursive_transform_ite(expr),
// 			Symbol(expr) => self.recursive_transform_symbol(expr)
// 		}
// 	}
// }
