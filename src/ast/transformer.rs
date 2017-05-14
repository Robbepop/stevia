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
	/// Consumes the given boxed-expression and returns a simplified equisatifiable boxed-expression.
	/// 
	/// This will reuse the box and thus avoids allocating dynamic memory.
	/// Returns identity if no simplifications have occured.
	fn boxed_transform(&mut self, boxed: P<Expr>) -> P<Expr>;

	/// Consumes the given expression and returns a simplified equisatifiable expression.
	/// 
	/// Returns identity if no simplifications have occured.
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
