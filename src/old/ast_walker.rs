use ast::{ExprNode};

pub trait Visitor<'ast>: Sized {
	fn visit_expr(&mut self, expr: &'ast ExprNode) {
		self.pre_visit_expr(expr);
		walk_node_expr(self, expr);
		self.post_visit_expr(expr);
	}

	fn pre_visit_expr(&mut self, _: &'ast ExprNode) {}
	fn post_visit_expr(&mut self, _: &'ast ExprNode) {}
}

pub fn walk_node_expr<'a, V: Visitor<'a>>(visitor: &mut V, expr: &'a ExprNode) {
	use ast::ExprKind::*;
	match expr.kind {

		Undefined  => {},
		Symbol{..} => {},

		Term(ref term) => {
			use ast::Term::*;
			match *term {
				BitVecConst(_) => {},

				Arithmetic(ref calc) => {
					use ast::Arithmetic::*;
					match *calc {
						Neg(ref subexpr) => {
							visitor.visit_expr(subexpr)
						},
						Add{ref terms} => {
							for term in terms.iter() {
								visitor.visit_expr(term)
							}
						},
						Mul{ref factors} => {
							for factor in factors.iter() {
								visitor.visit_expr(factor)
							}
						},
						Sub{ref minuend, ref subtrahend} => {
							visitor.visit_expr(minuend);
							visitor.visit_expr(subtrahend);
						},
						Div{ref dividend, ref divisor} => {
							visitor.visit_expr(dividend);
							visitor.visit_expr(divisor);
						},
						Mod{ref dividend, ref divisor} => {
							visitor.visit_expr(dividend);
							visitor.visit_expr(divisor);
						},
						SignedDiv{ref dividend, ref divisor} => {
							visitor.visit_expr(dividend);
							visitor.visit_expr(divisor);
						},
						SignedMod{ref dividend, ref divisor} => {
							visitor.visit_expr(dividend);
							visitor.visit_expr(divisor);
						},
						SignedRem{ref dividend, ref divisor} => {
							visitor.visit_expr(dividend);
							visitor.visit_expr(divisor);
						}
					}
				},

				Bitwise(ref bitwise_op) => {
					visitor.visit_expr(&bitwise_op.left);
					visitor.visit_expr(&bitwise_op.right);
				},

				Shift(ref shift) => {
					visitor.visit_expr(&shift.left);
					visitor.visit_expr(&shift.right);
				},

				Ordering(ref ordering) => {
					visitor.visit_expr(&ordering.left);
					visitor.visit_expr(&ordering.right);
				},

				Concat{ref hi, ref lo} => {
					visitor.visit_expr(hi);
					visitor.visit_expr(lo);
				},
				Extract{ref bitvec, ref lo_bit, ref hi_bit} => {
					visitor.visit_expr(bitvec);
					visitor.visit_expr(lo_bit);
					visitor.visit_expr(hi_bit);
				},
				Extend{ref bitvec, ref extension} => {
					visitor.visit_expr(bitvec);
					visitor.visit_expr(extension);
				},
				SignedExtend{ref bitvec, ref extension} => {
					visitor.visit_expr(bitvec);
					visitor.visit_expr(extension);
				},

				Read{ref array, ref index} => {
					visitor.visit_expr(array);
					visitor.visit_expr(index);
				},
				Write{ref array, ref index, ref new_val} => {
					visitor.visit_expr(array);
					visitor.visit_expr(index);
					visitor.visit_expr(new_val);
				}
			}
		},

		Formula(ref formula) => {
			use ast::Formula::*;
			match *formula {
				BoolConst(_) => {},
				Not(ref subexpr) => {
					visitor.visit_expr(subexpr);
				},
				And{ref conjunctions} => {
					for formula in conjunctions.iter() {
						visitor.visit_expr(formula);
					}
				},
				Or{ref disjunctions} => {
					for formula in disjunctions.iter() {
						visitor.visit_expr(formula);
					}
				},
				Binary(ref binary_formula) => {
					visitor.visit_expr(&binary_formula.left);
					visitor.visit_expr(&binary_formula.right);
				},
				ParamBool{ref bool_var, ref param} => {
					visitor.visit_expr(bool_var);
					visitor.visit_expr(param);
				}
			}
		},

		Equals{ref left, ref right} => {
			visitor.visit_expr(left);
			visitor.visit_expr(right);
		},

		IfThenElse{ref cond, ref then_case, ref else_case} => {
			visitor.visit_expr(cond);
			visitor.visit_expr(then_case);
			visitor.visit_expr(else_case);
		},

		Array{..}   => {},
		Bitvec{..}  => {},
		Boolean{..} => {}
	}
}
