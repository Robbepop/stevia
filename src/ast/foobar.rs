
	//=========================================================================
	// TERM EXPRESSIONS
	//=========================================================================

	// BITWISE EXPRESSIONS
	//-------------------------------------------------------------------------

	pub fn bvnot(ty: Type, inner: P<Expr>) -> Expr
		Expr::BitNot(expr::BitNot{ty, inner})
	}

	pub fn bvand(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		Expr::BitAnd(expr::BitAnd{ty, left, right})
	}

	pub fn bvor(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn bvxor(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn bvnand(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn bvnor(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn bvxnor(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	// ORDER COMPARE EXPRESSIONS
	//-------------------------------------------------------------------------

	pub fn bvult(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn bvule(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn bvugt(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn bvuge(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn bvslt(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn bvsle(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn bvsgt(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn bvsge(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	// SHIFT EXPRESSIONS
	//-------------------------------------------------------------------------

	pub fn bvushl(ty: Type, shifted: P<Expr>, shift_amount: P<Expr>) -> Expr
		
	}

	pub fn bvushr(ty: Type, shifted: P<Expr>, shift_amount: P<Expr>) -> Expr
		
	}

	pub fn bvsshr(ty: Type, shifted: P<Expr>, shift_amount: P<Expr>) -> Expr
		
	}

	// EXTEND & TRUNCATE EXPRESSIONS
	//-------------------------------------------------------------------------

	pub fn concat(ty: Type, hi: P<Expr>, lo: P<Expr>) -> Expr
		
	}

	pub fn extract(ty: Type, source: P<Expr>, range: Range<usize>) -> Expr
		
	}

	pub fn uextend(ty: Type, source: P<Expr>, extension: usize) -> Expr
		
	}

	pub fn sextend(ty: Type, source: P<Expr>, extension: usize) -> Expr
		
	}

	// ARRAY EXPRESSIONS
	//-------------------------------------------------------------------------

	pub fn read(ty: Type, array: P<Expr>, index: P<Expr>) -> Expr
		
	}

	pub fn write(ty: Type, array: P<Expr>, index: P<Expr>, new_val: P<Expr>) -> Expr
		
	}

	//=========================================================================
	// FORMULA EXPRESSIONS
	//=========================================================================

	pub fn boolconst(ty: Type, value: bool) -> Expr
		
	}


	pub fn not(ty: Type, inner: P<Expr>) -> Expr
		
	}

	pub fn and(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn conjunction(ty: Type, formulas: Vec<Expr>) -> Expr
		
	}

	pub fn or(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn disjunction(ty: Type, formulas: Vec<Expr>) -> Expr
		
	}

	pub fn xor(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn iff(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn implies(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn parambool(ty: Type, bool_var: P<Expr>, parameter: P<Expr>) -> Expr
		
	}

	//=========================================================================
	// GENERIC EXPRESSIONS
	//=========================================================================

	pub fn eq(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn ne(ty: Type, left: P<Expr>, right: P<Expr>) -> Expr
		
	}

	pub fn equality(ty: Type, formulas: Vec<Expr>) -> Expr
		
	}

	pub fn ite(ty: Type, cond: P<Expr>, then_case: P<Expr>, else_case: P<Expr>) -> Expr
		
	}

	pub fn symbol(ty: Type, name: SymName, ty: Type) -> Expr
		
	}

	pub fn boolean(ty: Type, name: SymName) -> Expr
		
	}

	pub fn bitvec(ty: Type, name: SymName, bitwidth: Bits) -> Expr
		
	}

	pub fn array(ty: Type, name: SymName, idx_width: Bits, val_width: Bits) -> Expr
		
	}
