
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprKind {
	//=========================================================================
	// TERM EXPRESSIONS
	//=========================================================================

	BitVecConst,

	Neg,

	Add,
	Mul,

	Sub,

	Div,
	Mod,
	SignedDiv,
	SignedMod,
	SignedRem,

	BitNot,
	BitAnd,
	BitOr,
	BitXor,
	BitNand,
	BitNor,
	BitXnor,

	Lt,
	Le,
	Gt,
	Ge,
	SignedLt,
	SignedLe,
	SignedGt,
	SignedGe,

	Shl,
	Shr,
	SignedShr,

	Concat,
	Extract,
	Extend,
	SignedExtend,

	Read,
	Write,

	//=========================================================================
	// FORMULA EXPRESSIONS
	//=========================================================================

	BoolConst,

	Not,

	And,
	Or,
	Xor,
	Iff,
	Implies,

	ParamBool,

	//=========================================================================
	// GENERIC EXPRESSIONS
	//=========================================================================

	Equals,
	IfThenElse,
	Symbol,
}
