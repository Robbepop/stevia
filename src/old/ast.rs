
/// An abstraction over an indirection to an entitiy `T`.
type P<T> = Box<T>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ExprId(u32);

// trait Expr {
// 	/// Returns an read-only reference to the expression's kind and internals.
// 	fn kind(&self) -> &ExprKind;

// 	/// Returns a mutable reference to the expression's kind and internals.
// 	fn kind_mut(&mut self) -> &mut ExprKind;

// 	/// Returns the type of the expression.
// 	fn ty(&self) -> Type;

// 	/// Returns an iterator over all children of the expression.
// 	fn children(&self) -> Iterator<Item=&ExprNode>;

// 	/// Returns a mutable iterator over all children of the expression.
// 	fn children_mut(&mut self) -> Iterator<Item=&mut ExprNode>;
// }

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExprNode {
	/// The kind of the expression.
	pub kind: ExprKind,
	/// The type of the expression.
	/// 
	/// This is mainly used to cache the type instead of re-computing it all the time.
	pub ty  : Type,
	/// The internal unique identifier for this expression node.
	pub id  : ExprId,
}

// impl ExprNode {
// 	pub fn is_bitwise(&self) -> bool {
// 		true
// }

/// Stub object definition.
/// 
/// This will be replaced for a real implementation of bitvectors.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BitVec(u64);

impl BitVec {
	pub fn into_u64(&self) -> u64 {
		self.0
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SymName(u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Type {
	/// States that this type has yet to be infered.
	/// 
	/// Maybe we do not need this variant at all.
	Infer,
	/// Boolean type.
	Boolean,
	/// Bitvector type with the given bit-width.
	BitVec(usize),
	/// Array type with the given index-width and value-width.
	Array(usize, usize)
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum BitwiseKind {
	Not,
	And,
	Or,
	Xor,
	Nand,
	Nor,
	Xnor,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Bitwise {
	pub kind : BitwiseKind,
	pub left : P<ExprNode>,
	pub right: P<ExprNode>
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum OrderingKind {
	Lt,
	Le,
	Gt,
	Ge,
	SignedLt,
	SignedLe,
	SignedGt,
	SignedGe
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ordering {
	pub kind : OrderingKind,
	pub left : P<ExprNode>,
	pub right: P<ExprNode>
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ShiftKind {
	Left,
	Right,
	SignedRight
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Shift {
	pub kind : ShiftKind,
	pub left : P<ExprNode>,
	pub right: P<ExprNode>
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Arithmetic {
	Neg(P<ExprNode>),

	Add{terms: Vec<ExprNode>},
	Mul{factors: Vec<ExprNode>},

	Sub{minuend: P<ExprNode>, subtrahend: P<ExprNode>},

	Div{dividend: P<ExprNode>, divisor: P<ExprNode>},
	Mod{dividend: P<ExprNode>, divisor: P<ExprNode>},
	SignedDiv{dividend: P<ExprNode>, divisor: P<ExprNode>},
	SignedMod{dividend: P<ExprNode>, divisor: P<ExprNode>},
	SignedRem{dividend: P<ExprNode>, divisor: P<ExprNode>}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
	BitVecConst(BitVec),

	Arithmetic(Arithmetic),
	Bitwise(Bitwise),
	Ordering(Ordering),
	Shift(Shift),

	Concat{hi: P<ExprNode>, lo: P<ExprNode>},
	Extract{bitvec: P<ExprNode>, lo_bit: P<ExprNode>, hi_bit: P<ExprNode>},
	Extend{bitvec: P<ExprNode>, extension: P<ExprNode>},
	SignedExtend{bitvec: P<ExprNode>, extension: P<ExprNode>},

	Read{array: P<ExprNode>, index: P<ExprNode>},
	Write{array: P<ExprNode>, index: P<ExprNode>, new_val: P<ExprNode>}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum BinFormulaKind {
	Xor,
	Nand,
	Nor,
	Iff,
	Implies
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BinFormula {
	pub kind : BinFormulaKind,
	pub left : P<ExprNode>,
	pub right: P<ExprNode>
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Formula {
	BoolConst(bool),

	Not(P<ExprNode>),

	And{conjunctions: Vec<ExprNode>},
	Or{disjunctions: Vec<ExprNode>},

	Binary(BinFormula),

	ParamBool{bool_var: P<ExprNode>, param: P<ExprNode>}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprKind {
	Undefined,

	Symbol{name: SymName, ty: Type},

	Term(Term),
	Formula(Formula),

	Equals{left: P<ExprNode>, right: P<ExprNode>},
	IfThenElse{cond: P<ExprNode>, then_case: P<ExprNode>, else_case: P<ExprNode>},

	Array{name: SymName, index_type: P<Type>, value_type: P<Type>},
	Bitvec{name: SymName, bit_width: usize},
	Boolean{name: SymName}
}

impl ExprNode {
	pub fn bitvec(name: SymName, bit_width: usize) -> ExprNode {
		ExprNode{
			kind: ExprKind::Bitvec{name, bit_width},
			ty: Type::BitVec(bit_width),
			id: ExprId(0)}
	}

	pub fn eq(left: ExprNode, right: ExprNode) -> ExprNode {
		ExprNode{
			kind: ExprKind::Equals{left: Box::new(left), right: Box::new(right)},
			ty: Type::Infer,
			id: ExprId(1)}
	}

	pub fn symbol(_: &str, ty: Type) -> ExprNode {
		ExprNode{ kind: ExprKind::Symbol{name: SymName(0), ty}, ty, id: ExprId(2)}
	}

	pub fn neg(inner: ExprNode) -> ExprNode {
		ExprNode{
			kind: ExprKind::Term(Term::Arithmetic(Arithmetic::Neg(Box::new(inner)))),
			ty: Type::Infer,
			id: ExprId(8)}
	}

	pub fn add(left: ExprNode, right: ExprNode) -> ExprNode {
		ExprNode::sum(vec![left, right])
	}

	pub fn sum(terms: Vec<ExprNode>) -> ExprNode {
		ExprNode{
			kind: ExprKind::Term(Term::Arithmetic(Arithmetic::Add{terms})),
			ty: Type::Infer,
			id: ExprId(3)}
	}

	pub fn mul(left: ExprNode, right: ExprNode) -> ExprNode {
		ExprNode::product(vec![left, right])
	}

	pub fn product(factors: Vec<ExprNode>) -> ExprNode {
		ExprNode{
			kind: ExprKind::Term(Term::Arithmetic(Arithmetic::Mul{factors})),
			ty: Type::Infer,
			id: ExprId(4)}
	}

	pub fn bool_const(value: bool) -> ExprNode {
		ExprNode{
			kind: ExprKind::Formula(Formula::BoolConst(value)),
			ty: Type::Boolean,
			id: ExprId(6)
		}
	}

	pub fn bitvec_const<T>(value: T) -> ExprNode
		where T: Into<BitVec>
	{
		ExprNode{
			kind: ExprKind::Term(Term::BitVecConst(value.into())),
			ty: Type::Infer,
			id: ExprId(5)}
	}
}

impl From<u32> for BitVec {
	fn from(value: u32) -> BitVec {
		BitVec(value as u64)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn simple_expr() {
		let x         = ExprNode::symbol("x", Type::BitVec(8));
		let x_plus_x  = ExprNode::add(x.clone(), x.clone());
		let two       = ExprNode::bitvec_const(2);
		let x_times_2 = ExprNode::mul(x.clone(), two.clone());
		let equality  = ExprNode::eq(x_plus_x, x_times_2);

		use ::ast_walker::Visitor;
		use ::printing_visitor::PrintingVisitor;
		let mut out = ::std::io::stdout();
		let mut printer = PrintingVisitor::new(&mut out);
		printer.visit_expr(&equality);

		// let equality = expr!{
		// 	(define :bool_var x)
		// 	(eq
		// 		(mul (var x) (bitvec_const 2))
		// 		(add (var x) (var x))
		// 	)
		// };
	}
}
