
use bitvec::BitVec;
use ast::variants::{ExprVariant, ExprKind};
use ast::traits::ExprTrait;
use ast::{P, Type};
use ast::iterators::{Childs, ChildsMut, IntoChilds};

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
#[SmtExprFnTyBody = "self.value.width()"]
pub struct BitVecConst{pub value: BitVec}

//=============================================================================
// ARITHMETIC EXPRESSIONS
//=============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Neg{pub inner: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Add{pub terms: Vec<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Mul{pub factors: Vec<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Sub{pub minuend: P<ExprVariant>, pub subtrahend: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Div{pub dividend: P<ExprVariant>, pub divisor: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Mod{pub dividend: P<ExprVariant>, pub divisor: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct SignedDiv{pub dividend: P<ExprVariant>, pub divisor: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct SignedMod{pub dividend: P<ExprVariant>, pub divisor: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct SignedRem{pub dividend: P<ExprVariant>, pub divisor: P<ExprVariant>}

//=============================================================================
// BITWISE EXPRESSIONS
//=============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct BitNot{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct BitAnd{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct BitOr{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct BitXor{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct BitNand{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct BitNor{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct BitXnor{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

//=============================================================================
// ORDER COMPARE EXPRESSIONS
//=============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Lt{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Le{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Gt{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Ge{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct SignedLt{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct SignedLe{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct SignedGt{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct SignedGe{pub left: P<ExprVariant>, pub right: P<ExprVariant>}

//=============================================================================
// SHIFT EXPRESSIONS
//=============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Shl{pub shifted: P<ExprVariant>, pub shift_amount: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Shr{pub shifted: P<ExprVariant>, pub shift_amount: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct SignedShr{pub shifted: P<ExprVariant>, pub shift_amount: P<ExprVariant>}

//=============================================================================
// EXTEND & EXTRACT EXPRESSIONS
//=============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Concat{pub hi: P<ExprVariant>, pub lo: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Extract{pub source: P<ExprVariant>, pub lo_bit: P<ExprVariant>, pub hi_bit: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Extend{pub source: P<ExprVariant>, pub extension: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct SignedExtend{pub source: P<ExprVariant>, pub extension: P<ExprVariant>}

//=============================================================================
// ARRAY EXPRESSIONS
//=============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Read{pub array: P<ExprVariant>, pub index: P<ExprVariant>}

#[derive(Debug, Clone, PartialEq, Eq, Hash, SmtExpr)]
pub struct Write{pub array: P<ExprVariant>, pub index: P<ExprVariant>, pub new_val: P<ExprVariant>}
