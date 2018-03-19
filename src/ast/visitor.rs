use ast::prelude::*;

pub mod prelude {
    pub use super::{
        VisitEvent,
        RecursiveTraverseVisitor,
        Visitor
    };
}

/// An event attached to visiting an expression.
/// 
/// This is useful to query for visitor that do different things upon
/// entering or leaving an expression tree node.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum VisitEvent {
    /// The first time an expression node is visited.
    /// 
    /// Note: This happens before visiting its child expressions.
    Entering,
    /// The last time an expression node is visited.
    /// 
    /// Note: This happens after visiting its child expressions.
    Leaving,
}

/// Traverses expression trees in a recursive fashion.
/// 
/// # Traverse strategy:
/// 
/// Example for any node `n`.
/// 
/// - Visit `n` upon entering it initially.
/// - Traversing through child expressions of `n`.
/// - Visit `n` upon leaving, finally.
/// 
/// So all nodes are visited twice by this traversal strategy.
pub struct RecursiveTraverseVisitor<V>
    where V: Visitor
{
    /// The internal visitor that performs the visitation.
    visitor: V
}

impl<V> RecursiveTraverseVisitor<V>
    where V: Visitor
{
    /// Creates a new `RecursiveTraverseVisitor` for the given visitor.
    pub fn new(visitor: V) -> Self {
        RecursiveTraverseVisitor{ visitor }
    }

    /// Traverses and visits the given expression tree using
    /// recursive visiting strategy where each expression node
    /// is visited twice upon entering and leaving the node
    /// respectively.
    pub fn traverse_visit(&mut self, expr: &AnyExpr) {
        self.visitor.visit_any_expr(expr, VisitEvent::Entering);
        for child in expr.children() {
            self.traverse_visit(child);
        }
        self.visitor.visit_any_expr(expr, VisitEvent::Leaving);
    }
}

/// Types implementing this trait are capable of visiting an expression tree.
/// 
/// It is possible to visit fine grained every different expression type and
/// also coarse grained for entire expression types such as boolean expressions,
/// bitvector expressions or array expressions.
pub trait Visitor {
    /// Visit any expression.
    fn visit_any_expr(&mut self, expr: &AnyExpr, event: VisitEvent) {
        match expr.ty().kind() {
            TypeKind::Bool => self.visit_bool_expr(expr, event),
            TypeKind::Bitvec => self.visit_bitvec_expr(expr, event),
            TypeKind::Array => self.visit_array_expr(expr, event)
        }
    }

    /// Visit any boolean expression.
    fn visit_bool_expr(&mut self, expr: &AnyExpr, event: VisitEvent) {
        assert_eq!(expr.ty().kind(), TypeKind::Bool);
        use ast::AnyExpr::*;
        match expr {
            IfThenElse(expr) => self.visit_cond(expr, event),
            Symbol(expr) => self.visit_var(expr, event),
            BoolConst(expr) => self.visit_bool_const(expr, event),
            BoolEquals(expr) => self.visit_bool_equals(expr, event),
            Not(expr) => self.visit_not(expr, event),
            And(expr) => self.visit_and(expr, event),
            Or(expr) => self.visit_or(expr, event),
            Xor(expr) => self.visit_xor(expr, event),
            Implies(expr) => self.visit_implies(expr, event),
            BitvecEquals(expr) => self.visit_bitvec_equals(expr, event),
            SignedGreaterEquals(expr) => self.visit_sge(expr, event),
            SignedGreaterThan(expr) => self.visit_sgt(expr, event),
            SignedLessEquals(expr) => self.visit_sle(expr, event),
            SignedLessThan(expr) => self.visit_slt(expr, event),
            UnsignedGreaterEquals(expr) => self.visit_uge(expr, event),
            UnsignedGreaterThan(expr) => self.visit_ugt(expr, event),
            UnsignedLessEquals(expr) => self.visit_ule(expr, event),
            UnsignedLessThan(expr) => self.visit_ult(expr, event),
            _ => unreachable!() // TODO 2018-03-19: make this a hard error
        }
    }

    /// Visit any bitvector expression.
    fn visit_bitvec_expr(&mut self, expr: &AnyExpr, event: VisitEvent) {
        assert_eq!(expr.ty().kind(), TypeKind::Bitvec);
        use ast::AnyExpr::*;
        match expr {
            IfThenElse(expr) => self.visit_cond(expr, event),
            Symbol(expr) => self.visit_var(expr, event),
            ArrayRead(expr) => self.visit_array_read(expr, event),
            Add(expr) => self.visit_add(expr, event),
            BitvecConst(expr) => self.visit_bitvec_const(expr, event),
            Mul(expr) => self.visit_mul(expr, event),
            Neg(expr) => self.visit_neg(expr, event),
            SignedDiv(expr) => self.visit_sdiv(expr, event),
            SignedModulo(expr) => self.visit_smod(expr, event),
            SignedRemainder(expr) => self.visit_srem(expr, event),
            Sub(expr) => self.visit_sub(expr, event),
            UnsignedDiv(expr) => self.visit_udiv(expr, event),
            UnsignedRemainder(expr) => self.visit_urem(expr, event),
            BitAnd(expr) => self.visit_bitand(expr, event),
            BitNot(expr) => self.visit_bitnot(expr, event),
            BitOr(expr) => self.visit_bitor(expr, event),
            BitXor(expr) => self.visit_bitxor(expr, event),
            Concat(expr) => self.visit_concat(expr, event),
            Extract(expr) => self.visit_extract(expr, event),
            SignExtend(expr) => self.visit_sext(expr, event),
            ZeroExtend(expr) => self.visit_zext(expr, event),
            ArithmeticShiftRight(expr) => self.visit_ashr(expr, event),
            LogicalShiftRight(expr) => self.visit_lshr(expr, event),
            ShiftLeft(expr) => self.visit_shl(expr, event),
            _ => unreachable!() // TODO 2018-03-19: make this a hard error
        }
    }

    /// Visit any array expression.
    fn visit_array_expr(&mut self, expr: &AnyExpr, event: VisitEvent) {
        assert_eq!(expr.ty().kind(), TypeKind::Array);
        use ast::AnyExpr::*;
        match expr {
            IfThenElse(expr) => self.visit_cond(expr, event),
            Symbol(expr) => self.visit_var(expr, event),
            ArrayWrite(expr) => self.visit_array_write(expr, event),
            _ => unreachable!() // TODO 2018-03-19: make this a hard error
        }
    }

    fn visit_cond(&mut self, _cond: &expr::IfThenElse, _: VisitEvent) {}

    fn visit_var(&mut self, _bool_var: &expr::Symbol, _: VisitEvent) {}

    fn visit_bool_const(&mut self, _bool_const: &expr::BoolConst, _: VisitEvent) {}

    fn visit_bool_equals(&mut self, _bool_equals: &expr::BoolEquals, _: VisitEvent) {}

    fn visit_and(&mut self, _and: &expr::And, _: VisitEvent) {}

    fn visit_or(&mut self, _or: &expr::Or, _: VisitEvent) {}

    fn visit_not(&mut self, _not: &expr::Not, _: VisitEvent) {}

    fn visit_xor(&mut self, _xor: &expr::Xor, _: VisitEvent) {}

    fn visit_implies(&mut self, _implies: &expr::Implies, _: VisitEvent) {}

    fn visit_array_read(&mut self, _array_read: &expr::ArrayRead, _: VisitEvent) {}

    fn visit_array_write(&mut self, _array_write: &expr::ArrayWrite, _: VisitEvent) {}

    fn visit_bitvec_const(&mut self, _bitvec_const: &expr::BitvecConst, _: VisitEvent) {}

    fn visit_add(&mut self, _add: &expr::Add, _: VisitEvent) {}

    fn visit_mul(&mut self, _mul: &expr::Mul, _: VisitEvent) {}

    fn visit_neg(&mut self, _neg: &expr::Neg, _: VisitEvent) {}

    fn visit_sdiv(&mut self, _sdiv: &expr::SignedDiv, _: VisitEvent) {}

    fn visit_smod(&mut self, _smod: &expr::SignedModulo, _: VisitEvent) {}

    fn visit_srem(&mut self, _srem: &expr::SignedRemainder, _: VisitEvent) {}

    fn visit_sub(&mut self, _sub: &expr::Sub, _: VisitEvent) {}

    fn visit_udiv(&mut self, _udiv: &expr::UnsignedDiv, _: VisitEvent) {}

    fn visit_urem(&mut self, _urem: &expr::UnsignedRemainder, _: VisitEvent) {}

    fn visit_bitnot(&mut self, _bitnot: &expr::BitNot, _: VisitEvent) {}

    fn visit_bitand(&mut self, _bitand: &expr::BitAnd, _: VisitEvent) {}

    fn visit_bitor(&mut self, _bitor: &expr::BitOr, _: VisitEvent) {}

    fn visit_bitxor(&mut self, _bitxor: &expr::BitXor, _: VisitEvent) {}

    fn visit_concat(&mut self, _concat: &expr::Concat, _: VisitEvent) {}

    fn visit_extract(&mut self, _extract: &expr::Extract, _: VisitEvent) {}

    fn visit_sext(&mut self, _sext: &expr::SignExtend, _: VisitEvent) {}

    fn visit_zext(&mut self, _zext: &expr::ZeroExtend, _: VisitEvent) {}

    fn visit_bitvec_equals(&mut self, _bitvec_equals: &expr::BitvecEquals, _: VisitEvent) {}

    fn visit_sge(&mut self, _sge: &expr::SignedGreaterEquals, _: VisitEvent) {}

    fn visit_sgt(&mut self, _sgt: &expr::SignedGreaterThan, _: VisitEvent) {}

    fn visit_sle(&mut self, _sle: &expr::SignedLessEquals, _: VisitEvent) {}

    fn visit_slt(&mut self, _slt: &expr::SignedLessThan, _: VisitEvent) {}

    fn visit_uge(&mut self, _uge: &expr::UnsignedGreaterEquals, _: VisitEvent) {}

    fn visit_ugt(&mut self, _ugt: &expr::UnsignedGreaterThan, _: VisitEvent) {}

    fn visit_ule(&mut self, _ule: &expr::UnsignedLessEquals, _: VisitEvent) {}

    fn visit_ult(&mut self, _ult: &expr::UnsignedLessThan, _: VisitEvent) {}

    fn visit_ashr(&mut self, _ashr: &expr::ArithmeticShiftRight, _: VisitEvent) {}

    fn visit_lshr(&mut self, _lshr: &expr::LogicalShiftRight, _: VisitEvent) {}

    fn visit_shl(&mut self, _shl: &expr::ShiftLeft, _: VisitEvent) {}
}
