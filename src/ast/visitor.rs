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
    /// Traverses and visits the given expression tree using
    /// recursive visiting strategy where each expression node
    /// is visited twice upon entering and leaving the node
    /// respectively.
    fn traverse_visit(&self, expr: &AnyExpr) {
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
    fn visit_any_expr(&self, expr: &AnyExpr, event: VisitEvent) {
        match expr.ty().kind() {
            TypeKind::Bool => self.visit_bool_expr(expr, event),
            TypeKind::Bitvec => self.visit_bitvec_expr(expr, event),
            TypeKind::Array => self.visit_array_expr(expr, event)
        }
    }

    /// Visit any boolean expression.
    fn visit_bool_expr(&self, expr: &AnyExpr, event: VisitEvent) {
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
    fn visit_bitvec_expr(&self, expr: &AnyExpr, event: VisitEvent) {
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
    fn visit_array_expr(&self, expr: &AnyExpr, event: VisitEvent) {
        assert_eq!(expr.ty().kind(), TypeKind::Array);
        use ast::AnyExpr::*;
        match expr {
            IfThenElse(expr) => self.visit_cond(expr, event),
            Symbol(expr) => self.visit_var(expr, event),
            ArrayWrite(expr) => self.visit_array_write(expr, event),
            _ => unreachable!() // TODO 2018-03-19: make this a hard error
        }
    }

    fn visit_cond(&self, _cond: &expr::IfThenElse, _: VisitEvent) {}

    fn visit_var(&self, _bool_var: &expr::Symbol, _: VisitEvent) {}

    fn visit_bool_const(&self, _bool_const: &expr::BoolConst, _: VisitEvent) {}

    fn visit_bool_equals(&self, _bool_equals: &expr::BoolEquals, _: VisitEvent) {}

    fn visit_and(&self, _and: &expr::And, _: VisitEvent) {}

    fn visit_or(&self, _or: &expr::Or, _: VisitEvent) {}

    fn visit_not(&self, _not: &expr::Not, _: VisitEvent) {}

    fn visit_xor(&self, _xor: &expr::Xor, _: VisitEvent) {}

    fn visit_implies(&self, _implies: &expr::Implies, _: VisitEvent) {}

    fn visit_array_read(&self, _array_read: &expr::ArrayRead, _: VisitEvent) {}

    fn visit_array_write(&self, _array_write: &expr::ArrayWrite, _: VisitEvent) {}

    fn visit_bitvec_const(&self, _bitvec_const: &expr::BitvecConst, _: VisitEvent) {}

    fn visit_add(&self, _add: &expr::Add, _: VisitEvent) {}

    fn visit_mul(&self, _mul: &expr::Mul, _: VisitEvent) {}

    fn visit_neg(&self, _neg: &expr::Neg, _: VisitEvent) {}

    fn visit_sdiv(&self, _sdiv: &expr::SignedDiv, _: VisitEvent) {}

    fn visit_smod(&self, _smod: &expr::SignedModulo, _: VisitEvent) {}

    fn visit_srem(&self, _srem: &expr::SignedRemainder, _: VisitEvent) {}

    fn visit_sub(&self, _sub: &expr::Sub, _: VisitEvent) {}

    fn visit_udiv(&self, _udiv: &expr::UnsignedDiv, _: VisitEvent) {}

    fn visit_urem(&self, _urem: &expr::UnsignedRemainder, _: VisitEvent) {}

    fn visit_bitnot(&self, _bitnot: &expr::BitNot, _: VisitEvent) {}

    fn visit_bitand(&self, _bitand: &expr::BitAnd, _: VisitEvent) {}

    fn visit_bitor(&self, _bitor: &expr::BitOr, _: VisitEvent) {}

    fn visit_bitxor(&self, _bitxor: &expr::BitXor, _: VisitEvent) {}

    fn visit_concat(&self, _concat: &expr::Concat, _: VisitEvent) {}

    fn visit_extract(&self, _extract: &expr::Extract, _: VisitEvent) {}

    fn visit_sext(&self, _sext: &expr::SignExtend, _: VisitEvent) {}

    fn visit_zext(&self, _zext: &expr::ZeroExtend, _: VisitEvent) {}

    fn visit_bitvec_equals(&self, _bitvec_equals: &expr::BitvecEquals, _: VisitEvent) {}

    fn visit_sge(&self, _sge: &expr::SignedGreaterEquals, _: VisitEvent) {}

    fn visit_sgt(&self, _sgt: &expr::SignedGreaterThan, _: VisitEvent) {}

    fn visit_sle(&self, _sle: &expr::SignedLessEquals, _: VisitEvent) {}

    fn visit_slt(&self, _slt: &expr::SignedLessThan, _: VisitEvent) {}

    fn visit_uge(&self, _uge: &expr::UnsignedGreaterEquals, _: VisitEvent) {}

    fn visit_ugt(&self, _ugt: &expr::UnsignedGreaterThan, _: VisitEvent) {}

    fn visit_ule(&self, _ule: &expr::UnsignedLessEquals, _: VisitEvent) {}

    fn visit_ult(&self, _ult: &expr::UnsignedLessThan, _: VisitEvent) {}

    fn visit_ashr(&self, _ashr: &expr::ArithmeticShiftRight, _: VisitEvent) {}

    fn visit_lshr(&self, _lshr: &expr::LogicalShiftRight, _: VisitEvent) {}

    fn visit_shl(&self, _shl: &expr::ShiftLeft, _: VisitEvent) {}
}
