use ast2::prelude::*;

/// Reexports all commonly used items of this module.
pub mod prelude {
    pub use super::{
        Expr,
        ExprKind,
        HasKind
    };
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Ite(IfThenElse),
    Symbol(Symbol),
    Equals(Equals)
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ExprKind {
    /// The if-then-else expression kind.
    Ite,
    /// The symbol expression kind
    Symbol,
    /// The equality expression kind
    Equals
}

/// This trait should be implemented by all structures that represent
/// an expression kind.
/// 
/// This is obviously true for `ExprKind` itself but also for all concrete expression types.
pub trait HasKind {
    /// Returns the kind of `self`.
    fn kind(&self) -> ExprKind;
}

impl HasKind for ExprKind {
    fn kind(&self) -> ExprKind {
        *self
    }
}

impl HasType for Expr {
    fn ty(&self) -> Type {
        use self::Expr::*;
        match *self {
            Ite(ref ite) => ite.ty(),
            Symbol(ref symbol) => symbol.ty(),
            Equals(ref equals) => equals.ty()
        }
    }
}
