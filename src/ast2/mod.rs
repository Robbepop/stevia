mod arity;
mod into_box;
mod child_iters;
mod binexpr_childs;
mod ty;
mod expr_kind;
mod any_expr;
mod formulas;
mod terms;
mod ite;
mod symbol;
mod equals;

pub use self::arity::prelude::*;
pub use self::into_box::prelude::*;
pub use self::child_iters::prelude::*;
pub use self::binexpr_childs::prelude::*;
pub use self::ty::prelude::*;
pub use self::expr_kind::prelude::*;
pub use self::any_expr::prelude::*;

pub use self::formulas::prelude::*;
pub use self::terms::prelude::*;

pub use self::ite::prelude::*;
pub use self::symbol::prelude::*;
pub use self::equals::prelude::*;

/// Re-exports all commonly used items of this module.
mod prelude {
    pub use super::*;
}

/// An abstraction over an indirection to an entitiy `T`.
pub type P<T> = Box<T>;
