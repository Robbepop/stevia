mod child_iters;
mod ty;
mod expr;
mod ite;
mod symbol;
mod equals;

pub use self::ty::prelude::*;
pub use self::expr::prelude::*;
pub use self::ite::prelude::*;
pub use self::symbol::prelude::*;
pub use self::equals::prelude::*;

/// Re-exports all commonly used items of this module.
mod prelude {
    pub use super::*;
}

/// An abstraction over an indirection to an entitiy `T`.
pub type P<T> = Box<T>;
