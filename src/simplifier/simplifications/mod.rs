mod bool_const_prop;
mod bool_symbolic_solver;
mod bool_lowering;
mod cmp_reduction;
mod equality_joiner;
mod involution;
mod normalizer;
mod flattening;
mod term_const_prop;
mod term_lowering;
mod like_term_joiner;
mod read_ite_lifting;

pub mod prelude {
    pub use super::{
        BoolConstPropagator,
        BoolSymbolicSolver,
        BoolReducer,
        ComparisonReducer,
        EqualityJoiner,
        InvolutionSimplifier,
        Normalizer,
        TermConstPropagator,
        TermReducer,
        LikeTermJoiner
    };
}

pub use self::cmp_reduction::prelude::*;
pub use self::involution::prelude::*;
pub use self::bool_const_prop::prelude::*;
pub use self::bool_symbolic_solver::prelude::*;
pub use self::bool_lowering::prelude::*;
pub use self::equality_joiner::prelude::*;
pub use self::normalizer::prelude::*;
pub use self::flattening::prelude::*;
pub use self::term_const_prop::prelude::*;
pub use self::term_lowering::prelude::*;
pub use self::like_term_joiner::prelude::*;
pub use self::read_ite_lifting::prelude::*;
