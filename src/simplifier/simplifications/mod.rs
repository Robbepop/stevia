mod bool_const_prop;
mod bool_symbolic_solver;
mod cmp_reduction;
mod equality_joiner;
mod involution;
mod normalizer;
mod flattening;
mod term_const_prop;
mod like_term_joiner;

pub mod prelude {
    pub use super::{
        BoolConstPropagator,
        BoolSymbolicSolver,
        ComparisonReducer,
        EqualityJoiner,
        InvolutionSimplifier,
        Normalizer,
        TermConstPropagator,
        LikeTermJoiner
    };
}

pub use self::cmp_reduction::prelude::*;
pub use self::involution::prelude::*;
pub use self::bool_const_prop::prelude::*;
pub use self::bool_symbolic_solver::prelude::*;
pub use self::equality_joiner::prelude::*;
pub use self::normalizer::prelude::*;
pub use self::flattening::prelude::*;
pub use self::term_const_prop::prelude::*;
pub use self::like_term_joiner::prelude::*;
