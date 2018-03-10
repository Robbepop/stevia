use ast::prelude::*;


use either::Either;

pub mod prelude {
    pub use super::TermSymbolicSolver;
}

/// This simplification procedure dissolves term expressions with symbolic simplifications.
/// 
/// This works best if used after an expression normalization transformation and
/// might be expensive for deeply nested expression trees that have many similarities.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TermSymbolicSolver;

impl AutoImplAnyTransformer for TermSymbolicSolver {}

        }
    }
                    }
                }
            }
            }
        }
}

    }
}

impl Transformer for TermSymbolicSolver {
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplifier::prelude::*;

    create_modular_ast_transformer! {
        struct TermSymbolicSolverTransformer;
        (_0, TermSymbolicSolver)
    }
    type TermSymbolicSolverSimplifier = BaseSimplifier<TermSymbolicSolverTransformer>;

    fn create_simplifier() -> TermSymbolicSolverSimplifier {
        TermSymbolicSolverSimplifier::default()
    }

    fn simplify(expr: &mut AnyExpr) -> TransformEffect {
        create_simplifier().simplify(expr)
    }

    fn assert_simplified<E1, E2>(input: E1, expected: E2)
        where E1: IntoAnyExprOrError,
              E2: IntoAnyExprOrError
    {
        let mut input = input.into_any_expr_or_error().unwrap();
        let expected = expected.into_any_expr_or_error().unwrap();
        simplify(&mut input);
        assert_eq!(input, expected);
    }

    fn new_builder() -> PlainExprTreeBuilder {
        PlainExprTreeBuilder::default()
    }

                ),
                ),
            )
    }
}
