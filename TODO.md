# TODO-List for STP-rs

- Implement `Context` for handling symbols and their associated metadata. Used by factories.
- Implement error handling mechanism and data structures. Used by factories for example.
- Implement `NaiveExprFactory` for handling creation of expressions.
- Implement `simple_type_check` method to naively check the children's type of a newly created expression for validity. This can be used by factory implementations that want to check for this addional safety guard.
- Implement attribute support for SmtExpr proc macro to improve controlling of auto generated AST code.
- Implement expression creation macro based on the syntax of SMTLib2.
- Implement generic recursive AST consumer that acts as a base for optimizations and other AST mutation operations.
- Add SMTLib2.X serialization support for the AST.

## Considerations

- Rename `ExprVariant` to `Expr`, `ExprTrait` to `IExpr`.
- Maybe remove `into_variant` from `ExprTrait` and put it into `IntoVariant` as new trait and make it possible to auto `impl From<T: IntoVariant> for ExprVariant { .. }`
