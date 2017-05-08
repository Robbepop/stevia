# TODO-List for STP-rs

- Implement attribute support for SmtExpr proc macro to improve controlling of auto generated AST code.
- Implement expression creation macro based on the syntax of SMTLib2.
- Implement generic recursive AST consumer that acts as a base for optimizations and other AST mutation operations.
- Implement generic recursive AST visitor that acts as a base for analysis on the AST or for serialization operations.
- Add naive pretty-printing facility for the AST.
- Add SMTLib2.X serialization support for the AST.

## Considerations

- Maybe remove `into_variant` from `ExprTrait` and put it into `IntoVariant` as new trait and make it possible to auto `impl From<T: IntoVariant> for ExprVariant { .. }`
