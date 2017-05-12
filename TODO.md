# TODO-List for Stevia

## Critical TODO's

- Finally add an attribute to `SmtExpr` proc. macro to set the expression type explicitely. (BitVecConst needs this!)
- Implement an `expr_tree!` macro to simplify building up extression trees with a syntax similar to SMTLib2.0.

## Short term TODO's

- Implement generic recursive AST consumer that acts as a base for optimizations and other AST mutation operations.
- Implement `Context` (or `Scope`) for handling symbols and their associated metadata. Used by factories.

## Long term TODO's

- Write documentation for all stable parts of the code.
- Implement expression simplifier based on generic recursive AST consumer.
- Find and depend on decent Bitvector library implementation.
- Find and depend on decent library implementation similar to STP's `libabc` for and-inverter-graph (AIG) computation..
- Add SMTLib2.X serialization (printer) and deserialization (parser) support.
- Implement `simple_type_check` method to naively check the children's type of a newly created expression for validity. This can be used by factory implementations that want to check for this addional safety guard. (Maybe this is not needed if we always create new child expressions with a type-checking factory!)

## Considerations

- Rename `ExprTrait` to `IExpr`.
- Maybe remove `into_variant` from `ExprTrait` and put it into `IntoVariant` as new trait and make it possible to auto `impl From<T: IntoVariant> for ExprVariant { .. }`. Or maybe remove it if it is not needed at all.

## Science

- Try to find a decent design to model `bvsum`, `bvprod`, `conjunction` and `disjunction` in `ExprFactory`.
- Find out how to solve the problem of evaluability of bitvector `ty: Type` in `NaiveExprFactory::{s|u}extend` methods.
- Find out what scopes `push` & `pop` in STP are and how to incorporate them into this SMT solver.
