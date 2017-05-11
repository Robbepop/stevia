# TODO-List for Stevia

## Critical TODO's

- Add a `ty: Type` field to all non-boolean expressions and implement `NaiveExprFactory` for them.
- Finally add an attribute to `SmtExpr` proc. macro to set the expression type explicitely. (BitVecConst needs this!)
- Implement a macro to simplify building up extression trees.

## Short term TODO's

- Implement `Context` for handling symbols and their associated metadata. Used by factories.
- Implement `simple_type_check` method to naively check the children's type of a newly created expression for validity. This can be used by factory implementations that want to check for this addional safety guard. (Maybe this is not needed if we always create new child expressions with a type-checking factory!)
- Implement expression creation macro based on the syntax of SMTLib2.
- Implement generic recursive AST consumer that acts as a base for optimizations and other AST mutation operations.

## Long term TODO's

- Implement expression simplifier based on generic recursive AST consumer.
- Find and depend on decent Bitvector library implementation.
- Find and depend on decent library implementation similar to STP's `libabc` for and inverter graph (AIG) computation..
- Add SMTLib2.X serialization and deserialization support.

## Considerations

- Try to find a decent design to model `bvsum`, `bvprod`, `conjunction` and `disjunction` in `ExprFactory`.
- Rename `ExprTrait` to `IExpr`.
- Maybe remove `into_variant` from `ExprTrait` and put it into `IntoVariant` as new trait and make it possible to auto `impl From<T: IntoVariant> for ExprVariant { .. }`
