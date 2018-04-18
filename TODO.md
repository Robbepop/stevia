# TODO-List for Stevia

## Short term

- Implement an expression tree consistency checker for the ast module.
- Clean up public visibility and prelude module usage within Stevia. (FPI: fewer-preludes-initiative)

## Long term

- Implement SMTLib2 parser.
- Add fuzzing targets for Parser and Simplifier modules.
- Find and depend on decent library implementation similar to STP's `libabc` for and-inverter-graph (AIG) computation.
- Improve doc-comments of some expressions. E.g. remove the ` ticks.
- Implement missing SMT modules
	- [x] AST
	- [x] Simplifier
	- [x] Simple Serializer
	- [ ] SMTLib2 Parser
	- [ ] SMT -> AIG (or similar): Bit Blaster
	- [ ] AIG Driver
	- [ ] AIG -> CNF: Tseytin Transformation
	- [ ] SAT Driver
	- [ ] Abstraction Refinement of Arrays
	- [ ] Linear Bitvector Solver

## Considerations

- Think about trade-offs by adding `Nand`, `Nor` and `Xnor` as new formula types.
- Make `SymbolInterner` more suitable for SMTLib2.0 shadowing and namespaces.

## Science

- Find a decent design for an `expr_tree!` macro that simplifies creation of expression trees via factories and a syntax similar to SMTLIB2.0.
- Find out what scopes `push` & `pop` in STP are and how to incorporate them into this SMT solver.
	- STP has a stack of vectors that acts as assertion scope level. Users may wish to add or remove such scopes to add or remove entire groups of assertions that have been added to the removed scope level. The STP scope design is inefficient and should not be taken over to Stevia. Stevia should model this  concept with a single vector for the assertions and another vector for entry points to new scope levels.
