## Simplifier

[100]: https://github.com/Robbepop/stevia/blob/master/src/simplifier/simplifications/bool_symbolic_solver.rs
[110]: https://github.com/Robbepop/stevia/blob/master/src/simplifier/simplifications/bool_const_prop.rs

The simplifier is a term rewriting system for the theories of bitvector and arrays.
Currently only a fraction of the final rewriting rules are implemented.

The simplifier's architecture consists of many different simplification passes that have a unique
and distinct simplification job within the entire simplification procedure.
The simplifier calls those simplification passes similar as to how a modern compiler invokes its
semantic checking and optimizing passes over the abstract code.

This `README` will contain a brief description of all simplification passes as well as a list
of all expressions and their associated simplification rules and their connection to the passes
to provide readers of this `README` an overview of all simplification rules and passes.

### Legend

|      Symbol       |           Meaning           |
|:-----------------:|:---------------------------:|
| `⊤`               | Symbol representing `true`  |
| `⊥`               | Symbol representing `false` |
| `x ➔ y`           | `x` is simplified to `y`    |
| ☑                 | Simplification already implemented. |
| ☐                 | Simplification currently unimplemented. |

### Simplifications

- IfThenElse

	**Formula:** `(ite condition then_case else_case)`

	- [x] `(ite c t e)` where `t == e` ➔ `t` ([BoolSymbolicSolver][100])
	- [x] `(ite (not c) t e)` ➔ `(ite c e t)` ([BoolSymbolicSolver][100])
	- [x] `(ite ⊤ t e)` ➔ `t` ([BoolConstPropagator][110])
	- [x] `(ite ⊥ t e)` ➔ `e` ([BoolConstPropagator][110])
	- [x] `(ite c t e)` where `t, e ∈ {⊤, ⊥}` and `t = e` ➔ `t` ([BoolConstPropagator][110])
	- [x] `(ite c ⊤ ⊥)` ➔ `c` ([BoolConstPropagator][110])
	- [x] `(ite c ⊥ ⊤)` ➔ `not c` ([BoolConstPropagator][110])
	- [x] `(ite c ⊤ e)` ➔ `(or c e)` ([BoolConstPropagator][110])
	- [x] `(ite c t ⊤)` ➔ `(or (not c) t)` ([BoolConstPropagator][110])
	- [x] `(ite c ⊥ e)` ➔ `(and (not c) e)` ([BoolConstPropagator][110])
	- [x] `(ite c t ⊥)` ➔ `(and c t)` ([BoolConstPropagator][110])
	- [ ] `(ite c c (not c))` ➔ `(ite c ⊤ ⊥)` (IfConstraintPropagation)
