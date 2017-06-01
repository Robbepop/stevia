| **Linux** | [![Build Status](https://travis-ci.org/Robbepop/stevia.svg?branch=master)](https://travis-ci.org/Robbepop/stevia) |
|:-:|:-:|
| **Windows** | [![Build Status](https://ci.appveyor.com/api/projects/status/16fc9l6rtroo4xqd?svg=true)](https://ci.appveyor.com/project/Robbepop/stevia/branch/master) |
| **Licence** | [![MIT licensed](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE) |

---

# Stevia - Satisfiability Modulo Theories (SMT) Solver

This is a brave attempt to write an [SMT](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) solver in the [Rust](https://www.rust-lang.org/) ([github](https://github.com/rust-lang/rust)) programming language based on the design of [STP](http://stp.github.io/) ([github](https://github.com/stp/stp)).

## Very future goals are
- Support for [SMTLib 2.6](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-draft-3.pdf).
- Theories of Bitvectors and Arrays.
- Comprehensive documentation for all important parts of the code.
- Eventually be able to keep up with other SMT solvers like STP.
- C API to enable bindings for other languages.
- Use an efficient SAT solver, like [candy-kingdom](https://github.com/Udopia/candy-kingdom).

## Simplifications

Stevia will support a great machinery of simplifications to its input formulas.
An early example of what is possible now:

```lisp
(=
  (=
    (=
      false
      (= (_ :32  42) (_ :32 1337) )
    )
    (= (_ :32 42) (_ :32 42) )
  )
  (=
    (= (not true) (= true (not true) ) )
    (= ; Here is the break: true is not false!
      (and true true)
      (= (_ :64 100) (-(-(_ :64 100))) )
    )
  )
)
```

Is getting simplified to this:

```lisp
false
```

Keep in mind that this is still a pretty naive simplification. More to come in future versions of Stevia!
