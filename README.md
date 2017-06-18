# Stevia - Satisfiability Modulo Theories (SMT) Solver

| **Linux**    | [![Build Status][travis badge]][travis link]          | | **Windows**  | [![Build Status][appveyor badge]][appveyor link]      |
|:------------:|:------------------------------------------------------|-|:------------:|:------------------------------------------------------|
| **Coverage** | [![Coverage Status][coveralls badge]][coveralls link] | | **Licence**  | [![MIT Licenced][licence badge]](./LICENCE)           |

---

This is a brave attempt to write a simple [SMT](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) solver in the [Rust](https://www.rust-lang.org/) ([github](https://github.com/rust-lang/rust)) programming language based on the design of [STP](http://stp.github.io/) ([github](https://github.com/stp/stp)).  

Currently the solver is in very early development phase.

## Very future goals are
- Support for [SMTLib 2.6](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-draft-3.pdf).
- Theories of Bitvectors and Arrays.
- Comprehensive documentation for all important parts of the code.
- Eventually be able to keep up with other SMT solvers like STP.
- C API to enable bindings for other languages.
- Use an efficient SAT solver, like [candy](https://github.com/Udopia/candy-kingdom).

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


[travis badge]: https://travis-ci.org/Robbepop/stevia.svg?branch=master
[travis link]: https://travis-ci.org/Robbepop/stevia
[appveyor badge]: https://ci.appveyor.com/api/projects/status/16fc9l6rtroo4xqd?svg=true
[appveyor link]: https://ci.appveyor.com/project/Robbepop/stevia/branch/master
[coveralls badge]: https://coveralls.io/repos/github/Robbepop/stevia/badge.svg?branch=master
[coveralls link]: https://coveralls.io/github/Robbepop/stevia?branch=master
[licence badge]: https://img.shields.io/badge/license-MIT-blue.svg
