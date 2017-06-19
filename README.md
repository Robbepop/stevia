# Stevia - Satisfiability Modulo Theories (SMT) Solver

|        Linux        |       Windows       |       Coverage       |       Licence      |
|:-------------------:|:-------------------:|:--------------------:|:------------------:|
| [![travisCI][1]][2] | [![appveyor][3]][4] | [![coveralls][5]][6] | [![licence][7]][8] |

[1]: https://travis-ci.org/Robbepop/stevia.svg?branch=master
[2]: https://travis-ci.org/Robbepop/stevia
[3]: https://ci.appveyor.com/api/projects/status/16fc9l6rtroo4xqd?svg=true
[4]: https://ci.appveyor.com/project/Robbepop/stevia/branch/master
[5]: https://coveralls.io/repos/github/Robbepop/stevia/badge.svg?branch=master
[6]: https://coveralls.io/github/Robbepop/stevia?branch=master
[7]: https://img.shields.io/badge/license-MIT-blue.svg
[8]: ./LICENCE

[smt-wiki]: https://en.wikipedia.org/wiki/Satisfiability_modulo_theories
[rust-home]: https://www.rust-lang.org/
[rust-repo]: https://github.com/rust-lang/rust
[stp-home]: http://stp.github.io/
[stp-repo]: https://github.com/stp/stp
[smtlib-home]: http://smtlib.cs.uiowa.edu/index.shtml
[candy-repo]: https://github.com/Udopia/candy-kingdom

---

This is a brave attempt to write a simple [SMT][smt-wiki] solver in the [Rust][rust-home] ([github][rust-repo]) programming language based on the design of [STP][stp-home] ([github][stp-repo]).  

Currently the solver is in very early development phase.

## Very future goals are
- Support for [SMTLib 2.6][smtlib-home].
- Theories of quantifier-free bitvectors and arrays: `QF_ABV`
- Comprehensive documentation for all important parts of the code.
- Eventually be able to keep up with other SMT solvers like STP.
- C API to enable bindings for other languages.
- Use an efficient SAT solver under the hood, like [candy][candy-repo].

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
