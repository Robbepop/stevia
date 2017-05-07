[![Build Status](https://travis-ci.org/Robbepop/stevia.svg?branch=master)](https://travis-ci.org/Robbepop/stevia)
[![MIT licensed](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE)

# Stevia - Satisfiability Modulo Theories (SMT) Solver

This is an brave attempt to write an [SMT](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) solver in the [Rust](https://www.rust-lang.org/) programming language based on the design of [STP](http://stp.github.io/).

## Very future goals are
- Support for [SMTLib 2.6](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-draft-3.pdf).
- Theories of Bitvectors and Arrays.
- Eventually be able to keep up with other SMT solvers like STP.
- C API to enable bindings for other languages.
- Incremental solving of problem instances.
- Comprehensive documentation for all important parts of the code.
