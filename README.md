# Toy implementation of OutsideIn(X)

[![Actions Status](https://github.com/coord-e/impl-outsidein/workflows/CI/badge.svg)](https://github.com/coord-e/impl-outsidein/actions?workflow=CI)

This repository contains the toy implementation of OutsideIn(X) type inference algorithm[[1]](#1), along with the following instantiation of constraint domain X:

- [`SimpleUnification`](src/Language/Simple/ConstraintDomain/SimpleUnification.hs): Solve equality constraints by unification.
- [`TypeClass`](src/Language/Simple/ConstraintDomain/TypeClass.hs): Solve equality and type class constraints.
- [`TypeClassTypeFamily`](src/Language/Simple/ConstraintDomain/TypeClassTypeFamily): Solve equality and type class constraints involving type families with the algorithm described in §7 of [[1]](#1).

## Bibliography

- <a id="1">[1]</a> Vytiniotis, Dimitrios, et al. "OutsideIn (X) Modular type inference with local assumptions." Journal of functional programming 21.4-5 (2011): 333-412.
