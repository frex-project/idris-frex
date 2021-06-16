# Frex: programming with equations using free extensions
https://www.cl.cam.ac.uk/~jdy22/projects/frex/

Frex offers a new approach to synthesising algebraic proofs in
dependently-typed programming languages, based on free extensions from
universal algebra.  Frex provides a common interface to algebraic
reasoning, supporting the construction of terms from variables and
operations, then automatically extending built-in propositional
equality to support user-defined equations.

Architecture
------------

The library has two parts:

* Core frex (`src/Frex`)

  The basic definitions and concepts revolving free extensions.

* Notation (`src/Notation`)

  A hierarchy of notation in algebraic structures.

* Frexlets (`src/Frexlet`)

  An extensible collection of instances of the basic definitions
  covering common algebraic structures.

[![Ubuntu](https://github.com/frex-project/idris-frex/actions/workflows/ci-ubuntu.yml/badge.svg)](https://github.com/frex-project/idris-frex/actions/workflows/ci-ubuntu.yml)
