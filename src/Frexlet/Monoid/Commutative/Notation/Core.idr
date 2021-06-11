||| Notational conventions for commutative monoid
module Frexlet.Monoid.Commutative.Notation.Core

import Frex
import Frexlet.Monoid.Commutative.Theory

import public Notation
import public Data.HVect

namespace Algebra
  public export
  cast : (a : MonoidStructure) -> HVect [0 `ary` U a, 2 `ary` U a]
  cast a = [ a.sem Neutral
           , a.sem Product
           ]

namespace Model
  public export
  cast : (a : CommutativeMonoid) -> HVect [0 `ary` U a, 2 `ary` U a]
  cast a = cast (a.Algebra)

