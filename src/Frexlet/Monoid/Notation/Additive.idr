||| Additive notation for working with monoids (mostly boilerplate)
module Frexlet.Monoid.Notation.Additive

import Frex

import Frexlet.Monoid.Theory
import public Notation.Additive

%default total

namespace Algebra
  public export
  cast : (a : MonoidStructure) -> HVect [0 `ary` U a, 2 `ary` U a]
  cast a = [ a.sem Neutral
           , a.sem Product
           ]

namespace Model
  public export
  cast : (a : Monoid) -> HVect [0 `ary` U a, 2 `ary` U a]
  cast a = cast (a.Algebra)

public export
(.Additive1) : (monoid : Monoid) -> Additive1 (U monoid)
monoid.Additive1 = MkAdditive1 (monoid.sem Neutral) (monoid.sem Product)

public export
(.Additive2) : (monoid : Monoid) -> Additive2 (U monoid)
monoid.Additive2 = MkAdditive2 (monoid.sem Neutral) (monoid.sem Product)

public export
(.Additive3) : (monoid : Monoid) -> Additive3 (U monoid)
monoid.Additive3 = MkAdditive3 (monoid.sem Neutral) (monoid.sem Product)

%hint
public export
notationAdd1 : Additive1 (Term Signature x)
notationAdd1= MkAdditive1
              (call {sig = Signature} Neutral)
              (call {sig = Signature} Product)

%hint
public export
notationAdd2 : Additive2 (Term Signature x)
notationAdd2 = MkAdditive2
              (call {sig = Signature} Neutral)
              (call {sig = Signature} Product)

%hint
public export
notationAdd3 : Additive3 (Term Signature x)
notationAdd3 = MkAdditive3
              (call {sig = Signature} Neutral)
              (call {sig = Signature} Product)
