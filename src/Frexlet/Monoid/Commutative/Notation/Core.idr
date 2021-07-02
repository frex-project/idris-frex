||| Notational conventions for commutative monoid
module Frexlet.Monoid.Commutative.Notation.Core

import Frex
import Frexlet.Monoid.Commutative.Theory

import public Notation
import public Notation.Action
import public Data.HVect
import public Frex.Free
import public Frex.Free.Construction

%default total

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

public export
(.sum) : (a : CommutativeMonoid) -> Vect n (U a) -> U a
(.sum) a xs = let _ : Additive1 (U a) = Prelude.cast (Core.Model.cast a) in
  case xs of
    [] => O1
    (x :: xs) => x .+. a.sum xs

public export
mult : (a : CommutativeMonoid) -> Nat -> U a -> U a
mult a n x = a.sum $ replicate n x

public export
NatActionData : (a : CommutativeMonoid) -> ActionData Nat (U a)
NatActionData a = mult a :: cast a

public export
NatAction1 : (a : CommutativeMonoid) -> Action1 Nat (U a)
NatAction1 a = cast (NatActionData a)

public export
NatAction2 : (a : CommutativeMonoid) -> Action2 Nat (U a)
NatAction2 a = cast (NatActionData a)

%hint
public export
notation2 : Action2 Nat (Term Signature (a `Either` (Fin n)))
notation2 = NatAction2 (F _ (irrelevantCast (a `Either` (Fin n))))

%hint
public export
notation1 : Action1 Nat (Term Signature (a `Either` (Fin n)))
notation1 = NatAction1 (F _ (irrelevantCast (a `Either` (Fin n))))
