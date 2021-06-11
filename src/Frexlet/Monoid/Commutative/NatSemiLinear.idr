||| Every commutative monoid has is acted on by the natural numbers semiring
||| making it what ought to be called a semi-linear space
module Frexlet.Monoid.Commutative.NatSemiLinear

import Frex

import Notation
import Notation.Action

import Frexlet.Monoid.Commutative.Theory
import Frexlet.Monoid.Commutative.Notation.Core
import Data.Vect.Properties

import Syntax.PreorderReasoning.Generic

%default total

public export
(.sum) : (a : CommutativeMonoid) -> Vect n (U a) -> U a
(.sum) a xs = let _ : Additive (U a) = Prelude.cast (Core.Model.cast a) in
  case xs of
    [] => O
    (x :: xs) => x + a.sum xs

public export
mult : (a : CommutativeMonoid) -> Nat -> U a -> U a
mult a n x = let _ : Additive1 (U a) = Prelude.cast (Core.Model.cast a)
           in a.sum $ replicate n x

public export
NatActionData : (a : CommutativeMonoid) -> ActionData Nat (U a)
NatActionData a = mult a :: cast a

public export
NatAction1 : (a : CommutativeMonoid) -> Action1 Nat (U a)
NatAction1 a = cast (NatActionData a)

public export
NatAction2 : (a : CommutativeMonoid) -> Action2 Nat (U a)
NatAction2 a = cast (NatActionData a)


public export
sumZeroZero : (a : CommutativeMonoid) -> (n : Nat) -> 
  let %hint notation : Action1 Nat (U a)
      notation = NatAction1 a in
  (cast a).equivalence.relation
    (a.sum (replicate n O1))
    O1
sumZeroZero a 0 = reflect (cast a) Refl
sumZeroZero a (S n) = 
  let %hint notation : Action1 Nat (U a)--, forall x. Action1 Nat (Term Signature x))
      notation = NatAction1 a --, NatAction1 (Free Signature (cast x)))
  in CalcWith @{cast a} $
  |~ a.sum (replicate (S n) O1)
  ~~ O1 .+. a.sum (replicate n O1) ...(Refl)
  <~ O1 .+. O1                     ...(a.Algebra.congruence Plus [_,_] [_,_]  \case
                                         0 => reflect (cast a) Refl
                                         1 => sumZeroZero a n)
  <~ O1                            ...(a.Validate (Mon LftNeutrality) (const _))
  
