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

import Frex.Free
import Frex.Free.Construction

import Frexlet.Monoid.Commutative.NatSemiLinear.Sum

%default total

-- ----------------------------------------------------------------- --- [Mult]

public export
multUnit : (a : CommutativeMonoid) -> 
  let %hint 
      notation : Action1 Nat (U a)
      notation = NatAction1 a 
  in  (x : U a) -> a.rel (the Nat 1 *. x)
                                       x
multUnit a x = 
  let %hint 
      notation : Action1 Nat (U a)
      notation = NatAction1 a 
  in CalcWith @{cast a} $
  |~ the Nat 1 *. x
  ~~ x .+. O1  ...(Refl)
  <~ x         ...(a.Validate (Mon RgtNeutrality) (flip index [_]))
  

