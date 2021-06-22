||| Properties involving involutive monoids
module Frexlet.Monoid.Involutive.Properties

import Frex
import Frex.Algebra
import Frex.Model

import public Frexlet.Monoid.Involutive.Theory
import public Frexlet.Monoid.Involutive.Notation

import Frexlet.Monoid
import Frexlet.Monoid.Theory
import Frexlet.Monoid.Notation
import Frexlet.Monoid.Frex

import Notation
import Notation.Multiplicative
import Notation.Additive
import Frex.Axiom

public export
FrexInvMonoid : (a : InvolutiveMonoid) -> (s : Setoid) -> Monoid
FrexInvMonoid a s = FrexMonoid (cast a) (cast Bool `Pair` s)

public export
invNeutral : (a : InvolutiveMonoid) ->
  let %hint
      notation : InvMult1 (U a)
      notation = a.Notation1
  in a.rel
    (I1).inv
    I1

invNeutral a = 
  let %hint
      notation : InvMult1 (U a)
      notation = a.Notation1
  in CalcWith @{cast a} $
  |~ (I1).inv
  <~ (I1).inv .*.  I1          ...(a.equivalence.symmetric _ _ $ 
                                   a.validate (Mon RgtNeutrality) [_])
  <~ (I1).inv .*. (I1).inv.inv ...(a.equivalence.symmetric _ _ $
                                   a.cong 1 (Sta (I1).inv .*. Dyn 0) [_] [_]
                                  [a.validate Involutivity [_]])
  <~ ((I1).inv .*. I1).inv     ...( a.equivalence.symmetric _ _ $
                                    a.validate Antidistributivity [(I1).inv, I1])
  <~ (I1).inv.inv              ...(a.cong 1 (Dyn 0).inv [_] [_]
                                  [a.validate (Mon RgtNeutrality) [_]])
  <~ I1                        ...(a.validate Involutivity [_])
