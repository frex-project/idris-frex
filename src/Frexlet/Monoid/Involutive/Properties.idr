||| Properties involving involutive monoids
module Frexlet.Monoid.Involutive.Properties

import Frex

import public Frexlet.Monoid.Involutive.Theory
import public Frexlet.Monoid.Involutive.Notation

import Frexlet.Monoid
import Frexlet.Monoid.Frex

import Notation
import Notation.Multiplicative

public export
FrexInvMonoid : (a : InvolutiveMonoid) -> (s : Setoid) -> Monoid
FrexInvMonoid a s = FrexMonoid (cast a) (cast Bool `Pair` s)

