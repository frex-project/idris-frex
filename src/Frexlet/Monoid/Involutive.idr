||| An involutive monoid a is a monoid equipped with a unary involution
||| operator .inv : U a -> U a satisfying:
|||
||| x.inv.inv = x
|||
||| (x .*. y).inv = y.inv .*. x.inv
module Frexlet.Monoid.Involutive

import public Frexlet.Monoid.Involutive.Theory
import public Frexlet.Monoid.Involutive.Properties
import public Frexlet.Monoid.Involutive.Involution
import public Frexlet.Monoid.Involutive.Frex

-------
import Frex
import Notation
import Notation.Multiplicative
import Frexlet.Monoid.Involutive.Notation
import Data.Setoid
import Frexlet.Monoid
import Frexlet.Monoid.Theory
import Frexlet.Monoid.Notation

%default total

public export
InvExtender : (a : InvolutiveMonoid) -> (s : Setoid) ->
  Frex.Frex.Extender (InvMonoidExtension a s)
InvExtender a s other = ?h0
  -- This makes the type-checker take forever and gobble up memory
  --MkExtensionMorphism ?h1 ?h2 ?h3
