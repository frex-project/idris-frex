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
