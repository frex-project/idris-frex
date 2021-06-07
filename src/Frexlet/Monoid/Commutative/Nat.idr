||| CommutativeMonoid structures over the Nats
module Frexlet.Monoid.Commutative.Nat

import Frex
import public Frexlet.Monoid
import Frexlet.Monoid.Nat
import Frexlet.Monoid.Commutative.Theory


import Data.Nat

||| Additive commutative monoid structure over the natural numbers
public export
Additive : CommutativeMonoid
Additive 
  = MkCommutativeMonoid Monoid.Nat.Additive       \env => plusCommutative _ _ 

||| Multiplicative monoid structure over the natural numbers
public export
Multiplicative : CommutativeMonoid
Multiplicative 
  = MkCommutativeMonoid Monoid.Nat.Multiplicative \env => multCommutative _ _ 
