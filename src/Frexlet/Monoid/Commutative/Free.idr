||| An inductive construction of the free commutative monoid over a
||| finite set.
module Frexlet.Monoid.Commutative.Free

import Frex

import Notation
import Notation.Action

import Frexlet.Monoid.Commutative.Theory
import Frexlet.Monoid.Commutative.Notation.Core
import Data.Vect.Properties

import Syntax.PreorderReasoning.Generic
import Syntax.PreorderReasoning

import Frex.Free
import Frex.Free.Construction

import Frexlet.Monoid.Commutative.NatSemiLinear
import Frexlet.Monoid.Commutative.NatSemiLinear

import public Frexlet.Monoid.Commutative.Nat

import Decidable.Equality
import Data.Bool.Decidable

%default total

public export
Model : (n : Nat) -> CommutativeMonoid
Model n = (Commutative.Nat.Additive ^ n).Data.Model

public export
FreeCommutativeMonoidOver : (n : Nat) -> CommutativeMonoidTheory `ModelOver` (cast $ Fin n)
FreeCommutativeMonoidOver n = 
  MkModelOver
  { Model = Model n
  , Env   = mate {b = cast $ Model n} (\i => Fin.tabulate \j => let u = dirac i j in ?h1)
  }
