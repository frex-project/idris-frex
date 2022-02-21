||| Monoid structures over the Nats
module Frexlet.Monoid.Nat

import Frex
import Frexlet.Monoid.Theory

import public Data.Nat

%default total

||| Additive monoid structure over the natural numbers
public export
Additive : Monoid
Additive = MkModel
  { Algebra = cast {from = Algebra Signature} $
              MkAlgebra { U = Nat
                        , Sem = \case
                           Neutral => 0
                           Product => plus
                        }
  , Validate = \case
      LftNeutrality => \env => Refl
      RgtNeutrality => \env => plusZeroRightNeutral _
      Associativity => \env => plusAssociative _ _ _
  }

||| Multiplicative monoid structure over the natural numbers
public export
Multiplicative : Monoid
Multiplicative = MkModel
  { Algebra = cast {from = Algebra Signature} $
      MkAlgebra {U = Nat, Sem = \case Neutral => 1
                                      Product => mult}
  , Validate = \case
      LftNeutrality => \env => plusZeroRightNeutral _
      RgtNeutrality => \env => multOneRightNeutral _
      Associativity => \env => multAssociative _ _ _
  }
