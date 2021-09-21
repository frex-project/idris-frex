module Frexlet.Monoid.Involutive.List

import Frex
import Frexlet.Monoid.Involutive.Theory
import Frexlet.Monoid
import Data.Setoid
import Data.List

%default total

public export
List : {A: Setoid} -> InvolutiveMonoid
List = MkModel (MkInvolutiveMonoidStructure ((ListMonoid {A}) .Algebra)
                 (MkSetoidHomomorphism List.reverse reverseHomomorphic))
  $ \case
     (Mon LftNeutrality) => ListMonoid .Validate LftNeutrality
     (Mon RgtNeutrality) => ListMonoid .Validate RgtNeutrality
     (Mon Associativity) => ListMonoid .Validate Associativity
     Involutivity        => \env => reflect (ListSetoid A) (reverseInvolutive (env 0))
     Antidistributivity  => \env => reflect (ListSetoid A) (sym (revAppend (env 0) (env 1)))
