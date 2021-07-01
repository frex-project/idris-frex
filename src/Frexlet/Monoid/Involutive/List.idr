module Frexlet.Monoid.Involutive.List

import Frex
import Frexlet.Monoid.Involutive.Theory
import Frexlet.Monoid
import Data.Setoid
import Data.List

%default total

reverseHomomorphic : {A : Setoid} -> (x, y : List (U A)) -> (A .ListEquality x y) -> A .ListEquality (reverse x) (reverse y)
reverseHomomorphic l1 l2 prf = roh [] [] l1 l2 (A .ListEqualityReflexive _) prf
  where roh  : {A : Setoid} -> (w, x, y, z : List (U A)) -> (A .ListEquality w x) ->(A .ListEquality y z) ->
               A .ListEquality (reverseOnto w y) (reverseOnto x z)
        roh w x [] [] yz Nil = yz
        roh w x (y::ys) (z::zs) wx (yzh :: yzt) = roh (y::w) (z::x) ys zs (yzh :: wx) yzt

public export
List : {A: Setoid} -> InvolutiveMonoid
List = MkModel (MkInvolutiveMonoidStructure ((ListMonoid {A}) .Algebra)
                 (MkSetoidHomomorphism Data.List.reverse reverseHomomorphic))
  $ \case
     (Mon LftNeutrality) => ListMonoid .Validate LftNeutrality
     (Mon RgtNeutrality) => ListMonoid .Validate RgtNeutrality
     (Mon Associativity) => ListMonoid .Validate Associativity
     Involutivity        => \env => reflect (ListSetoid A) (reverseInvolutive (env 0))
     Antidistributivity  => \env => reflect (ListSetoid A) (sym (revAppend (env 0) (env 1)))
