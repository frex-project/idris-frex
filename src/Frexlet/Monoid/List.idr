||| Monoid structures over Lists 
module Frexlet.Monoid.List

import Frex
import Frexlet.Monoid.Theory

import public Data.List
import public Data.Setoid.List
        
%default total

||| Monoid structure over lists with catenation
public export
ListMonoid : {A:Setoid} -> Monoid
ListMonoid = MkModel
  { Algebra = MkSetoidAlgebra
      { algebra = MkAlgebra
        { U = List (U A)
        , Sem = \case
           Neutral => []
           Product => (++) }
        , equivalence = (ListSetoid A) .equivalence
        , congruence = \case
          MkOp Neutral => \_,_,_ => (ListSetoid A).equivalence.reflexive _
          MkOp Product => \[x1,x2], [y1,y2], idx => appendCongruence x1 x2 y1 y2 (idx 0) (idx 1) }
  , Validate = \case
      LftNeutrality => \env => A .ListEqualityReflexive (env 0)
      RgtNeutrality => \env => reflect (ListSetoid A) (appendNilRightNeutral (env 0))
      Associativity => \env => reflect (ListSetoid A) (Data.List.appendAssociative (env 0) (env 1) (env 2))
  }
