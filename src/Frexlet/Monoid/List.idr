||| Monoid structures over Lists 
module Frexlet.Monoid.List

import Frex
import Frexlet.Monoid.Theory

import public Data.List
import public Data.Setoid.List
        
%default total

public export
prodCong : {A:Setoid} -> (x1, x2, y1, y2 : List (U A)) ->
  A .ListEquality x1 y1 -> A .ListEquality x2 y2 -> A .ListEquality (x1 ++ x2) (y1 ++ y2)
prodCong [] x2 [] y2 Nil p = p
prodCong (x::xs) x2 (y::ys) y2 (ph::pt) p = ph :: prodCong _ _ _ _ pt p

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
          MkOp Product => \[x1,x2], [y1,y2], idx => prodCong x1 x2 y1 y2 (idx 0) (idx 1) }
  , Validate = \case
      LftNeutrality => \env => A .ListEqualityReflexive (env 0)
      RgtNeutrality => \env => reflect (ListSetoid A) (appendNilRightNeutral (env 0))
      Associativity => \env => reflect (ListSetoid A) (Data.List.appendAssociative (env 0) (env 1) (env 2))
  }
