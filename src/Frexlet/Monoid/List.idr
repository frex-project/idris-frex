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

public export
assocAppend : {A:Setoid} -> (xs, ys, zs : List (U A)) -> A .ListEquality (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs)
assocAppend [] ys zs = A .ListEqualityReflexive _
assocAppend (x::xs) ys zs = prodCong [x] _ [x] _ (A .ListEqualityReflexive _) (assocAppend xs ys zs)

public export
leftAppendNeutral : {A:Setoid} -> (x : List (U A)) -> A .ListEquality ([] ++ x) x
leftAppendNeutral = A .ListEqualityReflexive

public export
rightAppendNeutral : {A:Setoid} -> (xs : List (U A)) -> A .ListEquality (xs ++ []) xs
rightAppendNeutral [] = A .ListEqualityReflexive []
rightAppendNeutral (x::xs) = prodCong [x] _ [x] _ (A .ListEqualityReflexive _) (rightAppendNeutral xs)


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
      LftNeutrality => \env => leftAppendNeutral (env 0)
      RgtNeutrality => \env => rightAppendNeutral (env 0)
      Associativity => \env => assocAppend (env 0) (env 1) (env 2)
  }
