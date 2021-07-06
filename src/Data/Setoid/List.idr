||| Setoid of lists over a setoid and associated definitions
module Data.Setoid.List

import Data.List
import Data.Setoid.Definition

%default total

namespace Relation
  public export
  data (.ListEquality) : (a : Setoid) -> Rel (List $ U a) where
    Nil : a.ListEquality [] []
    (::) : (hdEq : a.equivalence.relation x y) -> (tlEq : a.ListEquality xs ys) ->
          a.ListEquality (x :: xs) (y :: ys)

public export
(.ListEqualityReflexive) : (a : Setoid) -> (xs : List $ U a) -> a.ListEquality xs xs
a.ListEqualityReflexive [] = []
a.ListEqualityReflexive (x :: xs) = a.equivalence.reflexive x :: a.ListEqualityReflexive xs

public export
(.ListEqualitySymmetric) : (a : Setoid) -> (xs,ys : List $ U a) -> (prf : a.ListEquality xs ys) ->
  a.ListEquality ys xs
a.ListEqualitySymmetric [] [] [] = []
a.ListEqualitySymmetric (x :: xs) (y :: ys) (hdEq :: tlEq)
  = a.equivalence.symmetric x y hdEq :: a.ListEqualitySymmetric xs ys tlEq

public export
(.ListEqualityTransitive) : (a : Setoid) -> (xs,ys,zs : List $ U a) ->
  (prf1 : a.ListEquality xs ys) -> (prf2 : a.ListEquality ys zs) ->
  a.ListEquality xs zs
a.ListEqualityTransitive [] [] [] [] [] = []
a.ListEqualityTransitive (x :: xs) (y :: ys) (z :: zs) (hdEq1 :: tlEq1) (hdEq2 :: tlEq2)
  = a.equivalence.transitive x  y  z  hdEq1 hdEq2 ::
    a.ListEqualityTransitive xs ys zs tlEq1 tlEq2

public export
ListSetoid : (a : Setoid) -> Setoid
ListSetoid a = MkSetoid (List $ U a)
  $ MkEquivalence
  { relation   = a.ListEquality
  , reflexive  = a.ListEqualityReflexive
  , symmetric  = a.ListEqualitySymmetric
  , transitive = a.ListEqualityTransitive
  }

public export
ListMapFunctionHomomorphism : (f : a ~> b) ->
  SetoidHomomorphism (ListSetoid a) (ListSetoid b) (map f.H)
ListMapFunctionHomomorphism f [] [] [] = []
ListMapFunctionHomomorphism f (x :: xs) (y :: ys) (hdEq :: tlEq) =
  f.homomorphic x y hdEq :: ListMapFunctionHomomorphism f xs ys tlEq

public export
ListMapHomomorphism : (f : a ~> b) -> (ListSetoid a ~> ListSetoid b)
ListMapHomomorphism f = MkSetoidHomomorphism (map f.H) (ListMapFunctionHomomorphism f)

public export
ListMapIsHomomorphism : SetoidHomomorphism (a ~~> b) (ListSetoid a ~~> ListSetoid b)
  ListMapHomomorphism
ListMapIsHomomorphism f g f_eq_g [] = []
ListMapIsHomomorphism f g f_eq_g (x :: xs) = f_eq_g x :: ListMapIsHomomorphism f g f_eq_g xs

public export
ListMap : {0 a, b : Setoid} -> (a ~~> b) ~> (ListSetoid a ~~> ListSetoid b)
ListMap = MkSetoidHomomorphism
  { H           = ListMapHomomorphism
  , homomorphic = ListMapIsHomomorphism
  }

public export
reverseHomomorphic : {a : Setoid} -> (x, y : List (U a)) ->
  (a.ListEquality x y) -> a.ListEquality (reverse x) (reverse y)
reverseHomomorphic x y prf = roh [] [] x y (a.ListEqualityReflexive _) prf
  where roh  : (ws, xs, ys, zs : List (U a)) -> a.ListEquality ws xs -> a.ListEquality ys zs ->
               a.ListEquality (reverseOnto ws ys) (reverseOnto xs zs)
        roh ws xs   []      []    wx     []       = wx
        roh ws xs (y::ys) (z::zs) wx (yzh :: yzt) = roh (y::ws) (z::xs) ys zs (yzh :: wx) yzt

public export
appendCongruence : {a : Setoid} -> (x1, x2, y1, y2 : List (U a)) ->
  a.ListEquality x1 y1 -> a.ListEquality x2 y2 -> a.ListEquality (x1 ++ x2) (y1 ++ y2)
appendCongruence   []    x2   []    y2    []    p = p
appendCongruence (x::xs) x2 (y::ys) y2 (ph::pt) p = ph :: appendCongruence _ _ _ _ pt p
