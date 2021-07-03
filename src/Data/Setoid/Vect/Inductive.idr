||| The setoid of vectors over a given setoid, defined inductively
module Data.Setoid.Vect.Inductive

import Data.Setoid.Definition

import Data.Vect
import Data.HVect
import Data.Vect.Properties

%default total

public export
data (.VectEquality) : (a : Setoid) -> Rel (Vect n (U a)) where
  Nil : a.VectEquality [] []
  (::) : (hdEq : a.equivalence.relation x y) ->
         (tlEq : a.VectEquality xs ys) ->
         a.VectEquality (x :: xs) (y :: ys)

export
(++) : a.VectEquality xs ys -> a.VectEquality as bs ->
       a.VectEquality (xs ++ as) (ys ++ bs)
[] ++ qs = qs
(p :: ps) ++ qs = p :: (ps ++ qs)

public export
(.VectEqualityReflexive) : (a : Setoid) -> (xs : Vect n $ U a) -> a.VectEquality xs xs
a.VectEqualityReflexive [] = []
a.VectEqualityReflexive (x :: xs) = a.equivalence.reflexive x :: a.VectEqualityReflexive xs

public export
(.VectEqualitySymmetric) : (a : Setoid) -> (xs,ys : Vect n $ U a) -> (prf : a.VectEquality xs ys) ->
  a.VectEquality ys xs
a.VectEqualitySymmetric [] [] [] = []
a.VectEqualitySymmetric (x :: xs) (y :: ys) (hdEq :: tlEq)
  = a.equivalence.symmetric x y hdEq :: a.VectEqualitySymmetric xs ys tlEq

public export
(.VectEqualityTransitive) : (a : Setoid) -> (xs,ys,zs : Vect n $ U a) ->
  (prf1 : a.VectEquality xs ys) -> (prf2 : a.VectEquality ys zs) ->
  a.VectEquality xs zs
a.VectEqualityTransitive [] [] [] [] [] = []
a.VectEqualityTransitive (x :: xs) (y :: ys) (z :: zs) (hdEq1 :: tlEq1) (hdEq2 :: tlEq2)
  = a.equivalence.transitive x  y  z  hdEq1 hdEq2 ::
    a.VectEqualityTransitive xs ys zs tlEq1 tlEq2

public export
VectSetoid : (n : Nat) -> (a : Setoid) -> Setoid
VectSetoid n a = MkSetoid (Vect n (U a))
  $ MkEquivalence
  { relation   = a.VectEquality
  , reflexive  = a.VectEqualityReflexive
  , symmetric  = a.VectEqualitySymmetric
  , transitive = a.VectEqualityTransitive
  }

public export
VectMapFunctionHomomorphism : (f : a ~> b) ->
  SetoidHomomorphism (VectSetoid n a) (VectSetoid n b) (map f.H)
VectMapFunctionHomomorphism f [] [] [] = []
VectMapFunctionHomomorphism f (x :: xs) (y :: ys) (hdEq :: tlEq) =
  f.homomorphic x y hdEq :: VectMapFunctionHomomorphism f xs ys tlEq

public export
VectMapHomomorphism : (f : a ~> b) -> (VectSetoid n a ~> VectSetoid n b)
VectMapHomomorphism f = MkSetoidHomomorphism (map f.H) (VectMapFunctionHomomorphism f)

public export
VectMapIsHomomorphism : SetoidHomomorphism (a ~~> b) (VectSetoid n a ~~> VectSetoid n b)
  VectMapHomomorphism
VectMapIsHomomorphism f g f_eq_g [] = []
VectMapIsHomomorphism f g f_eq_g (x :: xs) = f_eq_g x :: VectMapIsHomomorphism f g f_eq_g xs

public export
VectMap : {0 a, b : Setoid} -> (a ~~> b) ~> (VectSetoid n a ~~> VectSetoid n b)
VectMap = MkSetoidHomomorphism
  { H           = VectMapHomomorphism
  , homomorphic = VectMapIsHomomorphism
  }
