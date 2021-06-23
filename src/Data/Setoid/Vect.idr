||| The setoid of vectors over a given setoid
module Data.Setoid.Vect

import Data.Setoid.Definition

import Data.Vect
import Data.HVect
import Data.Vect.Properties


public export
VectSetoid : (n : Nat) -> (a : Setoid) -> Setoid
VectSetoid n a = MkSetoid (Vect n (U a))
  -- need a local definition, see #1435
  let 0 Relation : (xs, ys : Vect n (U a)) -> Type
      Relation xs ys = (i : Fin n) -> a.equivalence.relation (index i xs) (index i ys)
  in MkEquivalence
  { relation   = Relation
  , reflexive  = \xs                    , i => a.equivalence.reflexive  _
  , symmetric  = \xs,ys, prf            , i => a.equivalence.symmetric  _ _   (prf  i)
  , transitive = \xs, ys, zs, prf1, prf2, i => a.equivalence.transitive _ _ _ (prf1 i) (prf2 i)
  }


public export
VectMap : {a, b : Setoid} -> (a ~~> b) ~> ((VectSetoid n a) ~~> (VectSetoid n b))
VectMap = MkSetoidHomomorphism
  (\f => MkSetoidHomomorphism
            (\xs => map f.H xs)
            \xs, ys, prf, i  => CalcWith @{cast b} $
              |~ index i (map f.H xs)
              ~~ f.H (index i xs)     ...(indexNaturality _ _ _)
              <~ f.H (index i ys)     ...(f.homomorphic _ _ (prf i))
              ~~ index i (map f.H ys) ...(sym $ indexNaturality _ _ _))
  \f,g,prf,xs,i => CalcWith @{cast b} $
    |~ index i (map f.H xs)
    ~~ f.H (index i xs) ...(indexNaturality _ _ _)
    <~ g.H (index i xs) ...(prf _)
    ~~ index i (map g.H xs) ...(sym $ indexNaturality _ _ _)
