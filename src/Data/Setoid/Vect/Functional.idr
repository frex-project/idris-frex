||| The setoid of vectors over a given setoid, defined using a function
module Data.Setoid.Vect.Functional

import Data.Setoid.Definition

import Data.Vect
import Data.HVect
import Data.Vect.Properties
import Data.Setoid.Vect.Inductive
import Control.Order
import Syntax.PreorderReasoning.Setoid


%default total

public export
0 (.VectEquality) : (a : Setoid) -> Rel (Vect n (U a))
a.VectEquality xs ys = (i : Fin n) ->
  a.equivalence.relation (index i xs) (index i ys)

-- Not using the more sensible type definition
-- Inductive.(.VectEquality) a xs ys -> Functional.(.VectEquality) a xs ys
-- so that the arguments are in the order as Vect's index.
export
index : (i : Fin n) ->
        Inductive.(.VectEquality) a xs ys ->
        a.equivalence.relation (index i xs) (index i ys)
index FZ     (hdEq :: _) = hdEq
index (FS k) (_ :: tlEq) = index k tlEq

%hide Inductive.(.VectEquality)
%hide Inductive.VectSetoid

public export
VectSetoid : (n : Nat) -> (a : Setoid) -> Setoid
VectSetoid n a = MkSetoid (Vect n (U a))
  $ MkEquivalence
  { relation   = (.VectEquality) a
  , reflexive  = \xs                    , i =>
      a.equivalence.reflexive  _
  , symmetric  = \xs,ys, prf            , i =>
      a.equivalence.symmetric  _ _   (prf  i)
  , transitive = \xs, ys, zs, prf1, prf2, i =>
      a.equivalence.transitive _ _ _ (prf1 i) (prf2 i)
  }

public export
VectMap : {a, b : Setoid} -> (a ~~> b) ~>
  (VectSetoid n a ~~> VectSetoid n b)
VectMap = MkSetoidHomomorphism
  (\f => MkSetoidHomomorphism
    (\xs => map f.H xs)
    $ \xs, ys, prf, i  => CalcWith b $
      |~ index i (map f.H xs)
      ~~ f.H (index i xs)
                          .=.(indexNaturality _ _ _)
      ~~ f.H (index i ys) ...(f.homomorphic _ _ (prf i))
      ~~ index i (map f.H ys)
                          .=<(indexNaturality _ _ _))
  $ \f,g,prf,xs,i => CalcWith b $
    |~ index i (map f.H xs)
    ~~ f.H (index i xs) .=.(indexNaturality _ _ _)
    ~~ g.H (index i xs) ...(prf _)
    ~~ index i (map g.H xs) .=<(indexNaturality _ _ _)
