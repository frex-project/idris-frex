||| A setoid is a type equipped with an equivalence relation
module Data.Setoid

import public Syntax.TransitiveReasoning

import Data.Vect
import Data.HVect

public export
record Equivalence (a : Type) where
  constructor MkEquivalence
  relation  : (x,y : a) -> Type
  reflexive : (x : a) 
              ----------------
           -> relation x x 
  symmetric : (x : a) -> (y : a) 
              -> relation x y 
              --------------------
              -> relation y x
  transitive: (x : a) -> (y : a) -> (z : a)
              -> relation x y -> relation y z
              ------------------------------
              -> relation x z

public export
EqualEquivalence : (0 a : Type) -> Equivalence a
EqualEquivalence a = MkEquivalence
  { relation = (===)
  , reflexive = \_ => Refl
  , symmetric = \_,_, Refl => Refl
  , transitive = \_,_,_,Refl,Refl => Refl
  }

public export
record Setoid where
  constructor MkSetoid
  0 U : Type
  equivalence : Equivalence U

public export
cast : (a : Setoid) -> Transitive (U a) (a.equivalence.relation)
cast a = MkTransitive a.equivalence.transitive

public export
Cast Type Setoid where
  cast a = MkSetoid a (EqualEquivalence a)

public export
VectSetoid : (n : Nat) -> (a : Setoid) -> Setoid
VectSetoid n a = MkSetoid (Vect n (U a)) 
  -- need a local definition, see #1435
  let Relation : (xs, ys : Vect n (U a)) -> Type
      Relation xs ys = (i : Fin n) -> a.equivalence.relation (index i xs) (index i ys)
  in MkEquivalence
  { relation   = Relation
  , reflexive  = \xs                    , i => a.equivalence.reflexive  _
  , symmetric  = \xs,ys, prf            , i => a.equivalence.symmetric  _ _   (prf  i)
  , transitive = \xs, ys, zs, prf1, prf2, i => a.equivalence.transitive _ _ _ (prf1 i) (prf2 i)
  }

infix 5 ~>

public export 0
SetoidHomomorphism : (a,b : Setoid) -> (f : U a -> U b) -> Type
SetoidHomomorphism a b f 
  = (x,y : U a) -> a.equivalence.relation x y 
  -> b.equivalence.relation (f x) (f y)
  
public export
record (~>) (a,b : Setoid) where
  constructor MkSetoidHomomorphism
  H : U a -> U b
  homomorphic : SetoidHomomorphism a b H
