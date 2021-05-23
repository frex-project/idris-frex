||| A setoid is a type equipped with an equivalence relation
module Data.Setoid

import public Syntax.PreorderReasoning.Generic
import Decidable.Order

import Data.Vect
import Data.HVect

public export
record Equivalence (A : Type) where
  constructor MkEquivalence
  0 relation  : (x,y : A) -> Type
  reflexive : (x : A) 
              ----------------
           -> relation x x 
  symmetric : (x : A) -> (y : A) 
              -> relation x y 
              --------------------
              -> relation y x
  transitive: (x : A) -> (y : A) -> (z : A)
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
record PreorderData A (rel : A -> A -> Type) where
  constructor MkPreorderData
  reflexive : (x : A) -> rel x x
  transitive : (x,y,z : A) -> rel x y -> rel y z -> rel x z

public export
[MkPreorderWorkaround] {x : PreorderData a rel} -> Preorder a rel where
  transitive = x.transitive
  reflexive  = x.reflexive

public export
MkPreorder : {0 a : Type} -> {0 rel : a -> a -> Type} 
  -> (reflexive : (x : a) -> rel x x)
  -> (transitive : (x,y,z : a) -> rel x y -> rel y z -> rel x z)
  -> Preorder a rel
MkPreorder reflexive transitive = MkPreorderWorkaround {x = MkPreorderData reflexive transitive}

public export
cast : (a : Setoid) -> Preorder (U a) (a.equivalence.relation)
cast a = MkPreorder a.equivalence.reflexive a.equivalence.transitive

public export
Cast Type Setoid where
  cast a = MkSetoid a (EqualEquivalence a)

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

infix 5 ~>, ~~>


public export 0
SetoidHomomorphism : (a,b : Setoid) -> (f : U a -> U b) -> Type
SetoidHomomorphism a b f 
  = (x,y : U a) -> a.equivalence.relation x y 
  -> b.equivalence.relation (f x) (f y)

public export
record (~>) (A,B : Setoid) where
  constructor MkSetoidHomomorphism
  H : U A -> U B
  homomorphic : SetoidHomomorphism A B H

public export 0
(~~>) : (a,b : Setoid) -> Setoid
%unbound_implicits off
(~~>) a b = MkSetoid (a ~> b) 
  let 0 relation : (f, g : a ~> b) -> Type
      relation f g = (x : U a) -> b.equivalence.relation (H f x) (H g x)
  in MkEquivalence
  { relation
  , reflexive = \f,x => b.equivalence.reflexive _
  , symmetric = \f,g,prf,x => b.equivalence.symmetric _ _ (prf x)
  , transitive = \f,g,h,f_eq_g, g_eq_h, x => b.equivalence.transitive _ _ _ (f_eq_g x) (g_eq_h x)
  }
%unbound_implicits on

