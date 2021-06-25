||| Basic definition and notation for setoids
module Data.Setoid.Definition

import public Syntax.PreorderReasoning.Generic
import public Decidable.Order
import public Data.Relation

infix 5 ~>, ~~>, <~>

public export
record Equivalence (A : Type) where
  constructor MkEquivalence
  0 relation  : Rel A
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
record PreorderData A (rel : Rel A) where
  constructor MkPreorderData
  reflexive : (x : A) -> rel x x
  transitive : (x,y,z : A) -> rel x y -> rel y z -> rel x z

public export
[MkPreorderWorkaround] {x : PreorderData a rel} -> Preorder a rel where
  transitive = x.transitive
  reflexive  = x.reflexive

public export
reflect : (a : Setoid) -> {x, y : U a} -> x = y -> a.equivalence.relation x y
reflect a Refl = a.equivalence.reflexive _

public export
MkPreorder : {0 a : Type} -> {0 rel : Rel a}
  -> (reflexive : (x : a) -> rel x x)
  -> (transitive : (x,y,z : a) -> rel x y -> rel y z -> rel x z)
  -> Preorder a rel
MkPreorder reflexive transitive = MkPreorderWorkaround {x = MkPreorderData reflexive transitive}

public export
cast : (a : Setoid) -> Preorder (U a) (a.equivalence.relation)
cast a = MkPreorder a.equivalence.reflexive a.equivalence.transitive

namespace ToSetoid
  public export
  irrelevantCast : (0 a : Type) -> Setoid
  irrelevantCast a = MkSetoid a (EqualEquivalence a)

public export
Cast Type Setoid where
  cast a = irrelevantCast a

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

public export
mate : {b : Setoid} -> (a -> U b) -> (cast a ~> b)
mate f = MkSetoidHomomorphism f \x,y, prf => reflect b (cong f prf)

||| Identity Setoid homomorphism
public export
id : (a : Setoid) -> a ~> a
id a = MkSetoidHomomorphism Prelude.id \x, y, prf => prf

||| Composition of Setoid homomorphisms
public export
(.) : {a,b,c : Setoid} -> b ~> c -> a ~> b -> a ~> c
g . f = MkSetoidHomomorphism (H g . H f) \x,y,prf => g.homomorphic _ _ (f.homomorphic _ _ prf)

public export
(~~>) : (a,b : Setoid) -> Setoid
%unbound_implicits off
(~~>) a b = MkSetoid (a ~> b)
  let 0 relation : (f, g : a ~> b) -> Type
      relation f g = (x : U a) -> b.equivalence.relation (f.H x) (g.H x)
  in MkEquivalence
  { relation
  , reflexive = \f,v => b.equivalence.reflexive (f.H v)
  , symmetric = \f,g,prf,w => b.equivalence.symmetric _ _ (prf w)
  , transitive = \f,g,h,f_eq_g, g_eq_h, q => b.equivalence.transitive _ _ _ (f_eq_g q) (g_eq_h q)
  }
%unbound_implicits on


||| Two setoid homomorphism are each other's inverses
public export
record Isomorphism {a, b : Setoid} (Fwd : a ~> b) (Bwd : b ~> a) where
  constructor IsIsomorphism
  BwdFwdId : (a ~~> a).equivalence.relation (Bwd . Fwd) (id a)
  FwdBwdId : (b ~~> b).equivalence.relation (Fwd . Bwd) (id b)

||| Setoid isomorphism
public export
record (<~>) (a, b : Setoid) where
  constructor MkIsomorphism
  Fwd : a ~> b
  Bwd : b ~> a

  Iso : Isomorphism Fwd Bwd


||| Reverse an isomorphism
public export
sym : a <~> b -> b <~> a
sym iso = MkIsomorphism iso.Bwd iso.Fwd (IsIsomorphism iso.Iso.FwdBwdId iso.Iso.BwdFwdId)

||| Quotient a type by an function into a setoid
|||
||| Instance of the more general coequaliser of two setoid morphisms.
public export
Quotient : (0 a : Type) -> {b : Setoid} -> (a -> U b) -> Setoid
Quotient a {b} q = MkSetoid a
  let 0 Relation : a -> a -> Type
      Relation x y = b.equivalence.relation
        (q x)
        (q y)
  in MkEquivalence
    { relation = Relation
    , reflexive = \x => b.equivalence.reflexive (q x)
    , symmetric =  \x,y=> b.equivalence.symmetric (q x) (q y)
    , transitive = \x,y,z  => b.equivalence.transitive (q x) (q y) (q z)
    }
