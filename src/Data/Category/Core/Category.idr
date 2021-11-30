module Data.Category.Core.Category

import public Data.Setoid
import public Data.Setoid.Pair

import Control.Relation
import Data.Nat
import Data.Vect

%default total

namespace Category
  public export
  record Structure Obj where
    constructor MkStructure
    Arr : (dom, cod : Obj) -> Setoid
    idArr   : {a : Obj} -> U $ Arr a a
    compArr : {a, b, c : Obj} -> (Arr b c `Pair` Arr a b) ~> Arr a c

  public export
  record (.Hom) {0 Obj : Type}
                (cat : Category.Structure Obj) (a, b : Obj) where
    constructor MkHom
    U : U $ cat.Arr a b

  public export
  record (.HomEq) {0 Obj : Type}
         (cat : Category.Structure Obj) (a, b : Obj) (f,g : cat.Hom a b) where
    constructor MkHomEq
    runEq : (cat.Arr a b).equivalence.relation (U f) (U g)

  public export
  (.HomSet) : {0 Obj : Type} ->
              (cat : Category.Structure Obj) -> (a, b : Obj) -> Setoid
  cat.HomSet a b = MkSetoid
    { U = cat.Hom a b
    , equivalence = MkEquivalence
      { relation   = cat.HomEq a b
      , reflexive  = \f       => MkHomEq $ (cat.Arr a b).equivalence.reflexive (U f)
      , symmetric  = \f,g,prf => MkHomEq $ (cat.Arr a b).equivalence.symmetric (U f) (U g) prf.runEq
      , transitive = \f,g,h,f_eq_g,g_eq_h => MkHomEq $
                       (cat.Arr a b).equivalence.transitive (U f) (U g) (U h)
                         f_eq_g.runEq g_eq_h.runEq
      }
    }

  public export
  Id : {cat : Structure obj} -> {a : obj} -> cat.Hom a a
  Id = MkHom cat.idArr

  public export
  (.) : {cat : Structure obj} -> {a, b, c : obj} ->
    (g : cat.Hom b c) -> (f : cat.Hom a b) ->
    cat.Hom a c
  g . f = MkHom (cat.compArr.H (U g , U f))

  public export
  record Laws {Obj : Type} (Cat : Structure Obj) where
    constructor Check
    idRgtNeutral : {a,b : Obj} -> (f : Cat .Hom a b) ->
      (Cat .HomSet a b).equivalence.relation
        (f . Id)
        f
    idLftNeutral : {a,b : Obj} -> (f : Cat .Hom a b) ->
      (Cat .HomSet a b).equivalence.relation
        (Id . f)
        f
    associativity : {a,b,c,d : Obj} ->
      (f : Cat .Hom c d) -> (g : Cat .Hom b c) -> (h : Cat .Hom a b) ->
      (Cat .HomSet a d).equivalence.relation
        ( f . (g . h))
        ((f .  g). h )

public export
record Category where
  constructor MkCategory
  0 Obj : Type
  structure : Structure Obj
  laws : Laws structure

public export
(.HomSet) : (cat : Category) -> (a, b : cat.Obj) -> Setoid
cat.HomSet a b = cat.structure.HomSet a b

public export
(.Hom) : (cat : Category) -> (a, b : cat.Obj) -> Type
cat.Hom a b = cat.structure.Hom a b

-- A bit crazy but:
-- since we often give objects as implicit arguments in types, and since we
-- often define record fields of these types using anonymous functions, and
-- idris2 doesn't have any syntax for implicit arguments in anonymous functions
-- it's useful to be able to project out the domain and codomain of a morphism.

public export
(.src),(.tgt) : {0 c : Category} -> {a,b : c.Obj} -> (c.Hom a b) -> c.Obj
(u.src) {a} = a
(u.tgt) {b} = b

public export
(.cong) : (cat : Category) -> {a,b,c : cat.Obj} ->
  SetoidHomomorphism (cat.HomSet b c `Pair` cat.HomSet a b) (cat.HomSet a c)
    (\uv => fst uv . snd uv)
cat.cong (u1,u2) (v1,v2) prf = MkHomEq $ cat.structure.compArr.homomorphic
  (U u1, U u2) (U v1, U v2) (MkAnd prf.fst.runEq prf.snd.runEq)

public export
MkHomHomo : {c : Category} -> {a,b : c.Obj} ->
  (c.structure.Arr a b)  ~> c.HomSet a b
MkHomHomo = MkSetoidHomomorphism
  { H = MkHom
  , homomorphic = \uv1,uv2 => MkHomEq
  }

public export
UHomo : {c : Category} -> {a,b : c.Obj} ->
  c.HomSet a b ~> (c.structure.Arr a b)
UHomo = MkSetoidHomomorphism
  { H = U
  , homomorphic = \uv1,uv2,prf => prf.runEq
  }


public export
HomArrIso : {c : Category} -> {a,b : c.Obj} ->
  c.HomSet a b <~> c.structure.Arr a b
HomArrIso = MkIsomorphism
  { Fwd = UHomo
  , Bwd = MkHomHomo
  , Iso = IsIsomorphism
      { FwdBwdId = (c.structure.Arr a b).equivalence.reflexive
      , BwdFwdId = \(MkHom u) => (c       .HomSet a b).equivalence.reflexive _
      }
  }

namespace CongTgt
  public export
  (.) : {cat : Category} -> {a,b,c : cat.Obj} ->
    {u1, u2 : cat.Hom b c} ->
    (cat.HomSet b c).equivalence.relation u1 u2 ->
    (v : cat.Hom a b) ->
    (cat.HomSet a c).equivalence.relation
      (u1 . v)
      (u2 . v)
  prf . v = cat.cong (u1, v) (u2, v)
          $ MkAnd prf $ (cat.HomSet _ _).equivalence.reflexive _

namespace CongSrc
  public export
  (.) : {cat : Category} -> {a,b,c : cat.Obj} ->
    (u : cat.Hom b c) ->
    {v1, v2 : cat.Hom a b} ->
    (cat.HomSet a b).equivalence.relation v1 v2 ->
    (cat.HomSet a c).equivalence.relation
      (u . v1)
      (u . v2)
  u . prf = cat.cong (u, v1) (u, v2)
          $ MkAnd ((cat.HomSet _ _).equivalence.reflexive _) prf

infixr 9 .:.

namespace CongBoth
  public export
  (.:.) : {cat : Category} -> {a,b,c : cat.Obj} ->
    {u1, u2 : cat.Hom b c} ->
    (cat.HomSet b c).equivalence.relation u1 u2 ->
    {v1, v2 : cat.Hom a b} ->
    (cat.HomSet a b).equivalence.relation v1 v2 ->
    (cat.HomSet a c).equivalence.relation
      (u1 . v1)
      (u2 . v2)
  prf1 .:. prf2 = cat.cong (u1, v1) (u2, v2)
          $ MkAnd prf1 prf2

public export
record (.Isomorphism) (cat : Category) {a,b : cat.Obj}
  (into : cat.Hom a b) (from : cat.Hom b a) where
  constructor MutuallyInverse
  IntoFromId : (cat.HomSet _ _).equivalence.relation
    (into . from)
    Id
  FromIntoId : (cat.HomSet _ _).equivalence.relation
    (from . into)
    Id
%unbound_implicits off
public export
record (.Invertible) (cat : Category) {a,b : cat.Obj}  (u : cat.Hom a b) where
  constructor IsInvertible
  inverse : cat.Hom b a
  isInverse : cat.Isomorphism u inverse
%unbound_implicits on
