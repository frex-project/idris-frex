module Data.Category.Core

import Data.Setoid
import Data.Setoid.Pair

import Control.Relation
import Data.Nat

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
  (.HomSet) : {0 Obj : Type} ->
              (cat : Category.Structure Obj) -> (a, b : Obj) -> Setoid
  cat.HomSet a b = MkSetoid 
    { U = cat.Hom a b
    , equivalence = MkEquivalence
      { relation   = \f,g => (cat.Arr a b).equivalence.relation (U f) (U g)
      , reflexive  = \f => (cat.Arr a b).equivalence.reflexive (U f)
      , symmetric  = \f,g,prf => (cat.Arr a b).equivalence.symmetric (U f) (U g) prf
      , transitive = \f,g,h,f_eq_g,g_eq_h => 
                       (cat.Arr a b).equivalence.transitive (U f) (U g) (U h) f_eq_g g_eq_h
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
    idLftNeutral : {a,b : Obj} -> (f : Cat .Hom a b) ->
      (Cat .HomSet a b).equivalence.relation
        (f . Id)
        f
    idRgtNeutral : {a,b : Obj} -> (f : Cat .Hom a b) ->
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

namespace Functor
  public export
  record Structure (C,D : Category) where
    constructor MkStructure
    mapObj : C .Obj -> D .Obj
    mapHom : {a,b : C .Obj} -> (C .HomSet a b) ~> (D .HomSet (mapObj a) (mapObj b))

  public export
  record Functoriality {C,D : Category} (F : Functor.Structure C D) where
    constructor Check
    idPreserve : (a : C .Obj) -> 
      (D .HomSet _ _).equivalence.relation
        (F .mapHom.H (Id {a}))
        Id

public export
record (~>) (C, D : Category) where
  constructor MkFunctor
  structure : Functor.Structure C D
  functoriality : Functoriality structure

infix 7 !!

public export
(!!) : {c,d : Category} -> (f : c ~> d) -> c.Obj -> d.Obj
(!!) f = f.structure.mapObj

public export
(.map) : {c,d : Category} -> (f : c ~> d) -> {a,b : c.Obj} -> c.Hom a b -> d.Hom (f !! a) (f !! b)
f.map = f.structure.mapHom.H

namespace NatTrans
  public export 0
  Transformation : {c,d : Category} -> (f,g : c ~> d) -> Type
  Transformation f g = (a : c.Obj) -> d.Hom (f !! a) (g !! a)

  public export 0
  Naturality : {c, d : Category} -> {f,g : c ~> d} -> (alpha : Transformation f g) -> Type
  Naturality alpha = {a,b : c.Obj} -> (u : c.Hom a b) ->
    (d.HomSet _ _).equivalence.relation
      (alpha b . f.map u)
      (g.map u . alpha a)

  public export
  record (~>) {C,D : Category} (F, G : C ~> D) where
    constructor MkNatTrans
    (^) : Transformation F G
    naturality : Naturality {f = F, g = G} (^)

