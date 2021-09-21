module Data.Category.Core

import Data.Setoid
import Data.Setoid.Pair

import Control.Relation
import Data.Nat

import Syntax.PreorderReasoning.Generic

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

public export
(.cong) : (cat : Category) -> {a,b,c : cat.Obj} ->
  SetoidHomomorphism (cat.HomSet b c `Pair` cat.HomSet a b) (cat.HomSet a c)
    (\uv => fst uv . snd uv)
cat.cong (u1,u2) (v1,v2) prf = MkHomEq $ cat.structure.compArr.homomorphic
  (U u1, U u2) (U v1, U v2) (MkAnd prf.fst.runEq prf.snd.runEq)

namespace Functor
  public export
  record Structure (C,D : Category) where
    constructor MkStructure
    mapObj : C .Obj -> D .Obj
    mapHom : {a,b : C .Obj} -> (C .HomSet a b) ~> (D .HomSet (mapObj a) (mapObj b))

  public export
  record Functoriality {C,D : Category} (F : Functor.Structure C D) where
    constructor Check
    id : (a : C .Obj) ->
      (D .HomSet _ _).equivalence.relation
        (F .mapHom.H (Id {a}))
        Id
    comp : {a,b,c : C .Obj} -> (f : C .Hom b c) -> (g : C .Hom a b) ->
      (D .HomSet _ _).equivalence.relation
        (F .mapHom.H (f . g))
        (F .mapHom.H f . F .mapHom.H g)

  public export
  record (~>) (C, D : Category) where
    constructor MkFunctor
    structure : Functor.Structure C D
    functoriality : Functoriality structure

  infixr 7 !!

  public export
  (!!) : {c,d : Category} -> (f : c ~> d) -> c.Obj -> d.Obj
  (!!) f = f.structure.mapObj

  public export
  (.mapSetoid) : {c,d : Category} -> (f : c ~> d) -> {a,b : c.Obj} -> c.HomSet a b ~> d.HomSet (f !! a) (f !! b)
  f.mapSetoid = f.structure.mapHom

  public export
  (.map) : {c,d : Category} -> (f : c ~> d) -> {a,b : c.Obj} -> c.Hom a b -> d.Hom (f !! a) (f !! b)
  f.map = f.mapSetoid.H

  public export
  Id : {c : Category} -> c ~> c
  Id = MkFunctor
    { structure = MkStructure
      { mapObj = id
      , mapHom = id _
      }
    , functoriality = Check
      { id   = \a   => (c.HomSet _ _).equivalence.reflexive Id
      , comp = \f,g => (c.HomSet _ _).equivalence.reflexive (f . g)
      }
    }

  public export
  (.) : {a, b, c : Category} -> (f : b ~> c) -> (g : a ~> b) -> a ~> c
  f . g = MkFunctor
    { structure = MkStructure
      { mapObj = (f !!) . (g !!)
      , mapHom = f.mapSetoid . g.mapSetoid
      }
    , functoriality = Check
      { id = \a =>
        CalcWith @{cast $ c.HomSet _ _} $
        |~ f.map (g.map Id)
        <~ f.map Id ...(f.mapSetoid.homomorphic _ Id $
                        g.functoriality.id _)
        <~ Id       ...(f.functoriality.id _)
      , comp = \u,v =>
        CalcWith @{cast $ c.HomSet _ _} $
        |~ f.map (g.map (u . v))
        <~ f.map (g.map u . g.map v)         ...(f.mapSetoid.homomorphic (g.map (u . v)) _ $
                                                 g.functoriality.comp u v)
        <~ f.map (g.map u) . f.map (g.map v) ...(f.functoriality.comp _ _)
      }
    }

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
    transformation : Transformation F G
    naturality : Naturality {f = F, g = G} transformation

  infix 8 ^

  public export
  (^) : {C, D : Category} -> {F, G : C ~> D} -> F ~> G -> Transformation F G
  (^) = (.transformation)

  public export
  Id : {c, d : Category} -> {f : c ~> d} -> f ~> f
  Id = MkNatTrans
    { transformation = \a => Id
    , naturality = \u => CalcWith @{cast $ d.HomSet _ _} $
      |~ (Id . f.map u)
      <~ f.map u        ...(d.laws.idLftNeutral _)
      <~ (f.map u . Id) ...((d.HomSet _ _).equivalence.symmetric _ _ $
                            d.laws.idRgtNeutral _)
    }

  public export
  (.) : {c, d : Category} -> {f,g,h : c ~> d} -> g ~> h -> f ~> g -> f ~> h
  (.) alpha beta = MkNatTrans
    { transformation = \a => (alpha ^ a) . (beta ^ a)
    , naturality = \ u => CalcWith @{cast $ d.HomSet _ _} $
      |~ ((alpha ^ _) . ( beta ^ _)) . f.map u
      <~ ( alpha ^ _) . ((beta ^ _)  . f.map u)  ...((d.HomSet _ _).equivalence.symmetric _ _ $
                                                     d.laws.associativity _ _ _)
      <~ ( alpha ^ _) . ((g.map u) . (beta ^ _)) ...(d.cong (_,_) (_,_) $
                                                     MkAnd
                                                       ((d.HomSet _ _).equivalence.reflexive _)
                                                       $ beta.naturality u)
      <~ ((alpha ^ _) . (g.map u)) . (beta ^ _)  ...(d.laws.associativity _ _ _)
      <~ (h.map u . ( alpha ^ _)) . (beta ^ _)   ...(d.cong (_,_) (_,_) $
                                                     MkAnd
                                                       (alpha.naturality u)
                                                       $ (d.HomSet _ _).equivalence.reflexive _)
      <~ (h.map u . ((alpha ^ _) . ( beta ^ _))) ...((d.HomSet _ _).equivalence.symmetric _ _ $
                                                     d.laws.associativity _ _ _)
    }

  public export 0
  NatTransEq : {c,d : Category} -> (f,g : c ~> d) -> Rel (f ~> g)
  NatTransEq f g alpha beta = (a : c.Obj) -> (d.HomSet _ _).equivalence.relation
                       (alpha ^ a) (beta ^ a)

  public export
  (~~>) : {c,d : Category} -> (f,g : c ~> d) -> Setoid
  f ~~> g = MkSetoid
    { U = f ~> g
      -- Might be easier had we showed Setoids have dependent products
      -- but we haven't yet, so we'll just do it directly
    , equivalence = MkEquivalence
        { relation = NatTransEq f g
        , reflexive = \alpha,a => (d.HomSet _ _).equivalence.reflexive _
        , symmetric = \alpha,beta,prf,a => (d.HomSet _ _).equivalence.symmetric _ _ $
                      prf a
        , transitive = \alpha,beta,gamma,a_eq_b,b_eq_c,a =>
                       (d.HomSet _ _).equivalence.transitive _ _ _
                       (a_eq_b a) (b_eq_c a)
        }
    }

  public export
  compose : {c,d : Category} -> {f,g,h : c ~> d} ->
    (g ~~> h `Pair` f ~~> g) ~> (f ~~> h)
  compose = MkSetoidHomomorphism
    { H = uncurry (.)
    , homomorphic = \(alpha1, beta1),(alpha2,beta2),prf,a =>
        d.cong (alpha1 ^ a , beta1 ^ a) (alpha2 ^ a , beta2 ^ a) $
        MkAnd (prf.fst a) (prf.snd a)
    }

  public export
  Functor : (c,d : Category) -> Category
  Functor c d = MkCategory
    { Obj = c ~> d
    , structure = MkStructure
        { Arr = (~~>)
        , idArr = Id
        , compArr = compose
        }
    , laws = Check
        { idRgtNeutral = \alpha => MkHomEq $ \a => d.laws.idRgtNeutral _
        , idLftNeutral = \alpha => MkHomEq $ \a => d.laws.idLftNeutral _
        , associativity = \alpha,beta,gamma => MkHomEq $ \a => d.laws.associativity _ _ _
        }
    }

public export
record Isomorphism {cat : Category} {a,b : cat.Obj}
  (into : cat.Hom a b) (from : cat.Hom b a) where
  constructor MutuallyInverse
  IntoFromId : (cat.HomSet _ _).equivalence.relation
    (into . from)
    Id
  FromIntoId : (cat.HomSet _ _).equivalence.relation
    (from . into)
    Id
