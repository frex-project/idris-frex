module Data.Category.Core.Functor

import Data.Category.Core.Category

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
(.mapSetoid) : {c,d : Category} -> (f : c ~> d) -> {a,b : c.Obj} ->
  c.HomSet a b ~> d.HomSet (f !! a) (f !! b)
f.mapSetoid = f.structure.mapHom

public export
(.map) : {c,d : Category} -> (f : c ~> d) -> {a,b : c.Obj} -> c.Hom a b ->
  d.Hom (f !! a) (f !! b)
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
      CalcWith (c.HomSet _ _) $
      |~ f.map (g.map Id)
      ~~ f.map Id ...(f.mapSetoid.homomorphic _ Id $
                      g.functoriality.id _)
      ~~ Id       ...(f.functoriality.id _)
    , comp = \u,v =>
      CalcWith (c.HomSet _ _) $
      |~ f.map (g.map (u . v))
      ~~ f.map (g.map u . g.map v)         ...(f.mapSetoid.homomorphic (g.map (u . v)) _ $
                                               g.functoriality.comp u v)
      ~~ f.map (g.map u) . f.map (g.map v) ...(f.functoriality.comp _ _)
    }
  }

public export
data Composable : {cat : Category} -> (src,tgt : cat.Obj) -> Type where
  Nil : {a : cat.Obj} -> Composable {cat} a a
  (::) : {a,b,c : cat.Obj} ->
    cat.Hom b c          -> Composable {cat} a b -> Composable {cat} a c
  ConsNested : {a,b,c : cat.Obj} ->
    Composable {cat} b c -> Composable {cat} a b -> Composable {cat} a c

public export
(.flatten) : {cat : Category} -> {0 a,b : cat.Obj} -> Composable {cat} a b -> cat.Hom a b
[].flatten = Id
(u  :: []).flatten = u
(u  :: us).flatten = u . us.flatten
(us `ConsNested` []).flatten = us.flatten
(us `ConsNested` vs).flatten = us.flatten . vs.flatten

namespace Composable
  public export
  (.mapC) : {c,d : Category} -> {0 a,b : c.Obj} -> (f : c ~> d) ->
    Composable {cat = c} a b -> Composable {cat = d} (f !! a) (f !! b)
  f.mapC [] = []
  f.mapC (u  :: vs) = (f.map u  :: f.mapC vs)
  f.mapC (us `ConsNested` vs) = (f.mapC us `ConsNested` f.mapC vs)

  public export
  (.functoriality) : {c,d : Category} -> {0 a, b : c.Obj} -> (f : c ~> d) ->
    (us : Composable a b) ->
    (d.HomSet _ _).equivalence.relation
      (f.map us.flatten)
      ((f.mapC us).flatten)
  f.functoriality [] = f.functoriality.id _
  f.functoriality (u  :: vs@[]) = (d.HomSet _ _).equivalence.reflexive _

  f.functoriality (u  :: vs@(_ :: _)) = CalcWith (d.HomSet _ _) $
    |~ f.map (u . vs.flatten)
    ~~ f.map u . (f.map vs.flatten) ...(f.functoriality.comp u vs.flatten)
    ~~ f.map u . (f.mapC vs).flatten ...(_ . f.functoriality vs)
    ~~ _ .=.(Refl)
  f.functoriality (u  :: vs@(_ `ConsNested` _)) = CalcWith (d.HomSet _ _) $
    |~ f.map (u . vs.flatten)
    ~~ f.map u . (f.map vs.flatten) ...(f.functoriality.comp u vs.flatten)
    ~~ f.map u . (f.mapC vs).flatten ...(f.map u . (f.functoriality vs))
    ~~ _ .=.(Refl)

  f.functoriality (us `ConsNested` []) = f.functoriality us
  f.functoriality (us `ConsNested` vs@(_ :: _)) = CalcWith (d.HomSet _ _) $
    |~ f.map (us.flatten . vs.flatten)
    ~~ (f.map us.flatten) . (f.map vs.flatten) ...(f.functoriality.comp _ _)
    ~~ (f.mapC us).flatten . (f.mapC vs).flatten ...((f.functoriality _) .:. (f.functoriality _))
    ~~ _ .=.(Refl)
  f.functoriality (us `ConsNested` vs@(_ `ConsNested` _)) = CalcWith (d.HomSet _ _) $
    |~ f.map (us.flatten . vs.flatten)
    ~~ (f.map us.flatten) . (f.map vs.flatten) ...(f.functoriality.comp _ _)
    ~~ (f.mapC us).flatten . (f.mapC vs).flatten ...((f.functoriality _) .:. (f.functoriality _))
    ~~ _ .=. Refl

public export
(.byFunctoriality) : {c,d : Category} -> {a, b : c.Obj} -> (f : c ~> d) ->
  (us,vs : Composable a b) ->
  (c.HomSet _ _).equivalence.relation
    us.flatten
    vs.flatten ->
  (d.HomSet _ _).equivalence.relation
    (f.mapC us).flatten
    (f.mapC vs).flatten
f.byFunctoriality us vs prf = CalcWith (d.HomSet _ _) $
  |~ (f.mapC us).flatten
  ~~  f.map us.flatten  ..<(f.functoriality _)
  ~~  f.map vs.flatten  ...(f.mapSetoid.homomorphic _ _ prf)
  ~~ (f.mapC vs).flatten ...(f.functoriality _)
