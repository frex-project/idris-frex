module Data.Category.Adjunction

import Data.Setoid
import Data.Setoid.Fun

import Data.Category.Core
import Data.Category.Construction.Pair
import Data.Category.Construction.Op
import Data.Category.Setoid

-- Use natural bijection definition, to avoid messing around with 2-categories
public export
HomPair : {c1, c2, d : Category} -> (f : c1 ~> d) -> (g : c2 ~> d) ->
  (c1.op `Pair` c2) ~> Setoid
HomPair f g = Hom {c = d} . (f.op `pair` g)

public export
record Adjoint {C,D : Category} (Lft : C ~> D) (Rgt : D ~> C) where
  constructor AreAdjoint
  mate : {a : C .Obj} -> {b : D .Obj} ->
    D .HomSet (Lft !! a) b <~> C .HomSet a (Rgt !! b)
  naturality : {a1,a2 : C .Obj} -> {b1,b2 : D .Obj} ->
    (f : D .Hom b1 b2) -> (g : C .Hom a2 a1) ->
    (u : D .Hom (Lft !! a1) b1) ->
    (C .HomSet a2 (Rgt !! b2)).equivalence.relation
      (mate.Fwd.H (f . u . (Lft).map g))
      ((Rgt).map f . mate.Fwd.H u . g)

public export
record Adjunction (C, D : Category) where
  constructor MkAdjunction
  lft : C ~> D
  rgt : D ~> C

  adjoint : Adjoint lft rgt


public export
cast : {f : c ~> d} -> {g : d ~> c} -> Adjoint f g -> (Adjunction c d)
cast adjoint = MkAdjunction f g adjoint

public export
(.mateNatural) : {c,d : Category} -> (adj : Adjunction c d) ->
  (HomPair adj.lft Id) ~> (HomPair Id adj.rgt)
(adj.mateNatural) {c,d} =
  MkNatTrans
  { transformation = \ab => MkHom (adj.adjoint.mate).Fwd
  , naturality = \uv => MkHomEq $ \phi =>
    MkHomEq (adj.adjoint.naturality (MkHom $ snd $ U uv)
                                    (MkHom $ fst $ U uv)
                            phi).runEq
  }

public export
mateIsInvertible : {c,d : Category} -> (adj : Adjunction c d) ->
  (Functor (c.op `Pair` d) Setoid).Invertible $ MkHom adj.mateNatural
mateIsInvertible adj = ComponentwiseIso adj.mateNatural $
  \ab => IsInvertible
    { inverse = MkHom adj.adjoint.mate.Bwd
    , isInverse = MutuallyInverse
        { FromIntoId = MkHomEq adj.adjoint.mate.Iso.BwdFwdId
        , IntoFromId = MkHomEq adj.adjoint.mate.Iso.FwdBwdId
        }

    }

public export
(.mateInvNatural) : {c,d : Category} -> (adj : Adjunction c d) ->
  (HomPair Id adj.rgt) ~> (HomPair adj.lft Id)
adj.mateInvNatural = U (mateIsInvertible adj).inverse

public export
mateIsomorphism : {c,d : Category} -> (adj : Adjunction c d) ->
  (Functor (c.op `Pair` d) Setoid).Isomorphism
    (MkHom adj.mateNatural   )
    (MkHom adj.mateInvNatural)
mateIsomorphism adj = (mateIsInvertible adj).isInverse

public export
unit : {c,d : Category} -> (adj : Adjunction c d) ->
  Id ~> adj.rgt . adj.lft
unit {c,d} adj = MkNatTrans
  { transformation = \a => (U $ adj.mateNatural ^ (a , adj.lft !! a)).H Id
  , naturality = \u =>
      {- The plan is to chase the identity through two diagrams:

  d.Hom (lft !! a) (lft !! a)  ----- mate ----------> c.Hom a (rgt !! lft !! a)
     \                        naturality                                     |
      \  d.Hom Id (lft.map u)     =          c.Hom Id (rgt.map . lft.map u)  |
       \                                                                     v
       --> d.Hom (lft !! a) (lft !! b) ---- mate ---> c.Hom a (rgt !! lft !! b)
      /                                                                      ^
     / d.Hom (lft !! u) Id               =                       d.Hom u  Id |
    /                                naturality                              |
  d.Hom (lft !! b) (lft !! b) ----- mate ----------> c.Hom b (rgt !! lft !! a)

       like so:

       id           |------------------->     unit a
       __                                      _
        \                                      |
         \                                     |
          -> lft.map u . id                    V
                ||                       (rgt.map . lft.map) u . unit a
             lft.map u                        ||
                ||                            ||
        id . lft.map u                   unit b . u
            ^                                 ^
           /                                  |
          /                                   |
        _/_                                  _|_
        id   |-------------------------> unit b
      -}
      let A,B : c.Obj
          A = u.src
          B = u.tgt
          T : c ~> c
          T = adj.rgt . adj.lft
          mate : {a : c.Obj} -> {b : d.Obj} ->
                  d.HomSet (adj.lft !! a) b ~> c.HomSet a (adj.rgt !! b)
          mate {a,b} = (U $ adj.mateNatural ^ (a , b))
          eta : (a : c.Obj) -> c.Hom a (T !! a)
          eta a = mate.H Id
          upper : (c.HomSet A (T !! B)).equivalence.relation
                    (mate.H (adj.lft.map u))
                    (((T).map u) . (eta A))
          upper = CalcWith (c.HomSet _ _) $
            |~  mate.H (adj.lft.map u)
            ~~ (mate.H (adj.lft.map u . Id     )) ..<(mate.homomorphic _ _ $
                                                      d.laws.idRgtNeutral _)
            ~~ (mate.H (adj.lft.map u . Id . Id)) ..<(mate.homomorphic _ _ $
                                                     (adj.lft.map u) .
                                                       (d.laws.idRgtNeutral Id))
            ~~ (mate.H (adj.lft.map u
                 . Id {a = adj.lft !! A}
                 . (adj.lft.map $ Id)))           ..<(mate.homomorphic _ _ $
                                                     adj.lft.map u . Id .
                                                     adj.lft.functoriality.id A)

            ~~ (((T).map u) . (eta A . Id))       ...(adj.adjoint.naturality
                                                     (adj.lft.map u)
                                                     Id
                                                     Id)
            ~~ (((T).map u) . (eta A))          ...(((T).map u) .
                                                    (c.laws.idRgtNeutral _ ))
          -- similarly for the lower half
          lower : (c.HomSet A (T !! B)).equivalence.relation
                    (mate.H (adj.lft.map u))
                    (eta B . u)
          lower = CalcWith (c.HomSet _ _) $
            |~ mate.H (adj.lft.map u)
            ~~ mate.H (     Id . (adj.lft.map u)) ..<(mate.homomorphic _ _ $
                                                      d.laws.idLftNeutral _)
            ~~ mate.H (Id . Id . (adj.lft.map u)) ..<(mate.homomorphic _ _ $
                                                      d.laws.idLftNeutral _)
            ~~ adj.rgt.map Id . eta B . u         ...(adj.adjoint.naturality
                                                      Id u Id)
            ~~             Id . eta B . u         ...(adj.rgt.functoriality.id _
                                                      . (eta B . u))
            ~~                  eta B . u         ...(c.laws.idLftNeutral _)
      in CalcWith (c.HomSet _ _) $
      |~ (eta B . u)
      ~~ mate.H (adj.lft.map u)  ..<(lower)
      ~~ (((T).map u) . (eta A)) ...(upper)
  }

%unbound_implicits off
namespace Adjoint
  public export
  (.op) : {c,d : Category} -> {lft : c ~> d} -> {rgt : d ~> c} ->
    Adjoint lft rgt -> Adjoint rgt.op lft.op
  adjoint.op =
    let MateOp : {a : d.op.Obj}-> {b : c.op.Obj} ->
          c.op.HomSet (rgt.op !! a) b <~> d.op.HomSet a (lft.op !! b)
        MateOp = (HomOpIso `trans` (sym $ adjoint.mate))
                       `trans` (sym HomOpIso)
    in AreAdjoint
    { mate = MateOp
      -- This is ridiculous, I think there's a bug in the elaborator if I need to
      -- supply all this information just to get going.
    , naturality = \f@(MkHom f' {a=b1,b=b2}),g@(MkHom g' {a=a2,b=a1}),u@(MkHom u') =>
        MkHomEq (CalcWith (d.HomSet (lft !! b2) a2) $
        |~ adjoint.mate.Bwd.H ((rgt.map (MkHom $ g')
                              . (MkHom $ u'))
                              . (MkHom $ f'))
        ~~ adjoint.mate.Bwd.H (rgt.map (MkHom $ g')
                              . (MkHom $ u')
                              . (MkHom $ f')) ..<(adjoint.mate.Bwd.homomorphic
                                                  _ _ $
                                                  c.laws.associativity
                                                    (rgt.map (MkHom $ g'))
                                                    (MkHom $ u')
                                                    (MkHom $ f'))
        ~~ (MkHom $ g') . (adjoint.mate.Bwd.H $ MkHom $ u')
                        . (lft.map $ MkHom $ f')
                -- simply ridiculous
             ...(((MkAdjunction lft rgt adjoint).mateInvNatural.naturality
                   (MkHom {a = (b1,a1), b=(b2, a2)} (f', g'))).runEq (MkHom u'))
        ~~ ((MkHom $ g') . (adjoint.mate.Bwd.H $ MkHom $ u'))
                         . (lft.map $ MkHom $ f')
                                                 ...(d.laws.associativity
                                                     (MkHom $ g')
                                                     (adjoint.mate.Bwd.H $ MkHom $ u')
                                                     (lft.map $ MkHom $ f'))).runEq
    }
%unbound_implicits on

public export
(.op) : {c, d : Category} -> Adjunction c d -> Adjunction d.op c.op
adj.op = MkAdjunction adj.rgt.op adj.lft.op adj.adjoint.op

public export
counit : {c,d : Category} -> (adj : Adjunction c d) ->
  adj.lft . adj.rgt ~> Id
counit {c,d} adj =
  let unitOp : Id ~> adj.op.rgt . adj.op.lft
      unitOp = unit adj.op
      epsilon : Transformation (adj.lft . adj.rgt) Id
      epsilon a = MkHom $ U $ unitOp ^ a
  in MkNatTrans
  { transformation = epsilon
  , naturality = \u@(MkHom u' {a,b}) =>
      let A,B : d.Obj
          A = a
          B = b
          v : d.op.Hom B A
          v = MkHom $ u'
      in CalcWith (d.HomSet _ _) $
      |~ (epsilon B) . (adj.lft.map (adj.rgt.map $ MkHom u'))
      ~~ (MkHom $ U $ (adj.op.rgt.map (adj.op.lft.map v)) . (MkHom $ U $ unitOp ^ B))
          ..<(MkHomEq
                ((epsilon B) . (adj.lft.structure.mapHom.homomorphic _ _ (etaLaw _))
             ).runEq)
      ~~ (MkHom $ U $ (unitOp ^ A) . v)
          ..<(MkHomEq (unitOp.naturality (MkHom $ U u)).runEq)
      ~~ (MkHom u') . (epsilon A) .=.(Refl)
  }

-- TODO: refactor the above to use these

-- Easy consequences of mate's naturality
public export
(.mateNaturalityPre) : {c,d : Category} -> (adj : Adjunction.Adjunction c d) ->
  {a2,a1 : c.Obj} -> {b : d.Obj} ->
  (u : c.Hom a2 a1) -> (f : d.Hom (adj.lft !! a1) b) ->
  (c.HomSet _ _).equivalence.relation
    (adj.adjoint.mate.Fwd.H (f . adj.lft.map u))
    (adj.adjoint.mate.Fwd.H f . u)
adj.mateNaturalityPre u f =
  let mate : {a : c.Obj} -> {b : d.Obj} ->
             d.HomSet (adj.lft !! a) b ~> c.HomSet a (adj.rgt !! b)
      mate = adj.adjoint.mate.Fwd
  in CalcWith (c.HomSet _ _) $
  |~ mate.H (f . adj.lft.map u)
  ~~ mate.H (Id . f . adj.lft.map u) ..<(mate.homomorphic _ _ $
                                         d.laws.idLftNeutral _)
  ~~ adj.rgt.map Id . mate.H f .  u  ...(adj.adjoint.naturality Id _ _)
  ~~             Id . mate.H f .  u  ...(adj.rgt.functoriality.id _
                                        . (mate.H f . u))
  ~~                  mate.H f .  u  ...(c.laws.idLftNeutral _)

public export
(.mateNaturalityPost) : {c,d : Category} -> (adj : Adjunction.Adjunction c d) ->
  {a : c.Obj} -> {b1,b2 : d.Obj} ->
  (u : d.Hom b1 b2) -> (f : d.Hom (adj.lft !! a) b1) ->
         -- v-- no idea why this `a` can't be inferred. Bug?
  (c.HomSet a _).equivalence.relation
    (adj.adjoint.mate.Fwd.H (u . f))
    (adj.rgt.map u . adj.adjoint.mate.Fwd.H f)
adj.mateNaturalityPost u f =
  let mate : {a : c.Obj} -> {b : d.Obj} ->
             d.HomSet (adj.lft !! a) b ~> c.HomSet a (adj.rgt !! b)
      mate = adj.adjoint.mate.Fwd
  in CalcWith (c.HomSet _ _) $
  |~ mate.H (u . f)
  ~~ mate.H (u . f . Id)             ..<(mate.homomorphic _ _ $
                                         u . d.laws.idRgtNeutral _)
  ~~ mate.H (u . f . adj.lft.map Id) ..<(mate.homomorphic _ _ $
                                         u . f . adj.lft.functoriality.id _)
  ~~ adj.rgt.map u . mate.H f . Id   ...(adj.adjoint.naturality _ _ _)
  ~~ adj.rgt.map u . mate.H f        ...(adj.rgt.map u . c.laws.idRgtNeutral _)

public export
(.mateInvNaturalityPre) : {c,d : Category} -> (adj : Adjunction.Adjunction c d) ->
  {a1,a2 : c.Obj} -> {b : d.Obj} ->
  (u : c.Hom a2 a1) -> (g : c.Hom a1 (adj.rgt !! b)) ->
  (d.HomSet _ b).equivalence.relation
    (adj.adjoint.mate.Bwd.H (g . u))
    (adj.adjoint.mate.Bwd.H g . adj.lft.map u)
adj.mateInvNaturalityPre u g =
  let mate : {a : c.Obj} -> {b : d.Obj} ->
             d.HomSet (adj.lft !! a) b <~> c.HomSet a (adj.rgt !! b)
      mate = adj.adjoint.mate
  in CalcWith (d.HomSet _ _) $
  |~ mate.Bwd.H (                          g . u)
  ~~ mate.Bwd.H ((mate.Fwd.H $ mate.Bwd.H g) . u)
                               ..<(mate.Bwd.homomorphic _ _ $
                                  mate.Iso.FwdBwdId g
                                  . u)
  ~~ mate.Bwd.H (mate.Fwd.H ((mate.Bwd.H g) . adj.lft.map u))
                               ..<(mate.Bwd.homomorphic _ _ $
                                   adj.mateNaturalityPre u (mate.Bwd.H g))
  ~~ mate.Bwd.H g . adj.lft.map u
                               ...(mate.Iso.BwdFwdId _)

public export
(.mateInvNaturalityPost) : {c,d : Category} -> (adj : Adjunction.Adjunction c d) ->
  {a : c.Obj} -> {b1,b2 : d.Obj} ->
  (u : d.Hom b1 b2) -> (g : c.Hom a (adj.rgt !! b1)) ->
  (d.HomSet _ _).equivalence.relation
    (adj.adjoint.mate.Bwd.H (adj.rgt.map u . g))
    (u . adj.adjoint.mate.Bwd.H g)
adj.mateInvNaturalityPost u g =
  let mate : {a : c.Obj} -> {b : d.Obj} ->
             d.HomSet (adj.lft !! a) b <~> c.HomSet a (adj.rgt !! b)
      mate = adj.adjoint.mate
  in CalcWith (d.HomSet _ _) $
  |~ mate.Bwd.H (adj.rgt.map u .                          g )
  ~~ mate.Bwd.H (adj.rgt.map u . (mate.Fwd.H $ mate.Bwd.H g))
                               ..<(mate.Bwd.homomorphic _ _ $
                                  adj.rgt.map u .
                                  mate.Iso.FwdBwdId g)
  ~~ mate.Bwd.H (mate.Fwd.H (u . (mate.Bwd.H g)))
                               ..<(mate.Bwd.homomorphic _ _ $
                                   adj.mateNaturalityPost u (mate.Bwd.H g))
  ~~ u . mate.Bwd.H g          ...(mate.Iso.BwdFwdId _)
