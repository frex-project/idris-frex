module Data.Category.Adjunction

import Data.Setoid
import Data.Category.Core
import Data.Category.Construction.Pair
import Data.Category.Construction.Op
import Data.Category.Setoid

import Data.Setoid.Fun
-- Use natural bijection definition, to avoid messing around with 2-categories
public export
HomPair : {c1, c2, d : Category} -> (f : c1 ~> d) -> (g : c2 ~> d) ->
  (c1.op `Pair` c2) ~> Setoid
HomPair f g = Hom {c = d} . (f.op `pair` g)

public export
record Adjunction (C, D : Category) where
  constructor MkAdjunction
  lft : C ~> D
  rgt : D ~> C

  mate : {a : C .Obj} -> {b : D .Obj} -> D .HomSet (lft !! a) b <~> C .HomSet a (rgt !! b)

  naturality : {a1,a2 : C .Obj} -> {b1,b2 : D .Obj} ->
    (f : D .Hom b1 b2) -> (g : C .Hom a2 a1) ->
    (u : D .Hom (lft !! a1) b1) ->
    (C .HomSet a2 (rgt !! b2)).equivalence.relation
      (mate.Fwd.H (f . u . lft.map g))
      (rgt.map f . mate.Fwd.H u . g)

public export
mateNatural : {c,d : Category} -> (adj : Adjunction c d) ->
  (HomPair adj.lft Id) ~> (HomPair Id adj.rgt)
mateNatural {c,d} adj =
  MkNatTrans
  { transformation = \ab => MkHom (adj.mate).Fwd
  , naturality = \uv => MkHomEq $ \phi =>
    MkHomEq (adj.naturality (MkHom $ snd $ U uv)
                            (MkHom $ fst $ U uv)
                            phi).runEq
  }

public export
mateIsInvertible : {c,d : Category} -> (adj : Adjunction c d) ->
  (Functor (c.op `Pair` d) Setoid).Invertible $ MkHom (mateNaturality adj)
mateIsInvertible adj = ComponentwiseIso (mateNatural adj) $
  \ab => IsInvertible
    { inverse = MkHom adj.mate.Bwd
    , isInverse = MutuallyInverse
        { FromIntoId = MkHomEq adj.mate.Iso.BwdFwdId
        , IntoFromId = MkHomEq adj.mate.Iso.FwdBwdId
        }

    }

public export
mateInvNatural : {c,d : Category} -> (adj : Adjunction c d) ->
  (HomPair Id adj.rgt) ~> (HomPair adj.lft Id)
mateInvNatural adj = U (mateIsInvertible adj).inverse
