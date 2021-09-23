module Data.Category.Adjunction

import Data.Setoid
import Data.Category.Core

-- Use natural bijection definition, to avoid messing around with 2-categories

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
(.naturalityInv) : {c,d : Category} -> (phi : Adjunction c d) ->
    {a1,a2 : c.Obj} -> {b1,b2 : d.Obj} ->
    (f : d.Hom b1 b2) -> (g : c.Hom a2 a1) ->
    (u : c.Hom a1 (phi.rgt !! b1)) ->
    (d.HomSet (phi.lft !! a2) b2).equivalence.relation
      (f . phi.mate.Bwd.H u . phi.lft.map g)
      (phi.mate.Bwd.H (phi.rgt.map f . u . g))
phi.naturalityInv f g u = ?naturalityInv_rhs
