module Data.Category.Adjunction

import Data.Setoid
import Data.Category.Core

public export
record Adjunction (C, D : Category) where
  constructor MkAdjunction
  lft : C ~> D
  rgt : D ~> C

  Unit   : Id ~> rgt . lft
  Counit : lft . rgt ~> Id

  {-
  triangleUnitCounit :
    ((Functor C D).HomSet _ _).equivalence.relation
      ((lft.map Unit) . (Counit . lft)
      Id
  -}
