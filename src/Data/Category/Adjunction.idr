module Data.Category.Adjunction

import Data.Category.Core

public export
record Adjunction (C, D : Category) where
  constructor MkAdjunction
  lft : C ~> D
  rgt : D ~> C
  
  unit   : Id ~> rgt . lft
  counit : lft . rgt ~> Id
  
  
