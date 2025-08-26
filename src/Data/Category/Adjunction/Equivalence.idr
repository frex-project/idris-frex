module Data.Category.Adjunction.Equivalence

import Data.Category
import Data.Category.Adjunction


public export
record IsEquivalence {B, C : Category} (Adj : Adjunction B C) where
  constructor Validate
  unitInvertible   : (Functor B B).Invertible (MkHom $   unit Adj)
  counitInvertible : (Functor C C).Invertible (MkHom $ counit Adj)
