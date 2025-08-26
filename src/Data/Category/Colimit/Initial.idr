module Data.Category.Colimit.Initial

import Data.Category

public export
record (.IsInitial) (C : Category) (I : C .Obj) where
  constructor Universality
  exists : (x : C .Obj) -> C .Hom I x
  unique : (x : C .Obj) -> (f,g : C .Hom I x) ->
           (C .HomSet I x).equivalence.relation f g

public export
record Initial (C : Category) where
  constructor MkInitial
  Data : C .Obj
  UP   : C .IsInitial Data
