module Data.Relation.Closure.Symmetric

import Data.Relation

public export
data Symmetrise : Rel a -> Rel a where
  Fwd : {0 r : Rel a} -> r x y -> Symmetrise r x y
  Bwd : {0 r : Rel a} -> r x y -> Symmetrise r y x

export
sym : Symmetrise r x y -> Symmetrise r y x
sym (Fwd p) = Bwd p
sym (Bwd p) = Fwd p

export
map : p ~> q -> Symmetrise p ~> Symmetrise q
map f (Fwd p) = Fwd (f p)
map f (Bwd p) = Bwd (f p)

export
join : Symmetrise (Symmetrise p) ~> Symmetrise p
join (Fwd p) = p
join (Bwd p) = sym p
