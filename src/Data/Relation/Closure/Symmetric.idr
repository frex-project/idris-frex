module Data.Relation.Closure.Symmetric

import Data.Relation

%default total

public export
data Symmetrise : Rel a -> Rel a where
  Fwd : {0 r : Rel a} -> r x y
           -> Symmetrise r x y
  Bwd : {0 r : Rel a} -> r x y
           -> Symmetrise r y x

export
sym : Symmetrise r ~> flip (Symmetrise r)
sym (Fwd p) = Bwd p
sym (Bwd p) = Fwd p

export
gmap : (f : a -> b) -> p ~> (q `on` f) -> Symmetrise p ~> (Symmetrise q `on` f)
gmap _ f (Fwd p) = Fwd (f p)
gmap _ f (Bwd p) = Bwd (f p)

export
map : p ~> q -> Symmetrise p ~> Symmetrise q
map = gmap id

export
join : Symmetrise (Symmetrise p) ~> Symmetrise p
join (Fwd p) = p
join (Bwd p) = sym p
