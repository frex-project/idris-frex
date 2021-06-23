||| Product of setoids
module Data.Setoid.Pair

import Data.Setoid.Definition

||| Binary relation conjunction
public export
record And {A,B : Type} (p : Rel A) (q : Rel B) (xy1, xy2 : (A, B)) where
  constructor MkAnd
  fst : p (fst xy1) (fst xy2)
  snd : q (snd xy1) (snd xy2)

||| Product of setoids
public export
Pair : (a,b : Setoid) -> Setoid
Pair a b = MkSetoid
  { U = (U a, U b)
  , equivalence = MkEquivalence
    { relation = a.equivalence.relation `And` b.equivalence.relation
    , reflexive = \xy => MkAnd
        (a.equivalence.reflexive $ fst xy)
        (b.equivalence.reflexive $ snd xy)
    , symmetric  = \xy1,xy2,prf => MkAnd
        (a.equivalence.symmetric (fst xy1) (fst xy2) prf.fst)
        (b.equivalence.symmetric (snd xy1) (snd xy2) prf.snd)
    , transitive = \xy1,xy2,xy3,prf1,prf2 => MkAnd
        (a.equivalence.transitive (fst xy1) (fst xy2) (fst xy3) prf1.fst prf2.fst)
        (b.equivalence.transitive (snd xy1) (snd xy2) (snd xy3) prf1.snd prf2.snd)
    }
  }

||| Left projection setoid homomorphism
public export
(.fst) : {0 a,b : Setoid} -> Pair a b ~> a
(.fst) = MkSetoidHomomorphism
  { H = Builtin.fst
  , homomorphic = \xy1,xy2,prf => prf.fst
  }

||| Right projection setoid homomorphism
public export
(.snd) : {0 a,b : Setoid} -> Pair a b ~> b
(.snd) = MkSetoidHomomorphism
  { H = Builtin.snd
  , homomorphic = \xy1,xy2,prf => prf.snd
  }

||| Setoid homomorphism constructor
public export
tuple : {0 a,b,c : Setoid} -> c ~> a -> c ~> b -> c ~> Pair a b
tuple f g = MkSetoidHomomorphism
  { H = \z => (f.H z, g.H z)
  , homomorphic = \z1,z2,prf => MkAnd
      (f.homomorphic z1 z2 prf)
      (g.homomorphic z1 z2 prf)
  }
