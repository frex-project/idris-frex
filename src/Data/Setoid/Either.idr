||| Coproduct of setoids
module Data.Setoid.Either

import Data.Setoid.Definition

namespace Relation
  ||| Binary relation disjunction
  public export
  data Or : (p : a -> a -> Type) -> (q : b -> b -> Type) -> (x, y : Either a b)  -> Type where
    Left  : {0 q : b -> b -> Type} -> p x y -> (p `Or` q) (Left  x) (Left  y)
    Right : {0 p : a -> a -> Type} -> q x y -> (p `Or` q) (Right x) (Right y)

||| Coproduct of setoids
public export
Either : (a,b : Setoid) -> Setoid
Either a b = MkSetoid
  { U = U a `Either` U b
  , equivalence = MkEquivalence
    { relation = a.equivalence.relation `Or` b.equivalence.relation
    , reflexive = \case
         Left  x => Left  $ a.equivalence.reflexive x
         Right y => Right $ b.equivalence.reflexive y
    , symmetric = \x,y => \case 
        Left  prf => Left  $ a.equivalence.symmetric _ _ prf
        Right prf => Right $ b.equivalence.symmetric _ _ prf
    , transitive = \x,y,z => \case 
        Left  prf1 => \case {Left  prf2 => Left  $ a.equivalence.transitive _ _ _ prf1 prf2}
        Right prf1 => \case {Right prf2 => Right $ b.equivalence.transitive _ _ _ prf1 prf2}
    }
  }

||| Setoid homomorphism smart constructor
public export
Left : {a, b: Setoid} -> a ~> (a `Either` b)
Left = MkSetoidHomomorphism 
  { H = Left
  , homomorphic = \x,y,prf => Left prf
  }

||| Setoid homomorphism smart constructor
public export
Right : {a, b: Setoid} -> b ~> (a `Either` b)
Right = MkSetoidHomomorphism 
  { H = Right
  , homomorphic = \x,y,prf => Right prf
  }

||| Setoid homomorphism deconstructor
public export
either : {a, b, c : Setoid} -> (a ~> c) -> (b ~> c) -> (a `Either` b) ~> c
either lft rgt = MkSetoidHomomorphism
  { H = either lft.H rgt.H
  , homomorphic = \x,y => \case
      Left  prf => lft.homomorphic _ _ prf
      Right prf => rgt.homomorphic _ _ prf
  }
