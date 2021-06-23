||| Product of setoids
module Data.Setoid.Pair

import Data.Setoid.Definition
import Data.Setoid.Either

||| Binary relation conjunction
public export
record And {A,B : Type} (p : A -> A -> Type) (q : B -> B -> Type) (xy1, xy2 : (A, B)) where
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
(.fst) : {a,b : Setoid} -> Pair a b ~> a
(.fst) = MkSetoidHomomorphism
  { H = Builtin.fst
  , homomorphic = \xy1,xy2,prf => prf.fst
  }

||| Right projection setoid homomorphism
public export
(.snd) : {a,b : Setoid} -> Pair a b ~> b
(.snd) = MkSetoidHomomorphism
  { H = Builtin.snd
  , homomorphic = \xy1,xy2,prf => prf.snd
  }

||| Setoid homomorphism constructor
public export
tuple : {a,b,c : Setoid} -> c ~> a -> c ~> b -> c ~> Pair a b
tuple f g = MkSetoidHomomorphism
  { H = \z => (f.H z, g.H z)
  , homomorphic = \z1,z2,prf => MkAnd
      (f.homomorphic z1 z2 prf)
      (g.homomorphic z1 z2 prf)
  }

||| Unique value of type unit
public export
unitVal : (x,y : Unit) -> x = y
unitVal () () = Refl

||| The unique setoid map into the terminal type
public export
unit : {a : Setoid} -> a ~> cast Unit
unit = MkSetoidHomomorphism
  { H = const ()
  , homomorphic = \_,_,_ => unitVal _ _
  }

||| The constant function as a setoid morphism
public export
const : {a,b : Setoid} -> (x : U b) -> a ~> b
const x = mate (Prelude.const x) . unit

||| Setoid homomorphism constructor
public export
bimap : {a,b,c,d : Setoid} -> c ~> a -> d ~> b -> Pair c d ~> Pair a b
bimap f g = tuple (f . (.fst)) (g . (.snd))

-- Distribution of products over sums, degenerate case:

||| Function underlying the bijection 2 x s <~> s + s
public export
distributeFunction : {s : Setoid} -> (Bool, U s) -> (U s `Either` U s)
distributeFunction (False, x) = Left  x
distributeFunction (True , x) = Right x

||| States: the function underlying the bijection 2 x s <~> s + s is a setoid homomorphism
public export
distributeHomomorphism : {s : Setoid} ->
  SetoidHomomorphism ((cast Bool) `Pair` s) (s `Either` s)
    (distributeFunction {s})
distributeHomomorphism (b1,x1) (b2,x2) prf =
  case prf.fst of
    Refl => case b2 of
      False => Left  prf.snd
      True  => Right prf.snd

||| Setoid homomorphism involved in the bijection 2 x s <~> s + s
public export
distribute : {s : Setoid} -> ((cast Bool) `Pair` s) ~> (s `Either` s)
distribute = MkSetoidHomomorphism
  { H = distributeFunction
  , homomorphic = distributeHomomorphism
  }
