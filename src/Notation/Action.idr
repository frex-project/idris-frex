module Notation.Action

import public Data.HVect
import public Data.Fun.Extra

import public Notation
import public Notation.Additive
import public Notation.Multiplicative

public export
head : HVect (ty :: tys) -> ty
head (x :: xs) = x

public export
tail : HVect (ty :: tys) -> HVect tys
tail (x :: xs) = xs

public export
Action1 : (a,b : Type) -> Type
Action1 a b = (a `MultiplicativeActsOn` b, Additive1 b)

public export
Action2 : (a,b : Type) -> Type
Action2 a b = (a `MultiplicativeActsOn2` b, Additive2 b)

public export
Action3 : (a,b : Type) -> Type
Action3 a b = (a `MultiplicativeActsOn3` b, Additive3 b)

public export
ActionData : Type -> Type -> Type
ActionData a b = HVect [[a,b] `ary` b, 0 `ary` b, 2 `ary` b]

public export
Cast (ActionData a b) (Action1 a b) where
  cast datum = (cast $ head datum, cast $ tail datum)

public export
Cast (ActionData a b) (Action2 a b) where
  cast datum = (cast $ head datum, cast $ tail datum)

public export
Cast (ActionData a b) (Action3 a b) where
  cast datum = (cast $ head datum, cast $ tail datum)

