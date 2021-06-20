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
MAction1 : (a,b : Type) -> Type
MAction1 a b = (a `MultiplicativeActsOn` b, Multiplicative1 b)

public export
MAction2 : (a,b : Type) -> Type
MAction2 a b = (a `MultiplicativeActsOn2` b, Multiplicative2 b)

public export
MAction3 : (a,b : Type) -> Type
MAction3 a b = (a `MultiplicativeActsOn3` b, Multiplicative3 b)

%hint
public export
fstAdditive1 : (Additive1 a, _) -> Additive1 a
fstAdditive1 = fst

%hint
public export
sndAdditive1 : (_, Additive1 a) -> Additive1 a
sndAdditive1 = snd

%hint
public export
fstAdditive2 : (Additive2 a, _) -> Additive2 a
fstAdditive2 = fst

%hint
public export
sndAdditive2 : (_, Additive2 a) -> Additive2 a
sndAdditive2 = snd

%hint
public export
fstAdditive3 : (Additive3 a, _) -> Additive3 a
fstAdditive3 = fst

%hint
public export
sndAdditive3 : (_, Additive3 a) -> Additive3 a
sndAdditive3 = snd


%hint
public export
fstMultiplicative1 : (Multiplicative1 a, _) -> Multiplicative1 a
fstMultiplicative1 = fst

%hint
public export
sndMultiplicative1 : (_, Multiplicative1 a) -> Multiplicative1 a
sndMultiplicative1 = snd

%hint
public export
fstMultiplicative2 : (Multiplicative2 a, _) -> Multiplicative2 a
fstMultiplicative2 = fst

%hint
public export
sndMultiplicative2 : (_, Multiplicative2 a) -> Multiplicative2 a
sndMultiplicative2 = snd

%hint
public export
fstMultiplicative3 : (Multiplicative3 a, _) -> Multiplicative3 a
fstMultiplicative3 = fst

%hint
public export
sndMultiplicative3 : (_, Multiplicative3 a) -> Multiplicative3 a
sndMultiplicative3 = snd

%hint
public export
fstMultiplicativeActsOn : (MultiplicativeActsOn a b, _) -> MultiplicativeActsOn a b
fstMultiplicativeActsOn = fst

%hint
public export
sndMultiplicativeActsOn : (_, MultiplicativeActsOn a b) -> MultiplicativeActsOn a b
sndMultiplicativeActsOn = snd

%hint
public export
fstMultiplicativeActsOn2 : (MultiplicativeActsOn2 a b, _) -> MultiplicativeActsOn2 a b
fstMultiplicativeActsOn2 = fst

%hint
public export
sndMultiplicativeActsOn2 : (_, MultiplicativeActsOn2 a b) -> MultiplicativeActsOn2 a b
sndMultiplicativeActsOn2 = snd

%hint
public export
fstMultiplicativeActsOn3 : (MultiplicativeActsOn3 a b, _) -> MultiplicativeActsOn3 a b
fstMultiplicativeActsOn3 = fst

%hint
public export
sndMultiplicativeActsOn3 : (_, MultiplicativeActsOn3 a b) -> MultiplicativeActsOn3 a b
sndMultiplicativeActsOn3 = snd

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

public export
Cast (ActionData a b) (MAction1 a b) where
  cast datum = (cast $ head datum, cast $ tail datum)

public export
Cast (ActionData a b) (MAction2 a b) where
  cast datum = (cast $ head datum, cast $ tail datum)

public export
Cast (ActionData a b) (MAction3 a b) where
  cast datum = (cast $ head datum, cast $ tail datum)

