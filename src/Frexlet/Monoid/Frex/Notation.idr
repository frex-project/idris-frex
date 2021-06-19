public export
Action1 : (a,b : Type) -> Type
Action1 a b = (a `MultiplicativeActsOn` b, Additive1 b)

public export
Action2 : (a,b : Type) -> Type
Action2 a b = (a `MultiplicativeActsOn2` b, Additive2 b)

public export
Action3 : (a,b : Type) -> Type
Action3 a b = (a `MultiplicativeActsOn3` b, Additive3 b)

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

