module Notation.Multiplicative

import Notation

import public Data.Vect.Quantifiers
import public Data.Fun.Extra

%default total

export infixl 9 .*., :*:, |*|, *., *:, *|, .*, :*, |*

public export
interface Multiplicative1 a where
  constructor MkMultiplicative1
  I1    : 0 `ary` a
  (.*.) : 2 `ary` a

public export
interface Multiplicative2 a where
  constructor MkMultiplicative2
  I2    : 0 `ary` a
  (:*:) : 2 `ary` a

public export
interface Multiplicative3 a where
  constructor MkMultiplicative3
  I3    : 0 `ary` a
  (|*|) : 2 `ary` a

public export
interface MultiplicativeActsOn a b where
  constructor MkMultiplicativeActsOn
  (*.) : [a, b] `ary` b

public export
interface MultiplicativeActsOn2 a b where
  constructor MkMultiplicativeActsOn2
  (*:) : [a, b] `ary` b

public export
interface MultiplicativeActsOn3 a b where
  constructor MkMultiplicativeActsOn3
  (*|) : [a, b] `ary` b

public export
interface MultiplicativeActedBy a b where
  constructor MkMultiplicativeActedBy
  (.*) : [a, b] `ary` a

public export
interface MultiplicativeActedBy2 a b where
  constructor MkMultiplicativeActedBy2
  (:*) : [a, b] `ary` a

public export
interface MultiplicativeActedBy3 a b where
  constructor MkMultiplicativeActedBy3
  (|*) : [a, b] `ary` a

public export
Cast (HVect [0 `ary` a, 2 `ary` a]) (Multiplicative1 a) where
  cast = uncurry MkMultiplicative1

public export
Cast (HVect [0 `ary` a, 2 `ary` a]) (Multiplicative2 a) where
  cast = uncurry MkMultiplicative2

public export
Cast (HVect [0 `ary` a, 2 `ary` a]) (Multiplicative3 a) where
  cast = uncurry MkMultiplicative3

public export
Cast ([a,b] `ary` b) (MultiplicativeActsOn a b) where
  cast = MkMultiplicativeActsOn

public export
Cast ([a,b] `ary` b) (MultiplicativeActsOn2 a b) where
  cast = MkMultiplicativeActsOn2

public export
Cast ([a,b] `ary` b) (MultiplicativeActsOn3 a b) where
  cast = MkMultiplicativeActsOn3

public export
Cast ([a,b] `ary` a) (MultiplicativeActedBy a b) where
  cast = MkMultiplicativeActedBy

public export
Cast ([a,b] `ary` a) (MultiplicativeActedBy2 a b) where
  cast = MkMultiplicativeActedBy2

public export
Cast ([a,b] `ary` a) (MultiplicativeActedBy3 a b) where
  cast = MkMultiplicativeActedBy3

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
