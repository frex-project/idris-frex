module Notation.Multiplicative

import Notation

import public Data.HVect
import public Data.Fun.Extra

infixl 9 .*., :*:, |*|, *., *:, *|, .*, :*, |*

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
