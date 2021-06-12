||| Notation for working with monoids (mostly boilerplate)
module Frexlet.Monoid.Notation

import Frex

import Frexlet.Monoid.Theory
import Notation.Additive
import Notation.Multiplicative

public export
(.Additive1) : (monoid : Monoid) -> Additive1 (U monoid)
monoid.Additive1 = MkAdditive1 (monoid.sem Neutral) (monoid.sem Product)

public export
(.Additive2) : (monoid : Monoid) -> Additive2 (U monoid)
monoid.Additive2 = MkAdditive2 (monoid.sem Neutral) (monoid.sem Product)

public export
(.Additive3) : (monoid : Monoid) -> Additive3 (U monoid)
monoid.Additive3 = MkAdditive3 (monoid.sem Neutral) (monoid.sem Product)

public export
(.Multiplicative1) : (monoid : Monoid) -> Multiplicative1 (U monoid)
monoid.Multiplicative1 = MkMultiplicative1 (monoid.sem Neutral) (monoid.sem Product)

public export
(.Multiplicative2) : (monoid : Monoid) -> Multiplicative2 (U monoid)
monoid.Multiplicative2 = MkMultiplicative2 (monoid.sem Neutral) (monoid.sem Product)

public export
(.Multiplicative3) : (monoid : Monoid) -> Multiplicative3 (U monoid)
monoid.Multiplicative3 = MkMultiplicative3 (monoid.sem Neutral) (monoid.sem Product)
