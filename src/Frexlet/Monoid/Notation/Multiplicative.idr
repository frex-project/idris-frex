||| Multiplicative notation for working with monoids (mostly boilerplate)
module Frexlet.Monoid.Notation.Multiplicative

import Frex

import Frexlet.Monoid.Theory

import public Notation.Multiplicative

%default total

public export
(.Multiplicative1) : (monoid : Monoid) -> Multiplicative1 (U monoid)
monoid.Multiplicative1 = MkMultiplicative1 (monoid.sem Neutral) (monoid.sem Product)

public export
(.Multiplicative2) : (monoid : Monoid) -> Multiplicative2 (U monoid)
monoid.Multiplicative2 = MkMultiplicative2 (monoid.sem Neutral) (monoid.sem Product)

public export
(.Multiplicative3) : (monoid : Monoid) -> Multiplicative3 (U monoid)
monoid.Multiplicative3 = MkMultiplicative3 (monoid.sem Neutral) (monoid.sem Product)

public export
notationSyntax : Multiplicative1 (Term Signature x)
notationSyntax = MkMultiplicative1
              (call {sig = Signature} Neutral)
              (call {sig = Signature} Product)
%hint
public export
notation1 : Multiplicative1 (Term Signature x)
notation1 = MkMultiplicative1
              (call {sig = Signature} Neutral)
              (call {sig = Signature} Product)

%hint
public export
notation2 : Multiplicative2 (Term Signature x)
notation2 = MkMultiplicative2
              (call {sig = Signature} Neutral)
              (call {sig = Signature} Product)

%hint
public export
notation3 : Multiplicative3 (Term Signature x)
notation3 = MkMultiplicative3
              (call {sig = Signature} Neutral)
              (call {sig = Signature} Product)
