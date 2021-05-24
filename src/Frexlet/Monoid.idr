module Frexlet.Monoid

import Frex

public export
data Operation = Neutral |
                 Product
                 
public export
Signature : Signature

public export
data Axiom = LftNeutrality | RgtNeutrality | Associativity

public export
Monoid : Presentation
Monoid = MkPresentation Monoid.Signature \case
  LftNeutrality  => ?h1
  RgtNeutrality  => ?h2
  Associativity  => ?h3


