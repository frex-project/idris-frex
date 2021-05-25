module Frexlet.Monoid.Commutative

import Frex

import public Frexlet.Monoid

data Axiom 
  = Mon Monoid.Axiom
  | Commutativity

public export
Commutative : Presentation
Commutative = MkPresentation Monoid.Signature Monoid.Commutative.Axiom \case
    Mon ax => (Monoid).axiom ax
    Commutativity => commutativity Product
