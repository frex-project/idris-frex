||| The syntax and axioms for monoids
module Frexlet.Monoid.Theory

import Frex

import Notation.Additive


public export
data Operation : Nat -> Type where
  Neutral : Operation 0
  Product : Operation 2
                 
public export
Signature : Signature
Signature = MkSignature Operation

public export
data Axiom 
 = LftNeutrality 
 | RgtNeutrality
 | Associativity 

public export
MonoidTheory : Presentation
MonoidTheory = MkPresentation Theory.Signature Theory.Axiom \case
    LftNeutrality => lftNeutrality Neutral Product
    RgtNeutrality => rgtNeutrality Neutral Product
    Associativity => associativity Product

public export
Monoid : Type
Monoid = Model MonoidTheory

