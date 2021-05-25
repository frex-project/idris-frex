module Frexlet.Monoid

import Frex

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
Monoid : Presentation
Monoid = MkPresentation Monoid.Signature Monoid.Axiom \case
    LftNeutrality => lftNeutrality Neutral Product
    RgtNeutrality => rgtNeutrality Neutral Product
    Associativity => associativity Product


