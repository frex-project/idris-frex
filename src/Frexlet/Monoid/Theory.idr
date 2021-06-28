||| The syntax and axioms for monoids
module Frexlet.Monoid.Theory

import Frex

%default total

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
MonoidStructure : Type
MonoidStructure = SetoidAlgebra Theory.Signature

public export
Monoid : Type
Monoid = Model MonoidTheory

public export
Unit : Op Signature
Unit = MkOp Neutral

public export
Prod : Op Signature
Prod = MkOp Product
