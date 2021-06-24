||| The syntax and axioms for monoids
module Frexlet.Monoid.Theory

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

export
HasPrecedence Signature where
 OpPrecedence Product = Just (InfixR 0)

export
Show (Op Signature) where
  show (MkOp Neutral) = "ε"
  show (MkOp Product) = "•"

export
Finite (Op Signature) where
  enumerate = [Unit, Prod]

export
Finite Axiom where
  enumerate = [ LftNeutrality
              , RgtNeutrality
              , Associativity
              ]

export
Show Axiom where
  show = \case
    LftNeutrality => "Left neutrality"
    RgtNeutrality => "Right neutrality"
    Associativity => "Associativity"
