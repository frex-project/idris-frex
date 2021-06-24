||| The syntax and axioms for rings
module Frexlet.Ring.Theory

import Frex

public export
data Operation : Nat -> Type where
  SNeutral : Operation 0
  SInverse : Operation 1
  Sum      : Operation 2
  PNeutral : Operation 0
  Product  : Operation 2

public export
Signature : Signature
Signature = MkSignature Operation

public export
data Axiom
 = SumLftNeutrality
 | SumCommutativity
 | SumAssociativity
 | SumRgtInverse
 | ProdLftNeutrality
 | ProdRgtNeutrality
 | ProdAssociativity
 | ProdLftAnnihilation
 | ProdRgtAnnihilation
 | LftDistributivity
 | RgtDistributivity

public export
RingTheory : Presentation
RingTheory = MkPresentation Theory.Signature Theory.Axiom \case
    SumLftNeutrality    => lftNeutrality SNeutral Sum
    SumCommutativity    => commutativity Sum
    SumAssociativity    => associativity Sum
    SumRgtInverse       => rgtInverse SNeutral SInverse Sum
    ProdLftNeutrality   => lftNeutrality PNeutral Product
    ProdRgtNeutrality   => rgtNeutrality PNeutral Product
    ProdAssociativity   => associativity Product
    ProdLftAnnihilation => lftAnnihilation SNeutral Product
    ProdRgtAnnihilation => rgtAnnihilation SNeutral Product
    LftDistributivity   => lftDistributivity Sum Product
    RgtDistributivity   => rgtDistributivity Sum Product

public export
RingStructure : Type
RingStructure = SetoidAlgebra Theory.Signature

public export
Ring : Type
Ring = Model RingTheory

public export
Zero : Op Signature
Zero = MkOp SNeutral

public export
Plus : Op Signature
Plus = MkOp Sum

public export
Opp : Op Signature
Opp = MkOp SInverse

public export
One : Op Signature
One = MkOp PNeutral

public export
Times : Op Signature
Times = MkOp Product

export
HasPrecedence Signature where
 OpPrecedence Sum      = Just (InfixR 0)
 OpPrecedence SInverse = Just (Prefix 2)
 OpPrecedence Product  = Just (InfixR 1)

export
Show (Op Signature) where
  show (MkOp SNeutral) = "0"
  show (MkOp Sum)      = "+"
  show (MkOp SInverse) = "-"
  show (MkOp PNeutral) = "1"
  show (MkOp Product)  = "*"

export
Finite (Op Signature) where
  enumerate = [Zero, Plus, Opp, One, Times]

export
Finite Axiom where
  enumerate = [ SumLftNeutrality
              , SumCommutativity
              , SumAssociativity
              , SumRgtInverse
              , ProdLftNeutrality
              , ProdRgtNeutrality
              , ProdAssociativity
              , ProdLftAnnihilation
              , ProdRgtAnnihilation
              , LftDistributivity
              , RgtDistributivity
              ]

export
Show Axiom where
  show SumLftNeutrality     = "Additive left neutrality"
  show SumCommutativity     = "Additive commutativity"
  show SumAssociativity     = "Additive associativity"
  show SumRgtInverse        = "Additive right inverse"
  show ProdLftNeutrality    = "Multiplicative left neutrality"
  show ProdRgtNeutrality    = "Multiplicative right neutrality"
  show ProdAssociativity    = "Multiplicative associativity"
  show ProdLftAnnihilation = "Left zero"
  show ProdRgtAnnihilation = "Right zero"
  show LftDistributivity    = "Left distributivity"
  show RgtDistributivity    = "Right distributivity"
