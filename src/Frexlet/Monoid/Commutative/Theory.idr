||| The syntax and axioms for monoids
module Frexlet.Monoid.Commutative.Theory

import Frex

import public Frexlet.Monoid

%default total

public export
data Axiom
  = Mon Monoid.Theory.Axiom
  | Commutativity

public export
CommutativeMonoidTheory : Presentation
CommutativeMonoidTheory = MkPresentation Theory.Signature Commutative.Theory.Axiom $ \case
    Mon ax => (MonoidTheory).axiom ax
    Commutativity => commutativity Product

public export
CommutativeMonoid : Type
CommutativeMonoid = Model CommutativeMonoidTheory

||| Smart constructor for commutative monoids
public export
MkCommutativeMonoid
  : (monoid : Monoid) ->
    (commutativity : ValidatesEquation
                       (Axiom.commutativity {sig = Theory.Signature} Product)
                       (monoid.Algebra)) ->
    CommutativeMonoid
MkCommutativeMonoid monoid commutativity = MkModel
  { Algebra = monoid.Algebra
  , Validate = \case
      Mon ax        => monoid.Validate ax
      Commutativity => commutativity
  }

public export
Cast CommutativeMonoid Monoid where
  cast cmonoid = MkModel
    { Algebra  = cmonoid.Algebra
    , Validate = \ax => cmonoid.Validate (Mon ax)
    }

public export
Zero : Op Signature
Zero = MkOp Neutral

public export
Plus : Op Signature
Plus = MkOp Product

export
[Raw] Show Commutative.Theory.Axiom where
  show = \case
    Mon ax => show @{Raw} ax
    Commutativity => "Commutativity"

export
[Words] Show Commutative.Theory.Axiom where
  show = \case
    Mon ax => show @{Words} ax
    Commutativity => "Commutativity"

export
Finite Commutative.Theory.Axiom where
  enumerate = map Mon enumerate ++ [Commutativity]

export
withRaw : Printer Signature a -> Printer CommutativeMonoidTheory a
withRaw = MkPrinter "CommutativeMonoidTheory" Raw

export
withWords : Printer Signature a -> Printer CommutativeMonoidTheory a
withWords = MkPrinter "CommutativeMonoidTheory" Words
