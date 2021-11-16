||| The syntax and axioms for monoids
module Frexlet.Monoid.Theory

import Decidable.Equality
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
MonoidTheory = MkPresentation Theory.Signature
                              Theory.Axiom $ \case
    LftNeutrality => lftNeutrality Neutral Product
    RgtNeutrality => rgtNeutrality Neutral Product
    Associativity => associativity         Product

public export
MonoidStructure : Type
MonoidStructure = SetoidAlgebra Signature

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
Show (Op Signature) where
  show (MkOp Neutral) = "Neutral"
  show (MkOp Product) = "Product"

export
Finite (Op Signature) where
  enumerate = [Unit, Prod]

export
Uninhabited (Equal {a = Op Signature} {b = Op Signature}
                (MkOp Neutral) (MkOp Product)) where
  uninhabited Refl impossible

export
Uninhabited (Equal {a = Op Signature} {b = Op Signature}
               (MkOp Product) (MkOp Neutral)) where
  uninhabited Refl impossible

export
DecEq (Op Signature) where
  decEq (MkOp Neutral) (MkOp Neutral) = Yes Refl
  decEq (MkOp Product) (MkOp Product) = Yes Refl
  decEq (MkOp Neutral) (MkOp Product) = No absurd
  decEq (MkOp Product) (MkOp Neutral) = No absurd

export
Eq (Op Signature) where
  MkOp Neutral == MkOp Neutral = True
  MkOp Product == MkOp Product = True
  _ == _ = False

export
Ord (Op Signature) where
  compare (MkOp Neutral) (MkOp Neutral) = EQ
  compare (MkOp Product) (MkOp Product) = EQ
  compare (MkOp Neutral) _ = LT
  compare _ (MkOp Neutral) = GT
  compare (MkOp Product) _ = GT
  compare _ (MkOp Product) = LT

export
Finite Axiom where
  enumerate = [ LftNeutrality
              , RgtNeutrality
              , Associativity
              ]

export
[Raw] Show Axiom where
  show = \case
    LftNeutrality => "LftNeutrality"
    RgtNeutrality => "RgtNeutrality"
    Associativity => "Associativity"

export
[Words] Show Axiom where
  show = \case
    LftNeutrality => "Left neutrality"
    RgtNeutrality => "Right neutrality"
    Associativity => "Associativity"

export
ascii : Printer Signature Unit
ascii = MkPrinter
  { carrier    = "a"
  , varShow    = %search
  , opPatterns = %search
  , opShow     = asciiShow
  , opPrec     = asciiPrec
  , topParens  = False
  , opParens   = False
  } where

  [asciiPrec] HasPrecedence Signature where
    OpPrecedence Product = Just (InfixL 8)

  [asciiShow] Show (Op Signature) where
    show (MkOp Neutral) = "zero"
    show (MkOp Product) = "<>"

export
generic : Printer Signature Unit
generic = MkPrinter
  { carrier    = "a"
  , varShow    = %search
  , opPatterns = %search
  , opShow     = genericShow
  , opPrec     = genericPrec
  , topParens  = False
  , opParens   = False
  } where

  [genericPrec] HasPrecedence Signature where
    OpPrecedence Product = Just (InfixR 0)

  [genericShow] Show (Op Signature) where
    show (MkOp Neutral) = "ε"
    show (MkOp Product) = "•"

export
natPlus : Printer Signature Unit
natPlus = MkPrinter
  { carrier    = "Nat"
  , varShow    = %search
  , opPatterns = %search
  , opShow     = natPlusShow
  , opPrec     = natPlusPrec
  , topParens  = False
  , opParens   = False
  } where

  [natPlusPrec] HasPrecedence Signature where
    OpPrecedence Product = Just (InfixL 8)

  [natPlusShow] Show (Op Signature) where
    show (MkOp Neutral) = "0"
    show (MkOp Product) = "+"

export
additive1 : Printer Signature Unit
additive1 = MkPrinter
  { carrier    = "a"
  , varShow    = %search
  , opPatterns = %search
  , opShow     = additive1Show
  , opPrec     = additive1Prec
  , topParens  = False
  , opParens   = False
  } where

  [additive1Prec] HasPrecedence Signature where
    OpPrecedence Product = Just (InfixL 8)

  [additive1Show] Show (Op Signature) where
    show (MkOp Neutral) = "O1"
    show (MkOp Product) = ".+."

export
additive2 : Printer Signature Unit
additive2 = MkPrinter
  { carrier    = "a"
  , varShow    = %search
  , opPatterns = %search
  , opShow     = additive2Show
  , opPrec     = additive2Prec
  , topParens  = False
  , opParens   = False
  } where

  [additive2Prec] HasPrecedence Signature where
    OpPrecedence Product = Just (InfixL 8)

  [additive2Show] Show (Op Signature) where
    show (MkOp Neutral) = "O2"
    show (MkOp Product) = ":+:"

export
withRaw : Printer Signature a -> Printer MonoidTheory a
withRaw = MkPrinter "MonoidTheory" Raw

export
withWords : Printer Signature a -> Printer MonoidTheory a
withWords = MkPrinter "MonoidTheory" Words
