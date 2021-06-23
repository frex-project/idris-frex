||| Definitions and functions dealing with single-sorted finitary signatures
module Frex.Presentation

import Frex.Signature
import Frex.Algebra

public export
record Equation (Sig : Signature) where
  constructor MkEq
  0 Var : Type
  lhs, rhs : Term Sig Var

public export
record Presentation where
  constructor MkPresentation
  signature : Signature
  0 Axiom   : Type
  axiom     : (ax : Axiom) -> Equation signature

public export %hint
projectSignature : Presentation -> Signature
projectSignature pres = pres.signature
