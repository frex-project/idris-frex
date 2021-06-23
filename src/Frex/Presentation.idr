||| Definitions and functions dealing with single-sorted finitary signatures
module Frex.Presentation

import Data.Fin
import Data.String
import Frex.Signature
import Frex.Algebra

public export
record Equation (Sig : Signature) where
  constructor MkEq
  0 support : Nat
  lhs, rhs : Term Sig (Fin support)

public export
record Presentation where
  constructor MkPresentation
  signature : Signature
  0 Axiom   : Type
  axiom     : (ax : Axiom) -> Equation signature

public export %hint
projectSignature : Presentation -> Signature
projectSignature pres = pres.signature

export
(Show (Op sig), HasPrecedence sig) => Show (Equation sig) where
  show (MkEq _ lhs rhs) = unwords [show lhs, "=", show rhs]
