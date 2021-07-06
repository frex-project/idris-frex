module Frexlet.Monoid.Free

import Data.Unit

import Frex
import Frexlet.Monoid
import Frexlet.Monoid.Frex.Construction

%default total

||| The trivial algebra with carrier the unit type
public export
TrivialAlgebra : Algebra Signature
TrivialAlgebra
  = MakeAlgebra
  { U = Unit
  , Semantics = \op,env => case op of
      MkOp Neutral => ()
      MkOp Product => ()
  }

||| The trivial monoid with carrier the unit type
public export
TrivialMonoid : Monoid
TrivialMonoid =
 MkModel
  { Algebra = cast TrivialAlgebra
  , Validate = \case
      LftNeutrality => \ _ => unitIrrelevant
      RgtNeutrality => \ _ => unitIrrelevant
      Associativity => \ _ => unitIrrelevant
  }

public export
||| The frex for the free monoid built out of n variables
FreeFrex : (n : Nat) -> Frex TrivialMonoid (cast $ Fin n)
FreeFrex n = MonoidFrex TrivialMonoid (cast $ Fin n)

||| A free monoid built out of n variables
public export
FreeMonoid : (n : Nat) -> Monoid
FreeMonoid n = (FreeFrex n).Data.Model

public export
SyntacticFrex : (n : Nat) -> Frex (FreeMonoid n) (cast $ Fin 0)
SyntacticFrex n = Construction.Frex (FreeMonoid n) (cast $ Fin 0)

public export
SyntacticExtension : (n : Nat) -> Extension (FreeMonoid n) (cast $ Fin 0)
SyntacticExtension n = (SyntacticFrex n).Data

public export
SyntacticMonoid : (n : Nat) -> Monoid
SyntacticMonoid n = (SyntacticExtension n).Model
