module Frexlet.Monoid.Examples

import Frex
import Frexlet.Monoid.Theory

import Frex.Free.Construction
import Frex.Free.Construction.Linear

import Text.PrettyPrint.Prettyprinter

%default total

Zero : Term Signature (Fin n)
Zero = call {n = Z} Neutral

(*) : Term Signature (Fin n) -> Term Signature (Fin n) ->
      Term Signature (Fin n)
(*) = call {n = 2} Product

[BORING] Show a where
  show _ = "boring"

infix 0 ~~
(~~) : Term Signature (Fin 1) -> Term Signature (Fin 1) -> Type
(~~) = (|-) {pres = MonoidTheory}
            (QuotientData MonoidTheory (irrelevantCast (Fin 1)))

myProof : (X 0 * Zero) ~~ (Zero * X 0)
myProof
  = Transitive (ByAxiom RgtNeutrality (const (X 0)))
  $ Sym $ ByAxiom LftNeutrality (const (X 0))

view : String
view = show $ display @{BORING} myProof

myProof2 : (X 0 * (X 0 * Zero))
        ~~ (X 0 * (Zero * X 0))
myProof2
  = Congruence {n = 2} (X 0 * X 1)
      {lhs = \case { FZ => X 0; FS FZ => X 0 * Zero}}
      {rhs = \case { FZ => X 0; FS FZ => Zero * X 0}}
    $ \case
         FZ => Refl (X 0)
         FS FZ => myProof

view2 : String
view2 = show $ display @{BORING} myProof2
