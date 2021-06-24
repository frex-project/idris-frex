||| Definitions and functions dealing with single-sorted finitary signatures
module Frex.Presentation

import Data.Fin
import Data.Finite
import Data.Name
import Text.PrettyPrint.Prettyprinter
import Data.Stream
import Data.String
import Data.Vect
import Frex.Signature
import Frex.Algebra

public export
record Equation (Sig : Signature) where
  constructor MkEq
  support : Nat
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

namespace Equation

  export
  display : (Show (Op sig), HasPrecedence sig) =>
            Bool -> Equation sig -> Doc ()
  display b (MkEq supp lhs rhs)
    = with Prelude.(::) concat [ tele supp, scoped lhs, pretty " ≡ ", scoped rhs]

    where

      tele : Nat -> Doc ()
      tele Z = ""
      tele n = "∀" <++> hsep (map (pretty . show) (take n names)) <+> ". "

      prettyName : {n : Nat} -> Term sig (Fin n) -> Term sig Name
      prettyName = map (\ k => index (cast k) names)

      scoped : {n : Nat} -> Term sig (Fin n) -> Doc ()
      scoped = display b . prettyName

namespace Presentation

  export
  display : (p : Presentation) ->
            Finite (p .Axiom) =>
            Show (p .Axiom) =>
            Finite (Op p.signature) =>
            Show (Op p.signature) =>
            HasPrecedence p.signature =>
            Doc ()
  display p = vcat
            $ "Operations:"
            :: indent 2 (display p.signature)
            :: "Axioms:"
            :: map (indent 2 . showAxiom) enumerate

    where

    showAxiom : p .Axiom -> Doc ()
    showAxiom ax = concat {t = List}
                 [pretty (show ax), ": ", display True (p.axiom ax)]
