||| Definitions and functions dealing with single-sorted finitary signatures
module Frex.Presentation

import Data.Fin
import Data.Finite
import Data.Name
import Text.PrettyPrint.Prettyprinter
import Data.Stream
import Data.String
import Frex.Signature
import Frex.Algebra

%default total

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
  display : Printer sig () -> Equation sig -> Doc ()
  display printer (MkEq supp lhs rhs)
    = concat {t = List} [ tele supp, scoped lhs, pretty " ≡ ", scoped rhs]

    where

      tele : Nat -> Doc ()
      tele Z = ""
      tele n = "∀" <++> hsep (map (pretty . show) (take n names)) <+> ". "

      scoped : Term sig (Fin supp) -> Doc ()
      scoped = display (withNames printer)

namespace Presentation

  export
  display : (p : Presentation) ->
            Finite (p .Axiom) =>
            Show (p .Axiom) =>
            Finite (Op p.signature) =>
            Printer p.signature () ->
            Doc ()
  display p printer = vcat
            $ "Operations:"
            :: indent 2 (Signature.display p.signature
                           @{(%search, printer.opPrec, printer.opShow)})
            :: "Axioms:"
            :: map (indent 2 . showAxiom) enumerate

    where

    showAxiom : p .Axiom -> Doc ()
    showAxiom ax = concat {t = List}
                 [pretty (show ax), ": ", display printer (p.axiom ax)]

%hint
public export
castEqHint : {auto castOp : sig1 ~> sig2} ->
   Cast (Equation sig1) (Equation sig2)
castEqHint {castOp} = MkCast $ \eq =>
  MkEq
  { support = eq.support
  , lhs = cast eq.lhs
  , rhs = cast eq.rhs
  }
