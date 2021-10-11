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
import Utils.String

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

public export
record Printer (pres : Presentation) (a : Type) where
  constructor MkPrinter
  axiomShow  : Show pres.Axiom
  sigPrinter : Printer pres.signature a

||| Used to print a definition corresponding to an axiom
export
withLower : Presentation.Printer pres a -> Printer pres a
withLower p = { axiomShow := lowerAxiom } p where

  [lowerAxiom] Show pres.Axiom where
    show ax = uncapitalise (show @{p.axiomShow} ax)

||| Used to print a definition corresponding to an axiom
export
withNames : Presentation.Printer pres () -> Printer pres (Fin n)
withNames = { sigPrinter $= withNames }

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


  export
  prettyEquation : Printer sig () ->
                   String -> List (Doc ()) -> String ->
                   Equation sig -> Doc ()
  prettyEquation p nm xs ty eq =
        let tmPrinter = withNames p in
        pretty nm <++> colon
                  <++> parens (concatWith (\ p, q => (p <+> comma <++> q)) xs
                               <++> colon <++> pretty ty)
                  <++> "->"
                  <++> display tmPrinter eq.lhs
                  <++> "=~="
                  <++> display tmPrinter eq.rhs

namespace Presentation

  export
  display : (pres : Presentation) ->
            Finite (pres .Axiom) =>
            Finite (Op pres.signature) =>
            Printer pres () ->
            Doc ()
  display pres p = vcat
            $ "Operations:"
            :: indent 2 (Signature.display pres.signature p.sigPrinter)
            :: "Axioms:"
            :: map (indent 2 . showAxiom) enumerate

    where

    showAxiom : pres .Axiom -> Doc ()
    showAxiom ax = hcat
                 [ pretty (show @{p.axiomShow} ax)
                 , ": "
                 , display p.sigPrinter (pres.axiom ax)]

namespace Axiom

  export
  display : {pres : _} -> Printer pres () -> pres .Axiom -> Doc ()
  display p ax =
    let rawAx = show @{p.axiomShow} ax; nm = uncapitalise rawAx in
    let eq = pres .axiom ax in
    let xs = map (pretty . show) $ take eq.support names in
      vcat [ prettyEquation p.sigPrinter nm xs "U m" eq
           , pretty nm <++> hsep xs <++> "="
             <++> "m.Validate" <++> pretty rawAx
             <++> parens (#"\ k => index k"# <++> group (list xs))
           , ""
           ]

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
