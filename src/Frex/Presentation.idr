||| Definitions and functions dealing with single-sorted finitary signatures
module Frex.Presentation

import Data.Fin
import Data.Name
import Data.String
import Data.Stream
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

export
(Show (Op sig), HasPrecedence sig) => Show (Equation sig) where
  show (MkEq supp lhs rhs)
    = with Prelude.(::) concat [ tele supp, scoped lhs, " ≡ ", scoped rhs]

    where

      tele : Nat -> String
      tele Z = ""
      tele n = "∀ " ++ unwords (map show (take n names)) ++ ". "

      prettyName : {n : Nat} -> Term sig (Fin n) -> Term sig Name
      prettyName = map (\ k => index (cast k) names)

      scoped : {n : Nat} -> Term sig (Fin n) -> String
      scoped = display True . prettyName



public export
interface Finite (0 a : Type) where
  enumerate : List a

export
display : (p : Presentation) ->
          Finite (p .Axiom) =>
          Show (p .Axiom) =>
          Show (Op p.signature) =>
          HasPrecedence p.signature =>
          String
display p = unlines $ map showAxiom enumerate where

  showAxiom : p .Axiom -> String
  showAxiom ax = concat $ with Prelude.(::) [ show ax, ": ", show (p.axiom ax)]
