module Main

import Data.String

import Frex
import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Notation.Multiplicative

import Frex.Axiom
import Frex.Free.Construction
import Frex.Free.Construction.Combinators
import Frex.Free.Construction.Linear

import Data.Fin
import Decidable.Equality
import Data.Either.Extra
import Data.Setoid.Vect.Inductive
import Text.PrettyPrint.Prettyprinter

import System.File

%default total

[BORING] Show a where
  show _ = "boring"

FrexNat : {0 x : Type} -> Frex Commutative.Nat.Additive (irrelevantCast x)
FrexNat = Frex.Construction.Frex Commutative.Nat.Additive (irrelevantCast x)

Sta' : {0 x : Type} -> Nat -> U ((FrexNat {x}).Data.Model)
Sta' = (FrexNat).Data.Embed.H.H

Dyn' : {0 x : Type} -> x -> U (FrexNat {x}).Data.Model
Dyn' = (FrexNat {x}).Data.Var.H

export infix 0 ~~
0 (~~) : (lhs, rhs : Term (EvaluationSig (CommutativeMonoidTheory).signature Nat) x) -> Type
(~~) = (FrexNat).Data.Model.rel

%hint
notation : {x : Type} -> Action2 Nat (U (FrexNat {x}).Data.Model)
notation = NatAction2 (FrexNat {x}).Data.Model

myProof : (~~) {x = Fin 3}
    ((Dyn' 0 :+: Sta' 6) :+: Dyn' 1 :+: (Dyn' 2 :+: Sta' 2))
    (Dyn' 1 :+: ((the Nat 1) *: Dyn' 0) :+: Dyn' 2 :+: Sta' 8)
myProof
  = Frex.prove 3 (Monoid.Commutative.Frex Nat.Additive)
          $ (Dyn FZ .+. Sta 6) .+. Dyn 1 .+. (Dyn 2 .+. Sta 2) =-=
            Dyn 1 .+. ((the Nat 1) *. Dyn 0) .+. Dyn 2 .+. Sta 8

main : IO Builtin.Unit
main = do
  -- unicode
  let separator : String := replicate 72 '-'
  let banner = \ str => unlines [separator, "-- " ++ str, separator]
  let printer = MkPrinter "CommutativeMonoidTheory" (Eval @{Words})
              $ withNesting $ withEvaluation $ withNames generic
  putStrLn $ banner "Commutative Monoid Theory"
  printLn  $ display CommutativeMonoidTheory
           $ MkPrinter "CommutativeMonoidTheory" Words $ withParens generic
  putStrLn $ banner "Simple proof"
  printLn  $ Proof.display unicode printer @{BORING} myProof

  let output = #"\documentclass{article}"#
              :: latexPreamble
              ::
              [ #"\begin{document}"#
              , #"\subsection{myProof}"#
              , show $ display latex printer @{BORING} myProof
              , #"\end{document}"#
              ]

  let compact = #"\documentclass{article}"#
            :: compactLatexPreamble
            ::
            [ #"\begin{document}"#
            , #"\subsection{myProof}"#
            , show $ display compactLatex printer @{BORING} myProof
            , #"\end{document}"#
            ]
  -- latex
  Right () <- writeFile "build/commutative-equations-output.tex" (unlines output)
    | Left err => print err
  Right () <- writeFile "build/commutative-equations-output-compact.tex" $
    unlines compact
    | Left err => print err

  pure ()
