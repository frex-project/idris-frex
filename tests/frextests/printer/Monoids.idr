module Main

import Data.String

import Frex
import Frexlet.Monoid.Theory
import Frexlet.Monoid
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

-- Using a concrete name so that the constraints when forming `X k` compute
infix 0 ~~
(~~) : Term Signature (Fin 10) -> Term Signature (Fin 10) -> Type
(~~) = (|-) {pres = MonoidTheory}
            (QuotientData MonoidTheory (irrelevantCast (Fin 10)))

myProof : (X 0 .*. I1) ~~ (I1 .*. X 0)
myProof
  = Free.prove (FreeMonoidOver _)
  $ (X 0 .*. I1) =-= (I1 .*. X 0)

myProof2 : (X 0 .*. (X 0 .*. I1))
        ~~ (X 0 .*. (I1 .*. X 0))
myProof2
  = Free.prove (FreeMonoidOver _)
  $   (X 0 .*. (X 0 .*. I1))
  =-= (X 0 .*. (I1 .*. X 0))

myProof3 : (X 0 .*. (X 1 .*. (X 2 .*. X 3)))
        ~~ (X 0 .*. I1 .*. (X 1 .*. X 2 .*. X 3))
myProof3
  = Free.prove (FreeMonoidOver _)
  $   (X 0 .*. (X 1 .*. (X 2 .*. X 3)))
  =-= (X 0 .*. I1 .*. (X 1 .*. X 2 .*. X 3))


main : IO Builtin.Unit
main = do
  -- unicode
  let separator : String := replicate 72 '-'
  let banner = \ str => unlines [separator, "-- " ++ str, separator]
  let printer = withWords $ withParens $ withNesting $ withNames generic
  putStrLn $ banner "Monoid Theory"
  printLn  $ display MonoidTheory (withWords $ withParens generic)
  putStrLn $ banner "Simple proof"
  printLn  $ Proof.display unicode printer @{BORING} myProof
  putStrLn $ banner "Proof with congruence"
  printLn  $ display unicode printer @{BORING} myProof2
  putStrLn $ banner "Proof with different congruences"
  printLn  $ display unicode printer @{BORING} myProof3

  let output = #"\documentclass{article}"#
              :: latexPreamble
              ::
              [ #"\begin{document}"#
              , #"\subsection{myProof}"#
              , show $ display latex printer @{BORING} myProof
              , #"\subsection{myProof2}"#
              , show $ display latex printer @{BORING} myProof2
              , #"\subsection{myProof3}"#
              , show $ display latex printer @{BORING} myProof3
              , #"\end{document}"#
              ]

  let compact = #"\documentclass{article}"#
            :: compactLatexPreamble
            ::
            [ #"\begin{document}"#
            , #"\subsection{myProof}"#
            , show $ display compactLatex printer @{BORING} myProof
            , #"\subsection{myProof2}"#
            , show $ display compactLatex printer @{BORING} myProof2
            , #"\subsection{myProof3}"#
            , show $ display compactLatex printer @{BORING} myProof3
            , #"\end{document}"#
            ]
  -- latex
  Right () <- writeFile "build/equations-output.tex" (unlines output)
    | Left err => print err
  Right () <- writeFile "build/equations-output-compact.tex" $
    unlines compact
    | Left err => print err

  pure ()
