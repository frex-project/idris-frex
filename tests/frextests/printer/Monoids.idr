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
  putStrLn $ banner "Monoid Theory"
  printLn  $ display MonoidTheory
  putStrLn $ banner "Simple proof"
  printLn  $ display unicode @{BORING} myProof
  putStrLn $ banner "Proof with congruence"
  printLn  $ display unicode @{BORING} myProof2
  putStrLn $ banner "Proof with different congruences"
  printLn  $ display unicode @{BORING} myProof3

  -- latex
  Right () <- writeFile "build/equations-output.tex" $
    unlines [ "\\documentclass{article}"
            , "\\usepackage{amsmath}"
            , "\\usepackage{newunicodechar}"
            , "\\newunicodechar{ε}{\\ensuremath{\\varepsilon}}"
            , "\\newunicodechar{•}{\\ensuremath{\\bullet}}"
            , "\\begin{document}"
            , "\\subsection{myProof}"
            , show $ display latex @{BORING} myProof
            , "\\subsection{myProof2}"
            , show $ display latex @{BORING} myProof2
            , "\\subsection{myProof3}"
            , show $ display latex @{BORING} myProof3
            , "\\end{document}"
            ]
    | Left err => print err

  pure ()
