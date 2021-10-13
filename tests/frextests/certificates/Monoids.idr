module Monoids

import Data.Unit

import Frex
import Frex.Free.Construction
import Frex.Free.Construction.Combinators

import Decidable.Equality
import Frex.Free.Construction.IdrisMonoid
import Frex.Free.Construction.Idris

import Frexlet.Monoid
import Frexlet.Monoid.Free
import Frexlet.Monoid.Notation.Additive

import Syntax.PreorderReasoning

import System.File

infix 0 ~~
0 (~~) : Rel (U (Construction.Free MonoidTheory $ cast $ Fin n).Data.Model)
(~~) = (Free MonoidTheory $ cast $ Fin n).Data.Model.rel

-- Modulo normalisation:
-- infix 0 ~~~
-- 0 (~~~) : Rel (Term Signature (Fin n))
-- (~~~) = (|-) {pres = MonoidTheory} (QuotientData MonoidTheory (cast (Fin n)))

Trivial : Lemma MonoidTheory
Trivial = mkLemma (FreeMonoidOver $ cast $ Fin 1)
        $ X 0 =-= X 0

Trivial2 : Lemma MonoidTheory
Trivial2 = mkLemma (FreeMonoidOver $ cast $ Fin 2)
         $ X 0 .+. X 1 =-= X 0 .+. X 1

Assoc : Lemma MonoidTheory
Assoc = mkLemma (FreeMonoidOver $ cast $ Fin 3) $
        X 0 .+. (X 1 .+. X 2)
    =-= (X 0 .+. X 1) .+. X 2

RAssoc : Lemma MonoidTheory
RAssoc = mkLemma (FreeMonoidOver $ cast $ Fin 3)
       $ (X 0 .+. X 1) .+. X 2
       =-= X 0 .+. (X 1 .+. X 2)

Units : Lemma MonoidTheory
Units = mkLemma (FreeMonoidOver $ cast $ Fin 1)
      $ (O1 .+. (X 0 .+. O1)) .+. O1 =-= X 0

units : (O1 .+. (X {k = 1} 0 .+. O1)) .+. O1 ~~ X 0
units = byLemma Units

main : IO Unit
main = do
  Right () <- writeFile "build/Proofs.idr" $ IdrisMonoid.idris
                [ ("trivial", Trivial)
                , ("trivial2", Trivial2)
                , ("assoc", Assoc)
                , ("units", Units)
                ]
    | Left err => print err

  Right () <- writeFile "build/GenericProofs.idr" $ Idris.idris
                (withRaw ascii)
                ["Frexlet.Monoid"]
                [ ("trivial", Trivial)
                , ("trivial2", Trivial2)
                , ("assoc", Assoc)
                , ("units", Units)
                ]
    | Left err => print err

  pure ()
