module Frex.Free.Construction.Idris

import Data.Relation.Closure.ReflexiveTransitive
import Data.Relation.Closure.Symmetric

import Control.Relation
import Data.Fin
import Data.Relation
import Data.Setoid
import Decidable.Equality
import Frex.Signature
import Frex.Presentation
import Frex.Lemma
import Frex.Algebra
import Frex.Free.Construction
import Frex.Free.Construction.Linear

import Data.String
import Text.PrettyPrint.Prettyprinter

%default total

export
display : {n : Nat} ->
          {pres : Presentation} ->
          Show (pres .Axiom) =>
          Show (Op pres.signature) =>
          HasPrecedence pres.signature =>
          {lhs, rhs : Term pres.signature (Fin n)} ->
          Derivation pres (QuotientData pres (cast (Fin n))) lhs rhs ->
          Doc ()
display @{showR} prf = vcat
   [ "|~" <++> pretty (show lhs)
   , vcat (steps prf)
   ] where

  TM : Type
  TM = Term pres.signature (Fin n)

  CTX : Type
  CTX = Term pres.signature (Maybe TM)

  PA : PresetoidAlgebra pres.signature
  PA = QuotientData pres (cast $ Fin n)

  byProof : Bool -> Doc () -> Doc ()
  byProof False d
    = d
  byProof True  d
    = "symmetric" <++> "$" <++> d

  base : Bool -> TM -> Doc () -> Doc ()
  base b t p = vcat
    [ "<~" <++> pretty (show t)
    , "  ...(" <++> byProof b p <++> ")"
    ]

  focus : CTX -> Doc ()
  focus ctx = hsep ["\\", "focus", "=>", displayUsing True "focus" ctx]

  cong : {begin, end : TM} -> Bool ->
         Locate pres.signature (algebra PA) (Step pres PA) begin end ->
         Doc ()
  cong b (Here p)
    = base b (if b then begin else end) $ display p
  cong b (Cong t {lhs} {rhs} p)
    = base b (plug (algebra PA) t $ if b then lhs else rhs)
    $ "cong" <++> parens (focus t) <++> "$" <++> display p

  step : {begin, end : TM} -> Closure pres PA begin end -> Doc ()
  step (Fwd p) = cong False p
  step (Bwd p) = cong True p

  steps  : {begin : TM} -> Derivation pres PA begin end -> List (Doc ())
  steps [] = []
  steps (r :: rs) = step r :: steps rs

export
idris : {pres : Presentation} ->
        Show (pres .Axiom) =>
        DecEq (Op pres.signature) =>
        Show (Op pres.signature) =>
        HasPrecedence pres.signature =>
        (name : String) -> Lemma pres -> String
idris nm lemma = show $ vcat
  [ pretty nm <++> ": (m : Monoid) -> (x1, ..., x_n : U m) -> m.rel lhs rhs"
  , pretty nm <++> hsep ?a <++> "="
  , indent 2 $ display $ linearise (Just %search) lemma.derivable
  ]
