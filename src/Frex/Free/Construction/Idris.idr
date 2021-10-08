module Frex.Free.Construction.Idris

import Data.Relation.Closure.ReflexiveTransitive
import Data.Relation.Closure.Symmetric

import Control.Relation
import Data.Fin
import Data.Name
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
          Printer pres () ->
          {lhs, rhs : Term pres.signature (Fin n)} ->
          Derivation pres (QuotientData pres (cast (Fin n))) lhs rhs ->
          Doc ()
display p prf =
   vcat
   [ "|~" <++> display printer lhs
   , vcat (steps prf)
   ] where

  printer : Printer pres.signature (Fin n)
  printer = withNames p.sigPrinter

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
    = "sym" <++> "$" <++> d

  base : Bool -> TM -> Doc () -> Doc ()
  base b t p = vcat
    [ "~~" <++> display printer t
    , "  ...(" <++> byProof b p <++> ")"
    ]

  focus : CTX -> Doc ()
  focus ctx = hsep
    ["\\", "focus", "=>"
    , display (withFocus "focus" $ withNesting printer) ctx]

  cong : {begin, end : TM} -> Bool ->
         Locate pres.signature (algebra PA) (Step pres PA) begin end ->
         Doc ()
  cong b (Here prf)
    = base b (if b then begin else end) $ displayNamed True p prf
  cong b (Cong t {lhs} {rhs} prf)
    = base b (plug (algebra PA) t $ if b then lhs else rhs)
    $ "cong" <++> parens (focus t) <++> "$" <++> displayNamed True p prf

  step : {begin, end : TM} -> Closure pres PA begin end -> Doc ()
  step (Fwd p) = cong False p
  step (Bwd p) = cong True p

  steps  : {begin : TM} -> Derivation pres PA begin end -> List (Doc ())
  steps [] = []
  steps (r :: rs) = step r :: steps rs

export
idris : {pres : Presentation} ->
        Ord (Op pres.signature) =>
        DecEq (Op pres.signature) =>
        Printer pres () ->
        (name : String) -> Lemma pres -> String
idris p nm lemma =
  let xs : List (Doc ()) = map (pretty . show)
                         $ take lemma.equation.support names
  in show $ vcat
  [ pretty nm <++> colon
              <++> parens (concatWith (\ p, q => (p <+> comma <++> q)) xs
                           <++> colon <++> "Nat")
              <++> "->"
              <++> Term.display (withNames $ p.sigPrinter) lemma.equation.lhs
              <++> "==="
              <++> Term.display (withNames $ p.sigPrinter) lemma.equation.rhs
  , pretty nm <++> hsep xs <++> "= Calc $"
  , indent 2 $ display p
             $ deloop
             $ linearise (Just %search) lemma.derivable
  ]
