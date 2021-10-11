module Frex.Free.Construction.IdrisMonoid

import Data.Relation.Closure.ReflexiveTransitive
import Data.Relation.Closure.Symmetric

import Control.Relation
import Data.Fin
import Data.Finite
import Data.List
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
import Utils.String

import Frexlet.Monoid.Theory

%default total

%hide Theory.Unit

export
display : {n : Nat} ->
          {lhs, rhs : Term Signature (Fin n)} ->
          Proof MonoidTheory lhs rhs ->
          Doc ()
display prf = vcat $ ("|~" <++> display tmPrinter lhs)
                   :: steps prf

  where

  TM : Type
  TM = Term Signature (Fin n)

  CTX : Type
  CTX = Term Signature (Maybe TM)

  tmPrinter : Printer Signature (Fin n)
  tmPrinter = withNames additive1

  ctxPrinter : Printer Signature (Maybe TM)
  ctxPrinter = withFocus "focus"
             $ withNesting
             $ withVal
             $ withNames additive2

  lemPrinter : Printer MonoidTheory ()
  lemPrinter = withLower $ withRaw additive1

  PA : PresetoidAlgebra Signature
  PA = QuotientData MonoidTheory (cast $ Fin n)

  base : Bool -> TM -> Doc () -> Doc ()
  base b t prf = vcat
    [ "~~" <++> display tmPrinter t
    , indent 2 $ ifThenElse b "..<(" "...(" <++> prf <++> ")"
    ]

  focus : CTX -> Doc ()
  focus ctx = hsep
    ["\\", "focus", "=>"
    , display ctxPrinter ctx]

  cong : {begin, end : TM} -> Bool ->
         Locate Signature (algebra PA) (Step MonoidTheory PA) begin end ->
         Doc ()
  cong b (Here prf)
    = base b (if b then begin else end) $ displayNamed True lemPrinter prf
  cong b (Cong t {lhs} {rhs} prf)
    = base b (plug (algebra PA) t $ if b then lhs else rhs)
    $ "Cong" <++> parens (focus t)
      <++> "$" <++> displayNamed True lemPrinter prf

  step : {begin, end : TM} -> Closure MonoidTheory PA begin end -> Doc ()
  step (Fwd p) = cong False p
  step (Bwd p) = cong True p

  steps  : {begin : TM} -> Derivation MonoidTheory PA begin end -> List (Doc ())
  steps [] = []
  steps (r :: rs) = step r :: steps rs

export
idris : List (String, Lemma MonoidTheory) -> String
idris proofs = show $ vcat $ (header ++) . (lemmas ++)
             $ intersperse ""
             $ proofs <&> \ nmlemma =>
  let
    nm := fst nmlemma
    lemma := snd nmlemma

    xs : List (Doc ())
    xs = map (pretty . show)
       $ take lemma.equation.support names

  in indent 2 $ vcat
  [ prettyEquation additive1 nm xs "U m" lemma.equation
  , pretty nm <++> hsep xs <++> "= CalcWith (cast m) $"
  , indent 2 $ display
             $ deloop
             $ linearise (Just %search) lemma.derivable
  ]

  where

    tmPrinter : Printer Signature (Fin n)
    tmPrinter = withNames additive1

    header : List (Doc ())
    header = map pretty $ lines #"""
import Data.Setoid

import Frex
import Frexlet.Monoid
import Frexlet.Monoid.Notation.Additive

import Notation.Hints

%hide Frex.Axiom.lftNeutrality
%hide Frex.Axiom.rgtNeutrality

parameters (m : Model MonoidTheory)

  infix 0 =~=
  0 (=~=) : (x, y : U m) -> Type
  x =~= y = (cast m).equivalence.relation x y

  %hint
  notation1 : NotationHint m Additive1
  notation1 = m.notationHint Additive1
            (Prelude.cast $ Additive.Model.cast m)

  %hint
  notation2 : Additive2 (Term Signature (Maybe (U m)))
  notation2 = notationAdd2

  Val : U m -> Term Signature (Maybe (U m))
  Val v = Done (Just v)

  (.asContext) :
    (Term Signature (Maybe (U m)) -> Term Signature (Maybe (U m))) ->
    U m -> U m
  f .asContext x = m .Sem (cast $ f (Done Nothing))
                 $ either id (\ k => index k [x])

  Cong : (f : Term Signature (Maybe (U m)) -> Term Signature (Maybe (U m))) ->
         {x, y : U m} -> x =~= y ->
         f .asContext x =~= f .asContext y
  Cong f {x, y} eq = m.cong 1 (cast $ f (Done Nothing)) [x] [y] [eq]


"""#

    lemmas : List (Doc ())
    lemmas = enumerate {a = Axiom} <&> \ ax =>
      indent 2 $ display (withRaw additive1) ax
