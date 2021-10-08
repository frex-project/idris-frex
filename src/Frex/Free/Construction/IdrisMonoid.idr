module Frex.Free.Construction.IdrisMonoid

import Data.Relation.Closure.ReflexiveTransitive
import Data.Relation.Closure.Symmetric

import Control.Relation
import Data.Fin
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

import Frexlet.Monoid.Theory

%default total

%hide Theory.Unit

export
withVal : Signature.Printer sig a -> Printer sig a
withVal p = { varShow := valVar } p where

  [valVar] Show a where
    showPrec d x = showCon d "Val" $ showArg @{varShow p} x

export
display : {n : Nat} ->
          {lhs, rhs : Term Signature (Fin n)} ->
          Proof MonoidTheory lhs rhs ->
          Doc Unit
display prf =
   vcat
   [ "|~" <++> display tmPrinter lhs
   , vcat (steps prf)
   ] where

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
  base b t p = vcat
    [ ifThenElse b "~:" ":~" <++> display tmPrinter t
    , "  ...(" <++> p <++> ")"
    ]

  focus : CTX -> Doc ()
  focus ctx = hsep
    ["\\", "focus", "=>"
    , display ctxPrinter ctx]

  cong : {begin, end : TM} -> Bool ->
         Locate Signature (algebra PA) (Step MonoidTheory PA) begin end ->
         Doc ()
  cong b (Here p)
    = base b (if b then begin else end) $ displayNamed True lemPrinter p
  cong b (Cong t {lhs} {rhs} p)
    = base b (plug (algebra PA) t $ if b then lhs else rhs)
    $ "Cong" <++> parens (focus t) <++> "$" <++> displayNamed True lemPrinter p

  step : {begin, end : TM} -> Closure MonoidTheory PA begin end -> Doc ()
  step (Fwd p) = cong False p
  step (Bwd p) = cong True p

  steps  : {begin : TM} -> Derivation MonoidTheory PA begin end -> List (Doc ())
  steps [] = []
  steps (r :: rs) = step r :: steps rs

export
idris : List (String, Lemma MonoidTheory) -> String
idris lemmas = show $ vcat $ (header ++)
             $ intersperse ""
             $ lemmas <&> \ nmlemma =>
  let
    nm := fst nmlemma
    lemma := snd nmlemma

    tmPrinter : Printer Signature (Fin lemma.equation.support)
    tmPrinter = withNames additive1

    xs : List (Doc ())
    xs = map (pretty . show)
       $ take lemma.equation.support names

  in indent 2 $ vcat
  [ pretty nm <++> colon
              <++> parens (concatWith (\ p, q => (p <+> comma <++> q)) xs
                           <++> colon <++> "U m")
              <++> "->"
              <++> display tmPrinter lemma.equation.lhs
              <++> "=~="
              <++> display tmPrinter lemma.equation.rhs
  , pretty nm <++> hsep xs <++> "= CalcWith (cast m) $"
  , indent 2 $ display
             $ deloop
             $ linearise (Just %search) lemma.derivable
  ]

  where

    header : List (Doc ())
    header = map pretty $ lines #"""
import Data.Setoid

import Frex
import Frexlet.Monoid
import Frexlet.Monoid.Notation.Additive

import Notation.Hints

%hide Frex.Axiom.lftNeutrality
%hide Frex.Axiom.rgtNeutrality

export
cast : Term sig (Maybe a) -> Term sig (Either a (Fin 1))
cast = map (maybe (Right FZ) Left)

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


  lftNeutrality : (x : U m) -> O1 .+. x =~= x
  lftNeutrality x = m.Validate LftNeutrality (\ _ => x)

  rgtNeutrality : (x : U m) -> x .+. O1 =~= x
  rgtNeutrality x = m.Validate RgtNeutrality (\ _ => x)

  associativity : (x, y, z : U m) -> x .+. (y .+. z) =~= (x .+. y) .+. z
  associativity x y z = m.Validate Associativity (\ k => index k [x,y,z])
"""#
