module Frex.Free.Construction.Idris

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

%default total

export
display : {n : Nat} ->
          {pres : Presentation} ->
          Printer pres () ->
          {lhs, rhs : Term pres.signature (Fin n)} ->
          Proof pres lhs rhs ->
          Doc ()
display p prf = vcat
   $ ("|~" <++> display tmPrinter lhs)
   :: steps prf

  where

  tmPrinter : Printer pres.signature (Fin n)
  tmPrinter = withNames p.sigPrinter

  TM : Type
  TM = Term pres.signature (Fin n)

  CTX : Type
  CTX = Term pres.signature (Maybe TM)


  ctxPrinter : Printer pres.signature (Maybe TM)
  ctxPrinter = withFocus "focus"
             $ withNesting
             $ withVal
             $ withQuoted tmPrinter

  lemPrinter : Printer pres ()
  lemPrinter = withLower p

  PA : PresetoidAlgebra pres.signature
  PA = QuotientData pres (cast $ Fin n)

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
         Locate pres.signature (algebra PA) (Step pres PA) begin end ->
         Doc ()
  cong b (Here prf)
    = base b (if b then begin else end) $ displayNamed True lemPrinter prf
  cong b (Cong t {lhs} {rhs} prf)
    = base b (plug (algebra PA) t $ if b then lhs else rhs)
    $ "Cong" <++> parens (focus t)
      <++> "$" <++> displayNamed True lemPrinter prf

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
        Finite (Op pres.signature) =>
        Finite (pres .Axiom) =>
        Printer pres () ->
        List String ->                -- additional imports
        List (String, Lemma pres) ->  -- results to print certificates for
        String
idris printer is proofs = with [List.(++), Prelude.(.)] show $ vcat
             $ (imports ++)
             . (banner "Hiding definitions conflicting with axiom names" ++)
             . (hidingList ++)
             . (pragmas ++)
             . (parametersBlock ++)
             . (banner "Boilerplate: equivalence & congruence combinator" ++)
             . (header ++)
             . (banner "Term combinators" ++)
             . (operations "m .Algebra .algebra .Semantics" tmPrinter ++)
             . (banner "Context combinators" ++)
             . (operations "Call" ctxPrinter ++)
             . (banner "Proofs the axioms hold in the model" ++)
             . (lemmas ++)
             . (banner "Lemmas" ++)
             $ intersperse ""
             $ proofs <&> \ nmlemma =>
  let
    nm := fst nmlemma
    lemma := snd nmlemma

    xs : List (Doc ())
    xs = map (pretty . show)
       $ take lemma.equation.support names

  in indent 2 $ vcat
  [ pretty tmPrinter.sigPrinter nm xs lemma.equation
  , pretty nm <++> hsep xs <++> "= CalcWith (cast m) $"
  , indent 2 $ display tmPrinter
             $ deloop
             $ linearise (Just %search) lemma.derivable
  ]

    where

    banner : String -> List (Doc ())
    banner str = pretty (replicate 72 '-')
              :: map (("--" <++>) . pretty) (lines str)
              ++ [""]

    tmPrinter : Printer pres ()
    tmPrinter = ({ sigPrinter->carrier := "U m" } printer)

    ctxPrinter : Printer pres ()
    ctxPrinter = { sigPrinter->carrier $= \ c => "Term Sig (Maybe (\{c}))" }
                 (withQuoted tmPrinter)

    imports : List (Doc ())
    imports = map (("import" <++>) . pretty) ("Frex" :: is)
              ++ [""]

    hidingList : List (Doc ())
    hidingList =
      let nms = flip List.mapMaybe (enumerate {a = pres .Axiom}) $ \ ax =>
                  do let nm = uncapitalise (show @{printer.axiomShow} ax)
                     guard $ elem nm $ the (List String)
                       [ "lftNeutrality"
                       , "rgtNeutrality"
                       , "associativity"
                       , "commutativity"
                       , "lftInverse"
                       , "rgtInverse"
                       , "lftAnnihilation"
                       , "rgtAnnihilation"
                       , "lftDistributivity"
                       , "rgtDistributivity"
                       , "involutivity"
                       , "antidistributivity"
                       ]
                     pure ("%hide Axiom." <+> pretty nm)
      in ifThenElse (null nms) nms (nms ++ [""])

    pragmas : List (Doc ())
    pragmas = ["%unbound_implicits off"]

    parametersBlock : List (Doc ())
    parametersBlock =
      ["", pretty "parameters (m : Model \{tmPrinter.theoryName})", ""]

    header : List (Doc ())
    header = map pretty $ lines #"""
  infix 0 =~=
  0 (=~=) : U m -> U m -> Type
  x =~= y = (cast m).equivalence.relation x y

  Sig : Signature
  Sig = \#{tmPrinter.theoryName} .signature

  Val : U m -> Term Sig (Maybe (U m))
  Val v = Done (Just v)

  0 Context : Type
  Context = Term Sig (Maybe (U m)) -> Term Sig (Maybe (U m))

  (.asContext) : Context -> (U m -> U m)
  f .asContext x = m .Sem (cast $ f (Done Nothing))
                 $ either id (\ k => index k [x])

  Cong : (f : Context) -> {x, y : U m} ->
         x =~= y -> f .asContext x =~= f .asContext y
  Cong f {x, y} eq = m.cong 1 (cast $ f (Done Nothing)) [x] [y] [eq]


"""#

    operations : String -> Printer pres () -> List (Doc ())
    operations call p = enumerate {a = Op (pres .signature)} <&> \ op =>
      let nm = pretty (show @{p.sigPrinter.opShow} op) in
      let xs = map (pretty . show) (take op.arity names) in
      Doc.indent 2 $ vcat
        $ toList ((<++> nm) <$> display p.sigPrinter op) ++
        [ display p.sigPrinter op
        , hsep [ Term.display (withNames p.sigPrinter) (Call op (tabulate Done))
               , "="
               , pretty call
               , "(MkOp"
               , pretty (showArg @{p.sigPrinter.opPatterns} op) <+> ")"
               , list xs ]
        , ""
        ]

    lemmas : List (Doc ())
    lemmas = enumerate {a = pres .Axiom} <&> \ ax =>
      indent 2 $ Axiom.display tmPrinter ax
