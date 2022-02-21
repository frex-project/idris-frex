module Frex.Free.Construction.Linear

import Frex.Signature
import Frex.Algebra
import Frex.Algebra.Abstract
import Frex.Presentation
import Frex.Free.Construction

import Data.Setoid
import Data.String
import Data.Relation
import Data.Relation.Closure.Symmetric
import Data.Relation.Closure.ReflexiveTransitive
import Decidable.Equality
import Text.PrettyPrint.Prettyprinter

%default total

%hide Data.Relation.Rel

namespace PresetoidAlgebra

  public export
  (.bindTerm) : {0 sig : Signature} -> {0 x : Type} ->
       (a : PresetoidAlgebra sig)
    -> (t : Term sig x) -> (env : x -> U a)
    -> (U a)
  a .bindTerm = bindTerm {a = a.algebra}

public export
data Step : (pres : Presentation)
            -> (a : PresetoidAlgebra pres.signature)
            -> Rel (U a) where
  Include : {x, y : U a} -> a.relation x y
            -> Step pres a x y
  ByAxiom : {0 a : PresetoidAlgebra pres.signature}
            -> (eq : Axiom pres)
            -> (env : Fin (pres.axiom eq).support -> U a)
            -> Step pres a
                 (a .bindTerm (pres.axiom eq).lhs env)
                 (a .bindTerm (pres.axiom eq).rhs env)

namespace Step

  export
  display : {pres : Presentation} ->
            {a : PresetoidAlgebra pres.signature} ->
            ({x, y : U a} -> Show (a.relation x y)) =>
            Show (pres .Axiom) =>
            {0 x, y : U a} -> Step pres a x y -> Doc ()
  display @{showR} (Include p) = pretty (show @{showR} p)
  display (ByAxiom eq env) = pretty (show eq)

  export
  displayNamed :
            (applied : Bool) ->
            {pres : Presentation} ->
            Printer pres () ->
            {0 x, y : Term pres.signature (Fin n)} ->
            Step pres (QuotientData pres (cast (Fin n))) x y -> Doc ()
  displayNamed applied p (Include prf) = pretty (show prf)
  displayNamed applied p (ByAxiom eq env) =
    let ax = pretty (show @{p.axiomShow} eq) in
    if not applied then ax else
      let printer = withNames $ { topParens := True } p.sigPrinter in
      hsep (ax :: toList (tabulate (displayPrec printer App . env)))

public export
plug : (a : Algebra sig) ->
       (ctx : Term sig (Maybe (U a))) ->
       (t : U a) -> U a
plug a t u = bindTerm t (fromMaybe u)

infixr 0 :.:
public export
(:.:) : {0 sig : Signature} ->
        Term sig (Maybe a) ->
        Term sig (Maybe a) ->
        Term sig (Maybe a)
g :.: f = bindTerm {a = Free _ _} g (maybe f (Done . Just))

export
plugFusion :
  {0 sig : Signature} -> {a : Algebra sig} ->
  (ctx2, ctx1 : Term sig (Maybe (U a))) ->
  (t : U a) ->
  plug a ctx2 (plug a ctx1 t)
  === plug a (ctx2 :.: ctx1) t
plugFusion ctx2 ctx1 t
  = sym $ trans (bindAssociative ctx2 (maybe ctx1 (Done . Just)) (fromMaybe t))
  $ bindTermExtensional ctx2 $ \case
      Nothing => Refl
      Just v => Refl

public export
data Locate : (sig : Signature) -> (a : Algebra sig) ->
              Rel (U a) -> Rel (U a) where
  ||| We prove the equality by invoking a rule at the
  ||| toplevel
  Here : {0 r : Rel (U a)} -> r x y
              -> Locate sig a r x y
  ||| We focus on a subterm `lhs` that may appear in
  ||| multiple locations and rewrite it to `rhs` using a
  ||| specific rule.
  Cong : {0 r : Rel (U a)} ->
         (t : Term sig (Maybe (U a))) ->
         {lhs, rhs : U a} -> r lhs rhs ->
         Locate sig a r (plug a t lhs) (plug a t rhs)

public export 0
Closure : (pres : Presentation) ->
          (a : PresetoidAlgebra pres.signature) -> Rel (U a)
Closure pres a
  = Symmetrise                      -- Symmetric
  $ Locate pres.signature a.algebra -- Congruence
  $ Step pres a

public export 0
Derivation : (p : Presentation)
  -> (a : PresetoidAlgebra
            p.signature)
  -> Rel (U a)
Derivation p a
  = RTList     -- Reflexive, Transitive
  $ Symmetrise -- Symmetric
               -- Congruence
  $ Locate p.signature a.algebra
  $ Step p a   -- Axiomatic steps

public export 0
Proof : (pres : Presentation) ->
        (lhs, rhs : Term pres.signature (Fin n)) ->
        Type
Proof pres lhs rhs = Derivation pres (QuotientData pres (cast (Fin n))) lhs rhs

export
join : Locate sig alg (Locate sig alg r) ~> Locate sig alg r
join (Here p) = p
join (Cong t (Here p)) = Cong t p
join (Cong t (Cong u {lhs} {rhs} p))
  = replace
    {p = \ x => Locate sig alg r x (plug alg t (plug alg u rhs))}
    (sym $ plugFusion t u lhs)
  $ replace
    {p = Locate sig alg r (plug alg (t :.: u) lhs)}
    (sym $ plugFusion t u rhs)
  $ Cong (t :.: u) p

export
locate :
  {a : PresetoidAlgebra pres.signature} ->
  Locate pres.signature a.algebra (Derivation pres a) ~> Derivation pres a
locate (Here p) = p
locate (Cong t p)
  = gmap (plug a.algebra t) (gmap (plug a.algebra t) (join . Cong t)) p

-- TODO: move to base
fromLeft : (b -> a) -> Either a b -> a
fromLeft f (Left a) = a
fromLeft f (Right b) = f b

keep : (env : Fin (S n) -> a) ->
       (Either a (Fin (S n))) -> Either a (Fin n)
keep env (Left t) = Left t
keep env (Right FZ) = Left (env FZ)
keep env (Right (FS k)) = Right k

keepFusion :
  (env : Fin (S n) -> a) ->
  (v : Either a (Fin (S n))) ->
  fromLeft env v === fromLeft (env . FS) (keep env v)
keepFusion env (Left t) = Refl
keepFusion env (Right FZ) = Refl
keepFusion env (Right (FS k)) = Refl

focus : (env : Fin (S n) -> a) ->
        (Either a (Fin (S n)) -> Maybe a)
focus env (Left t) = Just t
focus env (Right FZ) = Nothing
focus env (Right (FS k)) = Just (env (FS k))

focusFusion :
  (env : Fin (S n) -> a) ->
  (v : Either a (Fin (S n))) ->
  fromMaybe (env FZ) (focus env v) === fromLeft env v
focusFusion env (Left t) = Refl
focusFusion env (Right FZ) = Refl
focusFusion env (Right (FS k)) = Refl

keepFocus :
  (lhs, rhs : Fin (S n) -> a) ->
  (v : Either a (Fin (S n))) ->
  fromMaybe (rhs FZ) (focus lhs v) === fromLeft (lhs . FS) (keep rhs v)
keepFocus lhs rhs (Left t) = Refl
keepFocus lhs rhs (Right FZ) = Refl
keepFocus lhs rhs (Right (FS k)) = Refl

focusEq :
  {a : Algebra sig} ->
  (t : Term sig (Either (U a) (Fin (S n)))) ->
  (env : Fin (S n) -> U a) ->
  bindTerm t (fromLeft env)
  === bindTerm (map (focus env) t) (fromMaybe (env FZ))
focusEq t env = trans
  (bindTermExtensional t (\ v => sym $ focusFusion env v))
  (sym $ bindTermMapFusion (focus env) t (fromMaybe (env FZ)))

focusKeepEq :
  {a : Algebra sig} ->
  (t : Term sig (Either (U a) (Fin (S n)))) ->
  (lhs, rhs : Fin (S n) -> U a) ->
  bindTerm (map (focus lhs) t) (fromMaybe (rhs FZ))
  === bindTerm (map (keep rhs) t) (fromLeft (lhs . FS))
focusKeepEq t lhs rhs
  = trans (bindTermMapFusion (focus lhs) t (fromMaybe (rhs FZ)))
  $ trans (bindTermExtensional t (keepFocus lhs rhs))
  $ sym   (bindTermMapFusion (keep rhs) t (fromLeft (lhs . FS)))

keepEq :
  {a : Algebra sig} ->
  (t : Term sig (Either (U a) (Fin (S n)))) ->
  (env : Fin (S n) -> U a) ->
  bindTerm t (fromLeft env)
  === bindTerm (map (keep env) t) (fromLeft (env . FS))
keepEq t env = trans
  (bindTermExtensional t (keepFusion env))
  (sym $ bindTermMapFusion (keep env) t (fromLeft (env . FS)))


cong' : {sig : Signature} -> {a : Algebra sig} ->
        {0 r : Rel (U a)} ->
        (n : Nat) ->
        (t : Term sig (Either (U a) (Fin n))) ->
        {lhs, rhs : Fin n -> U a} ->
        (eq : (x : Fin n) -> r (lhs x) (rhs x)) ->
        RTList (Locate sig a r)
               (bindTerm t (fromLeft lhs))
               (bindTerm t (fromLeft rhs))

cong' 0 t eq
  = reflexive $ bindTermExtensional t $ \case
      Left _ => Refl
      Right k => absurd k

cong' (S k) t eq =
  let mid1 : U a
      mid1 = bindTerm (map (focus lhs) t) (fromMaybe (rhs FZ))

      mid2 : U a
      mid2 = bindTerm (map (keep rhs) t) (fromLeft (lhs . FS))

      end : U a
      end = bindTerm t (fromLeft rhs)

  in replace
    {p = \ x => Locate sig a r x mid1}
    (sym $ focusEq t lhs)
    (Cong (map (focus lhs) t) (eq FZ))
  :: (replace
    {p = \ x => RTList (Locate sig a r) x end}
    (sym $ focusKeepEq t lhs rhs)
  $ replace
    {p = RTList (Locate sig a r) mid2}
    (sym $ keepEq t rhs)
  $ cong' k (map (keep rhs) t) (\ k => eq (FS k)))

cong : {sig : Signature} -> {a : Algebra sig} ->
       {0 r : Rel (U a)} ->
       {n : Nat} ->
       (t : Term sig (Fin n)) ->
       {lhs, rhs : Fin n -> U a} ->
       (eq : (x : Fin n) -> r (lhs x) (rhs x)) ->
       RTList (Locate sig a r) (bindTerm t lhs) (bindTerm t rhs)
cong t eq
  = replace
    {p = \ x => RTList (Locate sig a r) x (bindTerm t rhs)}
    (bindTermMapFusion Right t (fromLeft lhs))
  $ replace
    {p = RTList (Locate sig a r) (bindTerm (map Right t) (fromLeft lhs))}
    (bindTermMapFusion Right t (fromLeft rhs))
  $ cong' n (map Right t) eq

export
linearise : {pres : Presentation} ->
            {a : PresetoidAlgebra pres.signature} ->
            Maybe (DecEq (U a)) ->
            (|-) {pres} a ~> Derivation pres a
linearise Nothing (Include p) = [Fwd (Here (Include p))]
linearise (Just dec) (Include p) with (decEq x y)
  linearise (Just dec) (Include p) | Yes eq = rewrite eq in []
  linearise (Just dec) (Include p) | No _ = [Fwd (Here (Include p))]
linearise mdec (Refl x) = []
linearise mdec (Sym p) = reverse sym (linearise mdec p)
linearise mdec (Transitive p q) = linearise mdec p ++ linearise mdec q
linearise mdec (ByAxiom eq env) = [Fwd (Here (ByAxiom eq env))]
linearise mdec (Congruence t eq)
  = concat
  $ map locate
  $ cong {sig = pres.signature} {r = Derivation pres a} t
  $ \ v => linearise mdec (eq v)

public export
record Focus (sig : Signature) (a : Algebra sig) where
  constructor MkFocus
  context : Term sig (Maybe (U a))
  content : U a

namespace Focus

  export
  display : Printer sig (U a) -> Focus sig a -> Doc ()
  display printer (MkFocus ctx t)
     = Term.display ({ varShow := focused } printer) ctx

    where

    [focused] Show (Maybe (U a)) where
      showPrec _ Nothing  = "[" ++ show @{printer.varShow} t ++ "]"
      showPrec d (Just a) = showPrec @{printer.varShow} d a

record Printer where
  constructor MkPrinter
  ||| Opening a proof environment
  beginProof       : Maybe String     -- e.g. \begin{align*}
  ||| Closing a proof environment
  endProof         : Maybe String     -- e.g. \end{align*}
  ||| Separation between LHS and justification
  sepJustification : Doc ()
  ||| Forward step brackets
  forwardStep      : (String, String) -- e.g. ≡[ and ⟩
  ||| Backward (symmetric) step brackets
  backwardStep     : (String, String) -- e.g. ≡⟨ and ]
  ||| new line separator (on top of literal newlines)
  newline          : String -- e.g. \\ in a latex align environment

export
unicode : Printer
unicode = MkPrinter
  { beginProof       = Nothing
  , endProof         = Nothing
  , sepJustification = hardline <+> "  "
  , forwardStep      = ("≡[", "⟩")
  , backwardStep     = ("≡⟨", "]")
  , newline          = ""
  }

export
latex : Printer
latex = MkPrinter
  { beginProof       = Just "\\begin{align*}"
  , endProof         = Just "\\end{align*}"
  , sepJustification = hardline <+> "  & \\quad "
  , forwardStep      = ("\\text{=[", "⟩}")
  , backwardStep     = ("\\text{=⟨", "]}")
  , newline          = "\\\\"
  }

export
latexPreamble : String
latexPreamble
  = #"""
    \usepackage{amsmath}
    \usepackage{newunicodechar}
    \newunicodechar{ε}{\ensuremath{\varepsilon}}
    \newunicodechar{•}{\ensuremath{\bullet}}
    \newunicodechar{⟨}{\ensuremath{\langle}}
    \newunicodechar{⟩}{\ensuremath{\rangle}}
    """#

export
compactLatex : Printer
compactLatex = MkPrinter
  { beginProof       = Just #"\begin{mathpar}\mprset{flushleft}"#
  , endProof         = Just #"\end{mathpar}"#
  , sepJustification = #"\explain={"#
  , forwardStep      = (#"["#, "⟩}")
  , backwardStep     = (#"⟨"#, "]}")
  , newline          = #""#
  }

export
compactLatexPreamble : String
compactLatexPreamble = #"""
              \usepackage{amsmath}
              \usepackage{mathtools}
              \usepackage{amssymb}
              \usepackage{newunicodechar}
              \usepackage{newunicodechar}
              \newunicodechar{ε}{\ensuremath{\varepsilon}}
              \newunicodechar{•}{\ensuremath{\bullet}}
              \newunicodechar{⟨}{\ensuremath{\langle}}
              \newunicodechar{⟩}{\ensuremath{\rangle}}
              \usepackage{ifthen}
              \usepackage{mathpartir}
              \newboolean{explanation}
              \setboolean{explanation}{false}
              \newcommand\explainabove[2]{\overset{\overset{%
              \clap{\text{\scriptsize #2}}}%
              {\downarrow}}{#1}}
              \newcommand\explainbelow[2]{\underset{\underset{%
              \clap{\text{\scriptsize #2}}}%
              {\uparrow}}{#1}}
              \newcommand\negate[1]{%
                \ifthenelse{\boolean{#1}}{%
                  \setboolean{#1}{false}%
                  }{%
                  \setboolean{#1}{true}%
                  }%
              }
              \newcommand\explain[2]{%
                \ifthenelse{\boolean{explanation}}{%
                  \explainabove{#1}{#2}%
                }{%
                  \explainbelow{#1}{#2}%
                }
                \negate{explanation}
              }
              """#

namespace Derivation

  export
  display : Printer ->
            {pres : Presentation} ->
            {a : PresetoidAlgebra pres.signature} ->
            Printer pres (U a) ->
            ({x, y : U a} -> Show (a.relation x y)) =>
            {x, y : U a} -> Derivation pres a x y -> Doc ()
  display printer p @{showR} prf = vcat $ concat {t = List}
     [ toList (pretty <$> printer.beginProof)
     , [ vcat (steps prf)
       , pretty (show @{p.sigPrinter.varShow} y) ]
     , toList (pretty <$> printer.endProof)
     ] where

    byProof : Bool -> Doc () -> Doc ()
    byProof False d
      = let (beg, end) = printer.forwardStep in
        pretty beg <++> d <++> pretty end <+> pretty printer.newline
    byProof True  d
      = let (beg, end) = printer.backwardStep in
        pretty beg <++> d <++> pretty end <+> pretty printer.newline

    base : Bool ->
           Either (U a) (Focus pres.signature a.algebra) ->
           Doc () -> Doc ()
    base b ctx prf = hcat
      [ either (pretty . show @{p.sigPrinter.varShow})
               (Focus.display p.sigPrinter)
               ctx
      , printer.sepJustification
      , byProof b prf
      ]

    cong : {begin, end : U a} -> Bool ->
           Locate pres.signature a.algebra (Step pres a) begin end ->
           Doc ()
    cong b (Here prf)
      = base b (Left (if b then end else begin))
      $ display @{showR} @{p.axiomShow} prf
    cong b (Cong t {lhs} {rhs} prf)
      = base b (Right (MkFocus t (if b then rhs else lhs)))
      $ display @{showR} @{p.axiomShow} prf

    step : {begin, end : U a} -> Closure pres a begin end -> Doc ()
    step (Fwd p) = cong False p
    step (Bwd p) = cong True p

    steps  : {begin : U a} -> Derivation pres a begin end -> List (Doc ())
    steps [] = []
    steps (r :: rs) = step r :: steps rs

namespace Proof

  export
  displayPerhapsWithMagic :
            Printer ->
            {pres : Presentation} ->
            {a : PresetoidAlgebra pres.signature} ->
            Printer pres (U a) ->
            ({x, y : U a} -> Show (a.relation x y)) =>
            Maybe (DecEq (U a)) ->
            Maybe (Ord (U a)) ->
            {x, y : U a} -> (|-) {pres} a x y -> Doc ()
  displayPerhapsWithMagic printer p @{showR} mdec mord
    = Derivation.display printer p @{showR}
    . optionalDeloop mdec mord
    . linearise mdec

    where

      optionalDeloop : Maybe (DecEq ty) -> Maybe (Ord ty) ->
                       RTList {a = ty} r ~> RTList r
      optionalDeloop (Just dec) (Just ord) rs = deloop rs
      optionalDeloop _ _ rs = rs

  export
  display : Printer ->
            {pres : Presentation} ->
            {a : PresetoidAlgebra pres.signature} ->
            Printer pres (U a) ->
            ({x, y : U a} -> Show (a.relation x y)) =>
            {auto dec : DecEq (U a)} ->
            {auto ord : Ord (U a)} ->
            {x, y : U a} -> (|-) {pres} a x y -> Doc ()
  display printer p @{showR} {dec} {ord}
    = displayPerhapsWithMagic printer p @{showR} (Just dec) (Just ord)

  export
  displayWithoutDecEq
    : Printer ->
      {pres : Presentation} ->
      {a : PresetoidAlgebra pres.signature} ->
      Printer pres (U a) ->
      ({x, y : U a} -> Show (a.relation x y)) =>
      {x, y : U a} -> (|-) {pres} a x y -> Doc ()
  displayWithoutDecEq printer p @{showR}
    = displayPerhapsWithMagic printer p @{showR} Nothing Nothing
