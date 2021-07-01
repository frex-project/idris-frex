module Frex.Free.Construction.Linear

import Frex.Signature
import Frex.Algebra
import Frex.Presentation
import Frex.Free.Construction

import Data.Setoid
import Data.String
import Data.Relation
import Data.Relation.Closure.Symmetric
import Data.Relation.Closure.ReflexiveTransitive
import Text.PrettyPrint.Prettyprinter

%default total

public export
data Step : (pres : Presentation) ->
            (a : PresetoidAlgebra pres.signature) ->
            Rel (U a) where
  Include : {x, y : U a} -> a.relation x y -> Step pres a x y
  ByAxiom : {0 a : PresetoidAlgebra pres.signature} ->
            (eq : Axiom pres) -> (env : Fin (pres.axiom eq).support -> U a) ->
            Step pres a (bindTerm {a = a.algebra} (pres.axiom eq).lhs env)
                        (bindTerm {a = a.algebra} (pres.axiom eq).rhs env)

namespace Step

  export
  display : {pres : Presentation} ->
            {a : PresetoidAlgebra pres.signature} ->
            ({x, y : U a} -> Show (a.relation x y)) =>
            Show (pres .Axiom) =>
            {0 x, y : U a} -> Step pres a x y -> Doc ()
  display @{showR} (Include p) = pretty (show @{showR} p)
  display (ByAxiom eq env) = pretty (show eq)

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

bindTermExtensional :
  {alg : Algebra sig} ->
  (t : Term sig vars) -> {lhs, rhs : vars -> U alg} ->
  (eq : (v : vars) -> lhs v === rhs v) ->
  bindTerm t lhs === bindTerm t rhs
bindTermsExtensional :
  {alg : Algebra sig} ->
  (ts : Vect n (Term sig vars)) -> {lhs, rhs : vars -> U alg} ->
  (eq : (v : vars) -> lhs v === rhs v) ->
  bindTerms ts lhs === bindTerms ts rhs

bindTermExtensional (Done v) eq = eq v
bindTermExtensional (Call f ts) eq
  = cong (alg .Semantics f) (bindTermsExtensional ts eq)

bindTermsExtensional [] eq = Refl
bindTermsExtensional (t :: ts) eq
  = cong2 (::) (bindTermExtensional t eq)
               (bindTermsExtensional ts eq)

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
data Locate : (sig : Signature) ->
              (a : Algebra sig) ->
              Rel (U a) -> Rel (U a) where

  ||| We prove the equality by invoking a rule at the toplevel
  Here : {0 r : Relation.Rel (U a)} -> r x y -> Locate sig a r x y

  ||| We focus on a subterm (that may appear in multiple places)
  ||| and rewrite it using a specific rule.
  Cong : {0 r : Relation.Rel (U a)} ->
         (t : Term sig (Maybe (U a))) ->
         {lhs, rhs : U a} -> r lhs rhs ->
         Locate sig a r (plug a t lhs) (plug a t rhs)

public export 0
Closure : (pres : Presentation) ->
          (a : PresetoidAlgebra pres.signature) ->
          Rel (U a)
Closure pres a
  = Symmetrise                      -- Symmetric
  $ Locate pres.signature a.algebra -- Congruence
  $ Step pres a


public export 0
Derivation : (pres : Presentation) ->
             (a : PresetoidAlgebra pres.signature) ->
             Rel (U a)
Derivation pres a
  = RTList          -- Reflexive, Transitive
  $ Closure pres a

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

bindTermMapFusion :
  {alg : Algebra sig} ->
  (ren : a -> vars) -> (t : Term sig a) -> (env : vars -> U alg) ->
  bindTerm (map ren t) env === bindTerm t (env . ren)
bindTermsMapFusion :
  {alg : Algebra sig} ->
  (ren : a -> vars) -> (ts : Vect n (Term sig a)) -> (env : vars -> U alg) ->
  bindTerms (bindTerms {a = Free _ _} ts (Done . ren)) env === bindTerms ts (env . ren)

bindTermMapFusion ren (Done v)    env = Refl
bindTermMapFusion ren (Call f ts) env
  = cong (alg .Semantics f) (bindTermsMapFusion ren ts env)

bindTermsMapFusion ren [] env = Refl
bindTermsMapFusion ren (t :: ts) env
  = cong2 (::) (bindTermMapFusion ren t env)
               (bindTermsMapFusion ren ts env)

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

linearise : {pres : Presentation} ->
            {a : PresetoidAlgebra pres.signature} ->
            (|-) {pres} a ~> Derivation pres a
linearise (Include p) = [Fwd (Here (Include p))]
linearise (Refl x) = []
linearise (Sym p) = reverse sym (linearise p)
linearise (Transitive p q) = linearise p ++ linearise q
linearise (ByAxiom eq env) = [Fwd (Here (ByAxiom eq env))]
linearise (Congruence t eq)
  = concat
  $ map locate
  $ cong {sig = pres.signature} {r = Derivation pres a} t
  $ \ v => linearise (eq v)

public export
record Focus (sig : Signature) (a : Algebra sig) where
  constructor MkFocus
  context : Term sig (Maybe (U a))
  content : U a

namespace Focus

  data Raw = MkRaw String
  Show Raw where show (MkRaw str) = str

  export
  display : (Show (U a), Show (Op sig), HasPrecedence sig) =>
            Bool -> Focus sig a -> Doc ()
  display b (MkFocus ctx t) =
    let focus = "[" ++ show t ++ "]" in
    Term.display b (map (MkRaw . maybe focus show) ctx)

namespace Derivation

  export
  display : {pres : Presentation} ->
            {a : PresetoidAlgebra pres.signature} ->
            ({x, y : U a} -> Show (a.relation x y)) =>
            Show (pres .Axiom) =>
            Show (U a) =>
            Show (Op pres.signature) =>
            HasPrecedence pres.signature =>
            {x, y : U a} -> Derivation pres a x y -> Doc ()
  display @{showR} prf = vcat [vcat (steps prf), pretty (show y)] where

    byProof : Bool -> Doc () -> Doc ()
    byProof False d = indent 2 $ "≡[" <++> d <++> "⟩"
    byProof True  d = indent 2 $ "≡⟨" <++> d <++> "]"

    base : Bool ->
           Either (U a) (Focus pres.signature a.algebra) ->
           Doc () -> List (Doc ())
    base b ctx p =
      [ either (pretty . show) (Focus.display True) ctx
      , byProof b p]

    cong : {begin, end : U a} -> Bool ->
           Locate pres.signature a.algebra (Step pres a) begin end ->
           List (Doc ())
    cong b (Here p)
      = base b (Left (if b then end else begin))
      $ display @{showR} p
    cong b (Cong t {lhs} {rhs} p)
      = base b (Right (MkFocus t (if b then rhs else lhs)))
      $ display @{showR} p

    step : {begin, end : U a} -> Closure pres a begin end -> List (Doc ())
    step (Fwd p) = cong False p
    step (Bwd p) = cong True p

    steps  : {begin : U a} -> Derivation pres a begin end -> List (Doc ())
    steps [] = []
    steps (r :: rs) = step r ++ steps rs

namespace Proof

  export
  display : {pres : Presentation} ->
            {a : PresetoidAlgebra pres.signature} ->
            ({x, y : U a} -> Show (a.relation x y)) =>
            Show (pres .Axiom) =>
            Show (U a) =>
            Show (Op pres.signature) =>
            HasPrecedence pres.signature =>
            {x, y : U a} -> (|-) {pres} a x y -> Doc ()
  display @{showR} = Derivation.display @{showR} . linearise

{-
export
display : {pres : Presentation} ->
          {a : PresetoidAlgebra pres.signature} ->
--          ({x, y : U a} -> Show (a.relation x y)) =>
          Show (pres .Axiom) =>
          Show (U a) =>
          Show (Op pres.signature) =>
          HasPrecedence pres.signature =>
          {x, y : U a} -> (|-) {pres} a x y -> Doc ()
display @{showR} prf = vcat [step False prf, pretty (show y)] where

  byProof : Bool -> Doc () -> Doc ()
  byProof False d = indent 2 $ "≡[" <++> d <++> "⟩"
  byProof True  d = indent 2 $ "≡⟨" <++> d <++> "]"

  step   : Bool -> {begin, end : U a} -> (|-) {pres} a begin end -> Doc ()
  justif : Bool -> {begin, end : U a} -> (|-) {pres} a begin end -> Doc ()

  step b prf = vcat [pretty (show begin), justif b prf]

  justif b (Include p)
    = ?goal -- byProof b $ pretty (show @{showR} p)
  justif b (Refl p)
    = byProof b "reflexivity"
  justif b (Sym p)
    = justif (not b) p
  justif b (Transitive p q)
    = vcat $ if b
        then [justif b q, step b p]
        else [justif b p, step b q]
  justif b (ByAxiom eq env)
    = byProof b $ pretty (show eq)
  justif b (Congruence ctxt env) = ?goal_
-}
