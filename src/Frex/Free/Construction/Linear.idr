module Frex.Free.Construction.Linear

import Frex.Signature
import Frex.Algebra
import Frex.Presentation
import Frex.Free.Construction

import Data.String
import Data.Relation
import Data.Relation.Closure.Symmetric
import Data.Relation.Closure.ReflexiveTransitive
import Text.PrettyPrint.Prettyprinter

public export
data Step : (pres : Presentation) ->
            (a : PresetoidAlgebra pres.signature) ->
            Rel (U a) where
  Include : {x, y : U a} -> a.relation x y -> Step pres a x y
  ByAxiom : {0 a : PresetoidAlgebra pres.signature} ->
            (eq : Axiom pres) -> (env : Fin (pres.axiom eq).support -> U a) ->
            Step pres a (bindTerm {a = a.algebra} (pres.axiom eq).lhs env)
                        (bindTerm {a = a.algebra} (pres.axiom eq).rhs env)

public export
data Locate : (sig : Signature) ->
              (alg : Algebra sig) ->
              Rel (U alg) -> Rel (U alg) where

  ||| We prove the equality by invoking a rule at the toplevel
  Here : {0 r : Relation.Rel (U alg)} -> r x y -> Locate sig alg r x y

  ||| We focus on a subterm (that may appear in multiple places)
  ||| and rewrite it using a specific rule.
  Cong : {0 r : Relation.Rel (U alg)} ->
         (t : Term sig (Maybe (U alg))) ->
         (lhs, rhs : U alg) -> r lhs rhs ->
         Locate sig alg r (bindTerm {a = alg} t (fromMaybe lhs))
                          (bindTerm {a = alg} t (fromMaybe rhs))

public export 0
Derivation : (pres : Presentation) ->
             (a : PresetoidAlgebra pres.signature) ->
             Rel (U a)
Derivation pres a
  = RTList                          -- Reflexive, Transitive
  $ Symmetrise                      -- Symmetric
  $ Locate pres.signature a.algebra -- Congruence
  $ Step pres a                     -- Closure

linearise : {pres : Presentation} ->
            {a : PresetoidAlgebra pres.signature} ->
            (|-) {pres} a ~> Derivation pres a
linearise (Include p) = [Fwd (Here (Include p))]
linearise (Refl x) = []
linearise (Sym p) = reverse sym (linearise p)
linearise (Transitive p q) = linearise p ++ linearise q
linearise (ByAxiom eq env) = [Fwd (Here (ByAxiom eq env))]
linearise (Congruence t eqForEq) = ?a_

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
