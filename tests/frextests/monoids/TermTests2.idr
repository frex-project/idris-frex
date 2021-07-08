module TermTests2

import Data.Unit

import Frex
import Frex.Free.Construction
import Frex.Free.Construction.Combinators

import Frexlet.Monoid
import Frexlet.Monoid.Free
import Frexlet.Monoid.Notation.Additive

import Syntax.PreorderReasoning

var : {n : Nat} -> Fin n -> U ((Construction.Free MonoidTheory $ cast $ Fin n).Data.Model)
var = (Construction.Free MonoidTheory $ cast $ Fin n).Data.Env.H

-- Modulo normalisation:
-- var : {n : Nat} -> Fin n -> Term Signature (Fin n)
-- var = Done

infix 0 ~~
0 (~~) : Rel (U (Construction.Free MonoidTheory $ cast $ Fin n).Data.Model)
(~~) = (Free MonoidTheory $ cast $ Fin n).Data.Model.rel

-- Modulo normalisation:
-- infix 0 ~~~
-- 0 (~~~) : Rel (Term Signature (Fin n))
-- (~~~) = (|-) {pres = MonoidTheory} (QuotientData MonoidTheory (cast (Fin n)))

public export
record Lemma (pres : Presentation) where
  constructor MkLemma
  equation : Equation pres.signature
  derivable : (|-) {pres} (QuotientData pres (cast (Fin equation.support)))
              equation.lhs equation.rhs
%hint
notation: {n : Nat} -> Additive1 (U (Construction.Free MonoidTheory $ cast $ Fin n).Data.Model)
notation = (Construction.Free MonoidTheory $ cast $ Fin n).Data.Model.Additive1


lemma :
  {n : Nat} ->
  (pres : Presentation) ->
  (free : Free pres (cast $ Fin n)) ->
  (t : Term pres.signature (Fin n)) ->
  bindTerm {a = Free _ _}
      t
     ((Free.Construction.Free pres (cast $ Fin n)) .Data.Env.H) = t

lemmas :
  {n : Nat} ->
  (pres : Presentation) ->
  (free : Free pres (cast $ Fin n)) ->
  (ts : Vect m (Term pres.signature (Fin n))) ->
  bindTerms {a = Free _ _}
      ts
     ((Free.Construction.Free pres (cast $ Fin n)) .Data.Env.H) = ts

lemma pres free (Done v) = Refl
lemma pres free (Call f ts) = cong (Call f) (lemmas pres free ts)

lemmas pres free [] = Refl
lemmas pres free (t :: ts)
  = cong2 (::) (lemma pres free t) (lemmas pres free ts)


mkLemma : {pres : Presentation} ->
          {n : Nat} -> (free : Free pres (cast (Fin n))) ->
          (eq : (Term pres.signature (Fin n), Term pres.signature (Fin n))) ->
          {auto prf : free.Data.Model.rel
                        (free.Sem (fst eq) free.Data.Env.H)
                        (free.Sem (snd eq) free.Data.Env.H)} ->
          Lemma pres
mkLemma free (lhs, rhs) =
  let equation : Equation pres.signature
      equation = MkEquation n (lhs, rhs)
  in MkLemma equation
   $ rewrite sym (lemma pres free lhs) in
     rewrite sym (lemma pres free rhs) in
     prove free (lhs, rhs)

instantiate :
  {pres : Presentation} ->
  {a : PresetoidAlgebra pres.signature} ->
  {lhs, rhs : Term pres.signature (Fin n)} ->
  (|-) {pres} (QuotientData pres (cast (Fin n))) lhs rhs ->
  (env : Fin n -> U a) ->
  (|-) {pres} a (bindTerm {a = a.algebra} lhs env) (bindTerm {a = a.algebra} rhs env)
instantiate (Include (Assume Refl)) env = Refl _
instantiate (Refl lhs) env = Refl _
instantiate (Sym p) env = Sym (instantiate p env)
instantiate (Transitive p q) env = Transitive (instantiate p env) (instantiate q env)
instantiate (ByAxiom eq f) env =
  -- for some reason these proofs need to be let-bound
  let lhsEq = bindAssociative {a = a.algebra} ((pres.axiom eq).lhs) f env in
  let rhsEq = bindAssociative {a = a.algebra} ((pres.axiom eq).rhs) f env in
  rewrite lhsEq in
  rewrite rhsEq in
  ByAxiom eq _
instantiate (Congruence t {lhs = lhsEnv} {rhs = rhsEnv} eqForEq) env =
  let lhsEq = bindAssociative {a = a.algebra} t lhsEnv env in
  let rhsEq = bindAssociative {a = a.algebra} t rhsEnv env in
  rewrite lhsEq in
  rewrite rhsEq in
  Congruence t $ \ i => instantiate (eqForEq i) env

||| A ByAxiom that's much more convenient to use
export
byLemma :
  {pres : Presentation} ->
  {a : PresetoidAlgebra pres.signature} ->
  (lemma : Lemma pres) ->
  PI (lemma.equation.support) Hidden (U a) $ \env =>
    (|-) {pres} a (bindTerm {a = a.algebra} lemma.equation.lhs (\ i => index i env))
                  (bindTerm {a = a.algebra} lemma.equation.rhs (\ i => index i env))
byLemma (MkLemma (MkEq n lhs rhs) prf)
  = curry n Hidden _ $ \ env =>
    instantiate prf (\ i => index i env)

Trivial : Lemma MonoidTheory
Trivial = mkLemma (FreeMonoidOver $ cast $ Fin 1)
        $ Done 0 =-= Done 0

Trivial2 : Lemma MonoidTheory
Trivial2 = mkLemma (FreeMonoidOver $ cast $ Fin 2)
         $ Done 0 .+. Done 1 =-= Done 0 .+. Done 1

Assoc : Lemma MonoidTheory
Assoc = mkLemma (FreeMonoidOver $ cast $ Fin 3) $
        Done 0 .+. (Done 1 .+. Done 2)
    =-= (Done 0 .+. Done 1) .+. Done 2

RAssoc : Lemma MonoidTheory
RAssoc = mkLemma (FreeMonoidOver $ cast $ Fin 3)
       $ (Done 0 .+. Done 1) .+. Done 2
       =-= Done 0 .+. (Done 1 .+. Done 2)

Units : Lemma MonoidTheory
Units = mkLemma (FreeMonoidOver $ cast $ Fin 1)
      $ (O1 .+. (Done 0 .+. O1)) .+. O1 =-= Done 0

units : (O1 .+. (var {n = 1} 0 .+. O1)) .+. O1 ~~ var 0
units = byLemma Units
