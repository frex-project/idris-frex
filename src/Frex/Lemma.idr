module Frex.Lemma

import Data.Fin

import Frex.Signature
import Frex.Axiom
import Frex.Presentation
import Frex.Algebra
import Frex.Model
import Frex.Free
import Frex.Free.Construction

import Data.Fun.Nary
import Data.Relation
import Data.Setoid

||| A lemma is an equation that can be proven in the free construction
public export
record Lemma (pres : Presentation) where
  constructor MkLemma
  equation : Equation pres.signature
  derivable : (|-) {pres} (QuotientData pres (cast (Fin equation.support)))
              equation.lhs equation.rhs

||| Declare a lemma by invoking a free solver on the equation.
public export
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
   $ rewrite sym (freeSem pres (cast $ Fin n) lhs) in
     rewrite sym (freeSem pres (cast $ Fin n) rhs) in
     prove free (lhs, rhs)

||| Instantiating a free proof on free terms to get a free proof on a setoid
public export
instantiate :
  {pres : Presentation} ->
  {a : PresetoidAlgebra pres.signature} ->
  {lhs, rhs : Term pres.signature (Fin n)} ->
  (|-) {pres} (QuotientData pres (cast (Fin n))) lhs rhs ->
  (env : Fin n -> U a) ->
  (|-) {pres} a (bindTerm {a = a.algebra} lhs env)
                (bindTerm {a = a.algebra} rhs env)
instantiate (Include (Assume Refl)) env = Refl _
instantiate (Refl lhs) env = Refl _
instantiate (Sym p) env = Sym (instantiate p env)
instantiate (Transitive p q) env
  = Transitive (instantiate p env) (instantiate q env)
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

||| Instantiating a lemma to prove a concrete fact in a give model
||| The user is expected to pass the instantiation (useful if unification
||| is not enough to reconstruct it)
public export
byLemma' :
  {pres : Presentation} ->
  (a : Model pres) ->
  (lemma : Lemma pres) ->
  PI (lemma.equation.support) Visible (U a) $ \env =>
    a.rel (a.Sem lemma.equation.lhs (\ i => index i env))
          (a.Sem lemma.equation.rhs (\ i => index i env))
byLemma' a (MkLemma (MkEq n lhs rhs) prf)
  = curry n Visible _ $ \ env =>
    solveVect (Free pres (cast $ Fin n)) env (lhs, rhs)
      @{ let lhsEq = freeSem pres (cast $ Fin n) lhs in
         let rhsEq = freeSem pres (cast $ Fin n) rhs in
         rewrite lhsEq in
         rewrite rhsEq in
         prf
       }

||| Instantiating a lemma to prove a concrete fact in a give model
||| The user does not have to pass the instantiation (useful if unification
||| is enough to reconstruct it)
public export
byLemma :
  {pres : Presentation} ->
  (a : Model pres) ->
  (lemma : Lemma pres) ->
  PI (lemma.equation.support) Hidden (U a) $ \env =>
    a.rel (a.Sem lemma.equation.lhs (\ i => index i env))
          (a.Sem lemma.equation.rhs (\ i => index i env))
byLemma a (MkLemma (MkEq n lhs rhs) prf)
  = curry n Hidden _ $ \ env =>
    solveVect (Free pres (cast $ Fin n)) env (lhs, rhs)
      @{ let lhsEq = freeSem pres (cast $ Fin n) lhs in
         let rhsEq = freeSem pres (cast $ Fin n) rhs in
         rewrite lhsEq in
         rewrite rhsEq in
         prf
       }
