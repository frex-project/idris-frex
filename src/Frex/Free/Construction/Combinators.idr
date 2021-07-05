module Frex.Free.Construction.Combinators

import Frex.Signature
import Frex.Presentation
import Frex.Model
import Frex.Algebra
import Frex.Algebra.Abstract
import Frex.Free.Construction

import Data.Setoid
import Data.Setoid.Vect.Inductive
import Data.Setoid.Vect.Functional

import Data.Either.Extra
import Data.Fin.Extra
import Data.Vect.Extra1

import Data.Fun.Nary

%default total

export
congruence' :
   {pres : Presentation} ->
   {a : PresetoidAlgebra pres.signature} ->
   {n : Nat} -> (t : Term pres.signature (Either (U a) (Fin n))) ->
   {lhs, rhs : Vect n (U a)} ->
   (eqForEq : Inductive.(.VectEquality) (cast $ QuotientModel pres a) lhs rhs) ->
   (|-) {pres} a
      (bindTerm {a = a.algebra} t (fromLeft (\ i => index i lhs)))
      (bindTerm {a = a.algebra} t (fromLeft (\ i => index i rhs)))
congruence' t eq = case mkAbstract t of
  MkAbstract {vars} u vals prf =>
    let prf' : (env : Vect n (U a)) ->
                bindTerm {a = a.algebra} t (fromLeft (\ i => index i env))
                === bindTerm {a = a.algebra} (map Extra.indexSum u)
                             (\ i => index i (vals ++ env))
        prf' env
          = trans (cong (\ t => bindTerm {a = a.algebra} t (fromLeft (\ i => index i env))) prf)
          $ trans (bindTermMapFusion (mapFst (\ i => index i vals)) u (fromLeft (\ i => index i env)))
          $ trans (sym $ bindTermExtensional u $ \case
                      Left k => indexIndexSumLeft {ys = env} k
                      Right k => indexIndexSumRight k)
          $ sym $ bindTermMapFusion indexSum u (\ i => index i (vals ++ env))
    in
    rewrite prf' lhs in
    rewrite prf' rhs in
    Congruence {n = vars + n} (map Extra.indexSum u) $ \ i =>
      Functional.index i (_ .VectEqualityReflexive vals ++ eq)

public export
WithEqualities :
   (pres : Presentation) ->
   (a : PresetoidAlgebra pres.signature) ->
   (lhs, rhs : Vect n (U a)) ->
   Type -> Type
WithEqualities pres a [] _ b = b
WithEqualities pres a (l :: lhs) (r :: rhs) b
  = (|-) {pres} a l r -> WithEqualities pres a lhs rhs b

export
withEqualities :
   {0 pres : Presentation} ->
   {0 a : PresetoidAlgebra pres.signature} ->
   (lhs, rhs : Vect n (U a)) ->
   (Inductive.(.VectEquality) (cast $ QuotientModel pres a) lhs rhs -> b) ->
   WithEqualities pres a lhs rhs b
withEqualities [] [] f = f []
withEqualities (l :: lhs) (r :: rhs) f
  = \ eq => withEqualities lhs rhs (f . (eq ::))


||| A congruence that's much more convenient to use
export
congruence :
   {pres : Presentation} ->
   {a : PresetoidAlgebra pres.signature} ->
   (n : Nat) -> (t : Term pres.signature (Either (U a) (Fin n))) ->
   PI n Hidden (U a) $ \ lhs =>
   PI n Hidden (U a) $ \ rhs =>
   WithEqualities pres a lhs rhs $
   (|-) {pres} a
      (bindTerm {a = a.algebra} t (fromLeft (\ i => index i lhs)))
      (bindTerm {a = a.algebra} t (fromLeft (\ i => index i rhs)))
congruence n t
  = curry n Hidden _ $ \ lhs =>
    curry n Hidden _ $ \ rhs =>
    withEqualities lhs rhs $ congruence' t

||| A ByAxiom that's much more convenient to use
export
byAxiom' :
  (pres : Presentation) ->
  {0 a : PresetoidAlgebra pres.signature} ->
  (eq : Axiom pres) ->
  PI ((pres.axiom eq).support) Visible (U a) $ \env =>
    (|-) {pres} a (bindTerm {a = a.algebra} (pres.axiom eq).lhs (\ i => index i env))
                  (bindTerm {a = a.algebra} (pres.axiom eq).rhs (\ i => index i env))
byAxiom' pres eq
  = curry (pres.axiom eq).support Visible _ $ \ env =>
    ByAxiom eq (\ i => index i env)

||| A ByAxiom that's much more convenient to use
export
byAxiom :
  (pres : Presentation) ->
  {0 a : PresetoidAlgebra pres.signature} ->
  (eq : Axiom pres) ->
  PI ((pres.axiom eq).support) Hidden (U a) $ \env =>
    (|-) {pres} a (bindTerm {a = a.algebra} (pres.axiom eq).lhs (\ i => index i env))
                  (bindTerm {a = a.algebra} (pres.axiom eq).rhs (\ i => index i env))
byAxiom pres eq
  = curry (pres.axiom eq).support Hidden _ $ \ env =>
    ByAxiom eq (\ i => index i env)
