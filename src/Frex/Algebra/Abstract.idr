module Frex.Algebra.Abstract

import Frex.Signature
import Frex.Algebra

import Data.Either.Extra
import Data.Fin.Extra
import Data.Vect.Extra1

%default total

export
bindTermMapFusion :
  {alg : Algebra sig} ->
  (ren : a -> vars) -> (t : Term sig a) -> (env : vars -> U alg) ->
  bindTerm (map ren t) env === bindTerm t (env . ren)
export
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

export
bindTermExtensional :
  {alg : Algebra sig} ->
  (t : Term sig vars) -> {lhs, rhs : vars -> U alg} ->
  (eq : (v : vars) -> lhs v === rhs v) ->
  bindTerm t lhs === bindTerm t rhs
export
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

public export
record Abstract
  {a, b : Type}
  (sig : Signature)
  (t : Term sig (Either a b)) where
  constructor MkAbstract
  {vars : Nat}
  u     : Term sig (Either (Fin vars) b)
  vals  : Vect vars a
  valid : t === map (mapFst (\ k => index k vals)) u

public export
record Abstracts
  {a, b : Type}
  {n : Nat}
  (sig : Signature)
  (ts : Vect n (Term sig (Either a b))) where
  constructor MkAbstracts
  {vars : Nat}
  us    : Vect n (Term sig (Either (Fin vars) b))
  vals  : Vect vars a
  valid : ts === map (map (mapFst (\ k => index k vals))) us

export
(::) : Abstract sig t -> Abstracts sig ts -> Abstracts sig (t :: ts)
(::) (MkAbstract {vars = vars1} u vals1 tequ)
     (MkAbstracts {vars = vars2} us vals2 tsequs) = MkAbstracts
  (map (mapFst (indexSum . Left)) u :: map (map (mapFst (indexSum . Right))) us)
  (vals1 ++ vals2)
  (cong2 (::) left rights) where

  left : t === ?
  left = trans tequ
       $ trans (bindTermExtensional u
               $ \ v => cong Done
               $ trans (mapFstExtensional
                         (\ x => sym (indexIndexSumLeft {ys = vals2} x))
                         v)
               $ sym $ mapFstFusion
                         {f = indexSum . Left}
                         {g = \ k => index k (vals1 ++ vals2)}
                         v)
       $ sym $ bindTermMapFusion
                 (mapFst (indexSum . Left))
                 u
                 (Done . mapFst (\ k => index k (vals1 ++ vals2)))

  right : (t : Term sig (Either (Fin vars2) b)) ->
          map (mapFst (\ k => index k vals2)) t
          === map (mapFst (\ k => index k (vals1 ++ vals2)))
              (map (mapFst (Extra.indexSum {m = vars1} . Right)) t)
  right t = trans (bindTermExtensional t
                  $ \ v => cong Done
                  $ trans (mapFstExtensional
                            (\ x => sym (indexIndexSumRight x))
                            v)
                  $ sym $ mapFstFusion
                            {f = indexSum . Right}
                            {g = \ k => index k (vals1 ++ vals2)}
                            v)
          $ sym $ bindTermMapFusion
                    (mapFst (indexSum . Right))
                    t
                    (Done . mapFst (\ k => index k (vals1 ++ vals2)))

  rights : ts === ?
  rights = trans tsequs
         $ trans (mapExtensional _ _ right us)
         $ sym $ mapFusion (map (mapFst (\ k => index k (vals1 ++ vals2))))
                           (map (mapFst (indexSum . Right)))
                           us

export
mkAbstract : (t : Term sig (Either a (Fin n))) -> Abstract sig t

export
mkAbstracts :
  (ts : Vect len (Term sig (Either a (Fin n)))) ->
  Abstracts sig ts

mkAbstract (Done (Left v)) = MkAbstract (Done (Left FZ)) [v] Refl
mkAbstract (Done (Right a)) = MkAbstract (Done (Right a)) [] Refl
mkAbstract (Call f xs) = case mkAbstracts xs of
  MkAbstracts us vals valid =>
    MkAbstract (Call f us) vals
      $ cong (Call f)
      $ trans valid
      $ sym $ bindTermsIsMap {a = Free sig (Either a (Fin n))} _ _

mkAbstracts [] = MkAbstracts [] [] Refl
mkAbstracts (t :: ts) = mkAbstract t :: mkAbstracts ts
