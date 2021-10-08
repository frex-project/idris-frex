||| Definitions and constructions involving free models
module Frex.Free

import public Frex.Free.Definition
import public Frex.Free.Construction

import Data.Setoid
import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model
import Frex.Powers

import Syntax.PreorderReasoning
import public Data.Fun.Nary


public export
extensionLemma : {0 pres : Presentation} -> {s : Setoid} -> {mod1,mod2 : pres `ModelOver` s} ->
  (h : mod1 ~> mod2) ->
  (s ~~> mod2.Model).rel
    (h.H.H . (mod1.Env))
    mod2.Env
extensionLemma h = h.preserves

public export
freeSolve : {pres : Presentation} -> {s : Setoid} ->
  {mod1,mod2 : pres `ModelOver` s} -> (h : mod1 ~> mod2) ->
  (eq : ( Term pres.signature (U s)
        , Term pres.signature (U s))) ->
  (prf : mod1.Model.rel
     (mod1.Model.Sem (fst eq) mod1.Env.H)
     (mod1.Model.Sem (snd eq) mod1.Env.H)) ->
  mod2.Model.rel
     (mod2.Model.Sem (fst eq) mod2.Env.H)
     (mod2.Model.Sem (snd eq) mod2.Env.H)
freeSolve h eq prf = CalcWith (cast mod2.Model) $
  |~ mod2.Model.Sem (fst eq) mod2.Env.H
  ~~ mod2.Model.Sem (fst eq) (h.H.H . mod1.Env).H
       ..<((eval {x = s}
               {a = mod2.Model.Algebra} (fst eq)).homomorphic
                      (h.H.H . mod1.Env)
                      mod2.Env
                      $ extensionLemma h)
  ~~ mod2.Model.Sem (snd eq) (h.H.H . mod1.Env).H
       ...(eqPreservation eq mod1.Env.H h.H prf)
  ~~ mod2.Model.Sem (snd eq) mod2.Env.H
       ...((eval {x = s}
                 {a = mod2.Model.Algebra} (snd eq)).homomorphic
                      (h.H.H . mod1.Env)
                      mod2.Env
                      $ extensionLemma h)

public export
solveVect : {0 n : Nat} -> {pres : Presentation} -> {a : Model pres} ->
  (free : Free pres (irrelevantCast $ Fin n)) -> (env : Vect n (U a)) ->
  (eq : ( Term pres.signature (Fin n)
        , Term pres.signature (Fin n))) ->
  {auto prf : free.Data.Model.rel
     (free.Sem (fst eq) free.Data.Env.H)
     (free.Sem (snd eq) free.Data.Env.H)}
     ->
  a.rel (a.Sem (fst eq) (flip Vect.index env))
        (a.Sem (snd eq) (flip Vect.index env))
solveVect free env eq =
  let AX : Model pres
      AX = free.Data.Model
      Other : pres `ModelOver` (irrelevantCast $ Fin n)
      Other = MkModelOver
        { Model = a
        , Env   = mate (flip index env)
        }
      h : free.Data ~> Other
      h = free.UP.Exists Other
  in freeSolve h eq prf

public export
solve : (n : Nat) -> {pres : Presentation} -> {a : Model pres} ->
  (free : Free pres (cast $ Fin n)) ->
  PI n Hidden (U a) $ (\ env =>
  (eq : ( Term pres.signature (Fin n)
        , Term pres.signature (Fin n))) ->
  {auto prf : free.Data.Model.rel
     (free.Sem (fst eq) free.Data.Env.H)
     (free.Sem (snd eq) free.Data.Env.H)}
     ->
  a.rel (a.Sem (fst eq) (flip Vect.index env))
        (a.Sem (snd eq) (flip Vect.index env)))
solve n free = Nary.curry n Hidden _ (solveVect free)

public export
prove : {n : Nat} -> {pres : Presentation} ->
  (free : Free pres (cast $ Fin n)) ->
  (eq : ( Term pres.signature (Fin n)
        , Term pres.signature (Fin n))) ->
  {auto prf : free.Data.Model.rel
     (free.Sem (fst eq) free.Data.Env.H)
     (free.Sem (snd eq) free.Data.Env.H)}
     ->
  let free' : Free pres (cast $ Fin n)
      free' = Free.Construction.Free pres (cast $ Fin n)
  in free'.Data.Model.rel
    (free'.Data.Model.Sem (fst eq) (free'.Data.Env.H))
    (free'.Data.Model.Sem (snd eq) (free'.Data.Env.H))
prove free eq = freeSolve
  (free.UP.Exists (Construction.Free pres (cast $ Fin n)).Data) eq prf

public export
(.simplify) : {pres : Presentation} -> {x : Setoid} ->
  (freea : (free : Free pres x ** Model pres)) ->
  (t : Term pres.signature (U x)) -> (env : x ~> cast (snd freea)) ->
  U (snd freea)
(free ** a).simplify t env
  = (free.UP.Exists (MkModelOver a env)).H.H.H (free.Data.Model.Sem t (free.Data.Env).H)

public export
simplifyGeneral : {pres : Presentation} -> {a : Model pres} -> {x : Setoid} ->
  (free : Free pres x) -> (env : x ~> cast a) ->
  (t : Term pres.signature (U x)) ->
  a.rel
    (a.Sem t env.H)
    ((free ** a).simplify t env)
simplifyGeneral free env t =
  let Other : pres `ModelOver` x
      Other = MkModelOver a env
      h : free.Data ~> Other
      h = free.UP.Exists Other
  in a.equivalence.symmetric _ _ $ CalcWith (cast a) $
  |~ h.H.H.H (free.Data.Sem t free.Data.Env.H)
  ~~ a.Sem t (h.H.H . free.Data.Env).H ...(homoPreservesSem h.H _ _)
  ~~ a.Sem t env.H                     ...((eval {x} {a = a.Algebra} t).homomorphic
                                           (h.H.H . free.Data.Env) (Other).Env $
                                           extensionLemma h)
public export
simplifyVect : {0 n : Nat} -> {pres : Presentation} -> {a : Model pres} ->
  (free : Free pres (irrelevantCast $ Fin n)) -> (env : Vect n (U a)) ->
  (t : Term pres.signature (Fin n)) ->
  a.rel
    (a.Sem t $ flip Vect.index env)
    ((free ** a).simplify t (mate $ flip Vect.index env))
simplifyVect free env = simplifyGeneral free (mate $ flip index env)

public export
simplify : (n : Nat) -> {pres : Presentation} -> {a : Model pres} ->
  (free : Free pres (cast $ Fin n)) ->
  PI n Hidden (U a) $ (\ env =>
  (t : Term pres.signature (Fin n)) ->
  a.rel
    (a.Sem t $ flip Vect.index env)
    ((free ** a).simplify t (mate $ flip Vect.index env)))
simplify n free = Nary.curry n Hidden _ (simplifyVect free)
