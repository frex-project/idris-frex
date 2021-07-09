||| Frex is an extensible library of algebraic solver built around the
||| concept of a FRee EXtension from universal algebra.
|||
||| This module imports the core defintions and concepts.
module Frex

import public Data.Setoid

import public Data.Finite

import public Frex.Signature
import public Frex.Algebra
import public Frex.Presentation
import public Frex.Axiom
import public Frex.Model
import public Frex.Powers
import public Frex.Free
import public Frex.Coproduct
import public Frex.Frex
import public Frex.Frex.Construction
import public Frex.Free.Construction.ByFrex
import public Frex.Lemma

import public Data.Fun.Nary

import Syntax.PreorderReasoning

%default total

public export
extEnv : {a : Model pres} -> {x : Setoid} -> (ext : Extension a x) ->
  Either (cast a) x ~> cast ext.Model
extEnv ext = either ext.Embed.H ext.Var

public export
extensionLemma : {a : Model pres} -> {x : Setoid} -> {ext1,ext2 : Extension a x} ->
  (h : ext1 ~> ext2) ->
  (Either (cast {to = Setoid} a) x ~~> ext2.Model).rel
    (h.H.H . (extEnv ext1))
    (extEnv ext2)
extensionLemma h (Left  x) = h.PreserveEmbed _
extensionLemma h (Right i) = h.PreserveVar   _

public export
frexEnv : {a : Model pres} -> {x : Setoid} -> (frex : Frex a x) ->
  Either (cast a) x ~> cast frex.Data.Model
frexEnv frex = extEnv frex.Data

public export
frexify : {pres : Presentation} -> {a : Model pres} -> {x : Setoid} ->
  {ext1,ext2 : Extension a x} -> (h : ext1 ~> ext2) ->
  (eq : ( Term pres.signature (U a `Either` U x)
        , Term pres.signature (U a `Either` U x))) ->
  (prf : ext1.Model.rel
     (ext1.Model.Sem (fst eq) (extEnv ext1).H)
     (ext1.Model.Sem (snd eq) (extEnv ext1).H)) ->
  ext2.Model.rel
     (ext2.Model.Sem (fst eq) (extEnv ext2).H)
     (ext2.Model.Sem (snd eq) (extEnv ext2).H)
frexify h eq prf = CalcWith @{cast ext2.Model} $
  |~ ext2.Model.Sem (fst eq) (extEnv ext2).H
  <~ ext2.Model.Sem (fst eq) (h.H.H . extEnv ext1).H
       ...(ext2.Model.equivalence.symmetric _ _ $
          (eval {x = (cast a) `Either` x}
               {a = ext2.Model.Algebra} (fst eq)).homomorphic
                      (h.H.H . (extEnv ext1))
                      (extEnv ext2)
                      $ extensionLemma h)
  <~ ext2.Model.Sem (snd eq) (h.H.H . extEnv ext1).H
       ...(eqPreservation eq (extEnv ext1).H h.H prf)
  <~ ext2.Model.Sem (snd eq) (extEnv ext2).H
       ...((eval {x = (cast a) `Either` x}
                 {a = ext2.Model.Algebra} (snd eq)).homomorphic
                      (h.H.H . (extEnv ext1))
                      (extEnv ext2)
                      $ extensionLemma h)

public export
solveVect : {0 n : Nat} -> {pres : Presentation} -> {a : Model pres} ->
  (frex : Frex a (cast $ Fin n)) -> (env : Vect n (U a)) ->
  (eq : ( Term pres.signature (U a `Either` Fin n)
        , Term pres.signature (U a `Either` Fin n))) ->
  {auto prf : frex.Data.Model.rel
     (frex.Sem (fst eq) (frexEnv frex).H)
     (frex.Sem (snd eq) (frexEnv frex).H)}
     ->
  a.rel (a.Sem (fst eq) (either Prelude.id (flip Vect.index env)))
        (a.Sem (snd eq) (either Prelude.id (flip Vect.index env)))
solveVect frex env eq =
  let AX : Model pres
      AX = frex.Data.Model
      Other : Extension a (cast $ Fin n)
      Other = MkExtension
        { Model = a
        , Embed = id a
        , Var   = mate (flip index env)
        }
      h : frex.Data ~> Other
      h = frex.UP.Exists Other
  in frexify h eq prf

public export
solve : (n : Nat) -> {pres : Presentation} -> {a : Model pres} ->
  (frex : Frex a (cast $ Fin n)) ->
  PI n Hidden (U a) $ (\ env =>
  (eq : ( Term pres.signature (U a `Either` Fin n)
        , Term pres.signature (U a `Either` Fin n))) ->
  {auto prf : frex.Data.Model.rel
     (frex.Sem (fst eq) (frexEnv frex).H)
     (frex.Sem (snd eq) (frexEnv frex).H)}
     ->
  a.rel (a.Sem (fst eq) (either Prelude.id (flip Vect.index env)))
        (a.Sem (snd eq) (either Prelude.id (flip Vect.index env))))
solve n frex = Nary.curry n Hidden _ (solveVect frex)

public export
proveAux : {n : Nat} -> {pres : Presentation} -> {a : Model pres} ->
  (frex : Frex a (cast $ Fin n)) -> (env : Vect n (U a)) ->
  (eq : ( Term pres.signature (U a `Either` Fin n)
        , Term pres.signature (U a `Either` Fin n))) ->
  {auto prf : frex.Data.Model.rel
     (frex.Sem (fst eq) (frexEnv frex).H)
     (frex.Sem (snd eq) (frexEnv frex).H)}
     ->
  let frex' : Frex a (cast $ Fin n)
      frex' = Frex.Construction.Frex a (cast $ Fin n)
  in frex'.Data.Model.rel
    (frex'.Data.Model.Sem (fst eq) (either frex'.Data.Embed.H.H
                                          (frex'.Data.Var.H)))
    (frex'.Data.Model.Sem (snd eq) (either frex'.Data.Embed.H.H
                                          (frex'.Data.Var.H)))
proveAux frex env eq = frexify
  (frex.UP.Exists (Construction.Frex a (cast $ Fin n)).Data) eq prf


public export
prove : (n : Nat) -> {pres : Presentation} -> {a : Model pres} ->
  (frex : Frex a (cast $ Fin n)) ->
  PI n Hidden (U a) $ (\ env =>
  (eq : ( Term pres.signature (U a `Either` Fin n)
        , Term pres.signature (U a `Either` Fin n))) ->
  {auto prf : frex.Data.Model.rel
     (frex.Sem (fst eq) (frexEnv frex).H)
     (frex.Sem (snd eq) (frexEnv frex).H)}
     ->
  let frex' : Frex a (cast $ Fin n)
      frex' = Frex.Construction.Frex a (cast $ Fin n)
  in frex'.Data.Model.rel
    (frex'.Data.Model.Sem (fst eq) (either frex'.Data.Embed.H.H
                                          (frex'.Data.Var.H)))
    (frex'.Data.Model.Sem (snd eq) (either frex'.Data.Embed.H.H
                                          (frex'.Data.Var.H))))
prove n frex = Nary.curry n Hidden _ (proveAux frex)
