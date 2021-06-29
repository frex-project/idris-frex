||| Frex is an extensible library of algebraic solver built around the
||| concept of a FRee EXtension from universal algebra.
|||
||| This module imports the core defintions and concepts.
module Frex

import public Data.Setoid

import public Frex.Signature
import public Frex.Algebra
import public Frex.Presentation
import public Frex.Axiom
import public Frex.Model
import public Frex.Powers
import public Frex.Free
import public Frex.Coproduct
import public Frex.Frex

import public Data.Fun.Nary

public export
frexEnv : {a : Model pres} -> {x : Setoid} -> (frex : Frex a x) ->
  Either (cast a) x ~> cast frex.Data.Model
frexEnv frex = either frex.Data.Embed.H
                      frex.Data.Var
public export
frexify : {0 n : Nat} -> {pres : Presentation} -> {a : Model pres} ->
  (frex : Frex a (cast $ Fin n)) -> (env : Vect n (U a)) ->
  (eq : ( Term pres.signature (U a `Either` Fin n)
        , Term pres.signature (U a `Either` Fin n))) ->
  {auto prf : frex.Data.Model.rel
     (frex.Sem (fst eq) (frexEnv frex).H)
     (frex.Sem (snd eq) (frexEnv frex).H)}
     ->
  a.rel (a.Sem (fst eq) (either Prelude.id (flip Vect.index env)))
        (a.Sem (snd eq) (either Prelude.id (flip Vect.index env)))
frexify frex env eq =
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

      env' : Either (cast a) (cast $ Fin n) ~> cast {to = Setoid} a
      env' = either (id $ cast a) (mate $ flip Vect.index env)
      extensionLemma : (Either (cast {to = Setoid} a) (cast $ Fin n) ~~>
                         (cast (Other).Model)).equivalence.relation
              (h.H.H . (frexEnv frex))
              env'
      extensionLemma (Left  x) = h.PreserveEmbed _
      extensionLemma (Right i) = h.PreserveVar   _

      lemma : (t : Term pres.signature $ (U a) `Either` (Fin n)) ->
        (Other).Model.rel
          (bindTerm {a = a.Algebra.algebra} t env'.H)
          (h.H.H.H (bindTerm {a = (AX).Algebra.algebra} t (frexEnv frex).H))
      lemma t = CalcWith @{cast (Other).Model} $
        |~ bindTerm {a = a.Algebra.algebra} t env'.H
        <~ bindTerm {a = a.Algebra.algebra} t (h.H.H.H . (frexEnv frex).H)
             ...((Other).Model.equivalence.symmetric _ _
                 $ (eval {x = (cast a) `Either` (cast $ Fin n)}
                       {a = a.Algebra} t).homomorphic
                       (h.H.H . (frexEnv frex))
                       env'
                       extensionLemma)
        <~ h.H.H.H (bindTerm {a = (AX).Algebra.algebra} t (frexEnv frex).H)
             ...((Other).Model.equivalence.symmetric _ _ $
                 homoPreservesSem h.H t (frexEnv frex).H)

  in CalcWith @{cast (Other).Model} $
  |~ bindTerm {a = a.Algebra.algebra} (fst eq) env'.H
  <~ h.H.H.H (bindTerm {a = (AX).Algebra.algebra} (fst eq) (frexEnv frex).H)
       ...(lemma (fst eq))
  <~ h.H.H.H (bindTerm {a = (AX).Algebra.algebra} (snd eq) (frexEnv frex).H)
       ...(h.H.H.homomorphic _ _ prf)
  <~ bindTerm {a = a.Algebra.algebra} (snd eq) env'.H
       ...((Other).Model.equivalence.symmetric _ _ $ lemma (snd eq))

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
solve n frex = Nary.curry n Hidden _ (frexify frex)
