module Frex.Powers.Construction

import Data.Setoid
import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model
import Decidable.Order

import Data.Vect
import Data.Vect.Properties


import Frex.Powers.Definition


parameters {0 Sig : Signature} (X : Setoid) (A : SetoidAlgebra Sig)
  public export
  PowerSetoid : Setoid
  PowerSetoid = X ~~> cast A

  public export
  PowerAlgebra : Algebra Sig
  PowerAlgebra = MkAlgebra (U PowerSetoid)
      \f,phis => 
      MkSetoidHomomorphism (\i => (A).algebra.Sem f (map (\phi => phi.H i) phis)) 
                           \u, v, prf => congruence A f _ _ \i =>
                             CalcWith @{cast A} $
                             |~ index i (map (\phi => phi.H u) phis)
                             ~~ (index i phis).H u ...(indexNaturality _ _ _)
                             <~ (index i phis).H v ...((index i phis).homomorphic _ _ prf)
                             ~~ index i (map (\phi => phi.H v) phis) ...(sym $ indexNaturality _ _ _)

  public export
  (~~>) : SetoidAlgebra Sig
  %unbound_implicits off
  (~~>) = 
    let equiv : Equivalence (U PowerSetoid)
        equiv = equivalence PowerSetoid
    in MkSetoidAlgebra PowerAlgebra
    equiv
    \f, phis, psis, prf, this => (A).congruence f _ _ 
      \i => CalcWith @{cast A} $
      |~ index i (map (\phi => phi.H this) phis)
      ~~ (index i phis).H this ...(indexNaturality _ _ _)
      <~ (index i psis).H this ...(prf i this) 
      ~~ index i (map (\phi => phi.H this) psis) ...(sym $ indexNaturality _ _ _)
  %unbound_implicits on

parameters {0 Sig : Signature} {X : Setoid} {A : SetoidAlgebra Sig}
  public export
  eval : (x : U X) -> (X ~~> A) ~> A
  eval x = MkSetoidHomomorphism 
    (MkSetoidHomomorphism (\phi => phi.H x) 
                          (\phi, psi, prf => prf x))
    \f, phis => A .equivalence.reflexive 
              $ ((X ~~> A).algebra.Sem f phis).H x
  
  -- In fact, holds on the nose (i.e., with equality), but it's much
  -- easier to just use the existing homoPreservesSem (which also
  -- holds on the nose...)
  public export
  pointwiseBind : (t : Term Sig y) -> (env : y -> U (X ~~> A)) -> (x : U X) ->
    A .equivalence.relation
     ((bindTerm {a = (X ~~> A).algebra} t        env  ).H x)
      (bindTerm {a = A .algebra       } t \i => (env i).H x)
  pointwiseBind t env x 
    = homoPreservesSem (Frex.Powers.Construction.eval x) t env

namespace Model
  public export
  (~~>) : {pres : Presentation} -> (x : Setoid) -> (a : Model pres) -> Model pres
  (~~>) x a = let X_to_A : SetoidAlgebra pres.signature
                  X_to_A = x ~~> a.Algebra
              in MkModel X_to_A
              \ax, env, x => CalcWith @{cast a} $
              |~ (bindTerm {a = X_to_A   .algebra} (pres.axiom ax).lhs env).H x
              <~ bindTerm  {a = a.Algebra.algebra} (pres.axiom ax).lhs (\i => (env i).H x)
                                               ...(pointwiseBind _ _ _)
              <~ bindTerm  {a = a.Algebra.algebra} (pres.axiom ax).rhs (\i => (env i).H x)
                                               ...(a.Validate _ _)
              <~ (bindTerm {a = X_to_A .algebra} (pres.axiom ax).rhs env).H x  
                                               ...(_.symmetric _ _  $ 
                                                   pointwiseBind _ _ _)
  
  
public export 
(^) : {pres : Presentation} -> 
  (a : Model pres) -> (x : Setoid) -> Power x a
  
%unbound_implicits off
a ^ x = MkPower 
  (MkParameterisation 
     (x ~~> a) 
     $ MkSetoidHomomorphism
       eval
       \x,y,x_eq_y,f => f.homomorphic _ _ x_eq_y)
  $ IsUniversal 
  { Exists = \other => 
      MkParameterisationMorphism 
        (MkSetoidHomomorphism 
          (MkSetoidHomomorphism 
               (\u => MkSetoidHomomorphism (\i => 
                  let f  = other.Eval.H i
                  in f.H.H u)
                 \i,j,i_eq_j => 
                   (other.Eval).homomorphic i j i_eq_j u)
            \u,v,u_eq_v,i =>
              let phi : other.Model ~> a
                  phi = .H (.Eval other) i
              in  phi.H.homomorphic u v u_eq_v)
          \op,env,i => 
             let OtoA : (other.Model ~> a)
                        -- Not sure why we need the annotation --- idris bug?
                 OtoA = (the (U x -> U (other.Model ~~> a))
                            ((other.Eval).H)) i
             in CalcWith @{cast a} $
             |~ OtoA .H.H (other.Model.Sem op env)
             <~ a.Sem op (map (OtoA .H.H) env) ...(OtoA .preserves op env)
                                                  -- vv too disgusting...
             ~~ a.Sem op (map (\phi => phi.H i) (map _ env))
                              ...(cong (a.Sem op)
                                 $ sym $ mapFusion _ _ env))
        \u,i => (cast a).equivalence.reflexive _
  , Unique = \other, extend1,extend2,u,i => CalcWith @{cast a} $
      |~ (the _ $ extend1.H.H.H u).H i
      <~ (the _ $ other.Eval.H i).H.H u ...(extend1.preserve u i)
      <~ (the _ $ extend2.H.H.H u).H i  ...((cast a).equivalence.symmetric _ _ $ 
                                            extend2.preserve u i)
  }
%unbound_implicits off
