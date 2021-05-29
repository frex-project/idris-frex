module Frex.Powers.Construction

import Data.Setoid
import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model

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
  
  public export
  pointwiseBind : (t : Term Sig y) -> (env : y -> U (X ~~> A)) -> (x : U X) ->
    (bindTerm {a = (X ~~> A).algebra} t               env).H x = 
     bindTerm {a = A .algebra       } t \i => (env i).H x
  
  public export
  pointwiseBindTerms : (ts : Vect n $ Term Sig y) -> (env : y -> U (X ~~> A)) -> (x : U X) ->
    map (\phi => .H phi x) (bindTerms {a = (X ~~> A).algebra} ts               env) =
    bindTerms {a = A .algebra       } ts \i => (env i).H x
  pointwiseBindTerms    []     env x = Refl
  pointwiseBindTerms (t :: ts) env x 
    = cong2 (::) (pointwiseBind      t  env x) 
                 (pointwiseBindTerms ts env x)
  
  pointwiseBind (Done v   ) env x = Refl
  pointwiseBind (Call f ts) env x = cong (A .algebra.Sem f) $ pointwiseBindTerms ts env x
  
namespace Model
  public export
  (~~>) : {pres : Presentation} -> (x : Setoid) -> (a : Model pres) -> Model pres
  (~~>) x a = let X_to_A : SetoidAlgebra pres.signature
                  X_to_A = x ~~> a.Algebra
              in MkModel X_to_A
              \ax, env, x => CalcWith @{cast a} $
              |~ (bindTerm {a = X_to_A   .algebra} (pres.axiom ax).lhs env).H x
              ~~ bindTerm  {a = a.Algebra.algebra} (pres.axiom ax).lhs (\i => (env i).H x)
                                               ...(pointwiseBind _ _ _)
              <~ bindTerm  {a = a.Algebra.algebra} (pres.axiom ax).rhs (\i => (env i).H x)
                                               ...(a.Validate _ _)
              ~~ (bindTerm {a = X_to_A .algebra} (pres.axiom ax).rhs env).H x  
                                               ...(sym $ pointwiseBind _ _ _)
  
  
