||| When the exponent is `Fin n`, we can represent the power Fin n
||| `Power` A using `Vect n A`.
module Frex.Powers.Fin

import Data.Setoid
import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model

import Data.Vect
import Data.Vect.Properties


import Frex.Powers.Definition
import Frex.Powers.Construction
import Frex.Powers.Abstract

parameters {0 Sig : Signature} (N : Nat) (A : SetoidAlgebra Sig)
  public export
  FinPowerSetoid : Setoid
  FinPowerSetoid = VectSetoid N (cast A)
  
  public export
  FinPowerAlgebra : Algebra Sig
  FinPowerAlgebra = MkAlgebra (U FinPowerSetoid) \op, xss =>
    map (A .algebra.Sem op) (transpose xss)

  public export
  indexHomomorphismLemma : 
    (i : Fin N) -> (op : Op Sig) -> 
    (zss : Vect (arity op) (U FinPowerSetoid)) -> 
    A .equivalence.relation
       (index i (map (A .algebra.Sem op) (transpose zss)))
       (A .algebra.Sem op (map (index i) zss))
  indexHomomorphismLemma i op zss = CalcWith @{cast A} $
          |~ index i (map (A .algebra.Sem op) (transpose zss))
          ~~ A .algebra.Sem op (     index i $ transpose zss)  
               ...(indexNaturality _ _ _)
          <~ A .algebra.Sem op (map (index i)            zss)  
               ...(A .congruence op _ _ $ reflect (VectSetoid _ $ cast A) 
                   $ indexTranspose _ _)
    

  public export
  FinPowerSetoidAlgebra : SetoidAlgebra Sig
  FinPowerSetoidAlgebra = 
    let equiv : Equivalence (U FinPowerSetoid)
        equiv = FinPowerSetoid .equivalence
    in MkSetoidAlgebra FinPowerAlgebra equiv \op,xss,yss,prf,i => 
    let lemma : (j : Fin $ arity op) -> 
                A .equivalence.relation 
                  (index j (map (index i) xss))
                  (index j (map (index i) yss))
        lemma j = CalcWith @{cast A} $
          |~ (index j (map (index i)  xss))
          ~~ index i (index j xss)        ...(      indexNaturality _ _ _)
          <~ index i (index j yss)        ...(prf j i)
          ~~ index j (map (index i)  yss) ...(sym $ indexNaturality _ _ _)
    in CalcWith @{cast A} $
    |~ index i (map (A .algebra.Sem op) (transpose xss))
    <~ A .algebra.Sem op (map (index i) xss) ...(indexHomomorphismLemma i op xss)
    <~ A .algebra.Sem op (map (index i) yss) ...(A .congruence op 
                                                   (map (index i) xss) 
                                                   (map (index i) yss) lemma)
    <~ index i (map (A .algebra.Sem op) 
                    (transpose yss))         ...((cast A).equivalence.symmetric 
                                                  _ _ $
                                                 indexHomomorphismLemma i op yss)

parameters {0 Sig : Signature} {N : Nat} {A : SetoidAlgebra Sig}
  public export
  eval : (x : Fin N ) -> (N `FinPowerSetoidAlgebra` A) ~> A
  eval x = MkSetoidHomomorphism
    (MkSetoidHomomorphism (index x) 
      \xs,ys,prf => prf x)
     (indexHomomorphismLemma N A x)
      
  public export
  pointwiseBind : (t : Term Sig y) -> (env : y -> Vect N (U A)) -> (x : Fin N) ->
    A .equivalence.relation
     (index x
      (bindTerm {a = (N `FinPowerSetoidAlgebra` A).algebra} 
                                        t            env))
    (  bindTerm {a = A .algebra       } t (index x . env))
  pointwiseBind t env x = homoPreservesSem (Fin.eval x) t env

  public export
  representation : (N `FinPowerSetoidAlgebra` A) <~> (cast (Fin N) ~~> A)
  representation = 
    let fwd : Vect N (U A) -> (U (cast (Fin N) ~~> A))
        fwd xs = MkSetoidHomomorphism 
                   (\x => index x xs)
                   \x,y,x_eq_y => reflect (cast A) 
                     (cong (flip index xs) x_eq_y)
    in MkIsomorphism
    { Iso = MkIsomorphism 
        { Fwd = MkSetoidHomomorphism 
                  fwd
                  \xs,ys,prf => prf
        , Bwd = MkSetoidHomomorphism
                 (\phi => tabulate phi.H)
                 \phis, psis, prf, i => CalcWith @{cast A} $ 
                   |~ index i (tabulate phis.H)
                   ~~ phis.H i ...(indexTabulate _ _)
                   <~ psis.H i ...(prf i)
                   ~~ index i (tabulate psis.H) ...(sym $ indexTabulate _ _)
        , Iso = IsIsomorphism
            { BwdFwdId = \x, i => reflect (cast A) $ indexTabulate _ _ 
            , FwdBwdId = \i, x => reflect (cast A) $ indexTabulate _ _ 
            }
        }
    , FwdHomo = \op, xss, i => CalcWith @{cast A} $
        |~ index i ((N `FinPowerSetoidAlgebra` A).algebra.Sem op xss)
        <~ A .algebra.Sem op (map (index i) xss) 
             ...((eval i).preserves op xss)
        ~~ A .algebra.Sem op (map (\xs => (fwd xs).H i)      xss) 
             ...(Refl)
        ~~ A .algebra.Sem op (map (\phi => phi.H i) (map fwd xss)) 
             ...(cong (A .algebra.Sem op) $ sym $
                 mapFusion _ _ _)
    }

public export  
(~~>) : {pres : Presentation} -> (n : Nat) -> (a : Model pres) 
  -> Model pres
n ~~> a = 
  transport (cast (Fin n) ~~> a) $
    sym representation

public export 
(^) : {pres : Presentation} -> 
  (a : Model pres) -> (n : Nat) -> Power (cast $ Fin n) a
a ^ n = Abstract.transport (a ^ (cast {to = Setoid} (Fin n))) 
        (sym representation)
