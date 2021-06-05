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

parameters {0 Sig : Signature} (N : Nat) (A : SetoidAlgebra Sig)
  public export
  FinPowerSetoid : Setoid
  FinPowerSetoid = VectSetoid N (cast A)
  
  public export
  FinPowerAlgebra : Algebra Sig
  FinPowerAlgebra = MkAlgebra (U FinPowerSetoid) \op, xss =>
    map (A .algebra.Sem op) (transpose xss)

  public export
  FinPowerSetoidAlgebra : SetoidAlgebra Sig
  FinPowerSetoidAlgebra = 
    let equiv : Equivalence (U FinPowerSetoid)
        equiv = FinPowerSetoid .equivalence
    in MkSetoidAlgebra FinPowerAlgebra equiv \op,xss,yss,prf,i => 
    let lemma1 : (zss : Vect (arity op) (U FinPowerSetoid)) -> 
                  A .equivalence.relation
                    (index i (map (A .algebra.Sem op) (transpose zss)))
                    (A .algebra.Sem op (map (index i) zss))
        lemma1 zss = CalcWith @{cast A} $
          |~ index i (map (A .algebra.Sem op) (transpose zss))
          ~~ A .algebra.Sem op (     index i $ transpose zss)  ...(?h2'')
          ~~ A .algebra.Sem op (map (index i)            zss)  ...(?h3'')
        lemma2 : (j : Fin $ arity op) -> 
                 A .equivalence.relation 
                   (index j (map (index i) xss))
                   (index j (map (index i) yss))
        lemma2 j = CalcWith @{cast A} $
          |~ (index j (map (index i)  xss))
          ~~ index i (index j xss)        ...(      indexNaturality _ _ _)
          <~ index i (index j yss)        ...(prf j i)
          ~~ index j (map (index i)  yss) ...(sym $ indexNaturality _ _ _)
    in CalcWith @{cast A} $
    |~ index i (map (A .algebra.Sem op) (transpose xss))
    <~ A .algebra.Sem op (map (index i) xss)             ...(lemma1 xss)
    <~ A .algebra.Sem op (map (index i) yss)             ...(A .congruence op 
                                                              (map (index i) xss) 
                                                              (map (index i) yss) lemma2)
    <~ index i (map (A .algebra.Sem op) (transpose yss)) ...((cast A).equivalence.symmetric _ _ $
                                                             lemma1 yss)

  
