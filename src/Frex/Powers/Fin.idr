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


public export
FinPowerSetoid : {0 sig : Signature} -> (n: Nat) -> (a: SetoidAlgebra sig) -> Setoid
FinPowerSetoid n a = VectSetoid n (cast a)

public export
FinPowerAlgebra : {0 sig : Signature} -> (n: Nat) -> (a: SetoidAlgebra sig) ->  Algebra sig
FinPowerAlgebra n a = MakeAlgebra (U $ FinPowerSetoid n a) \op, xss =>
  map (a.algebra.Sem op) (transpose xss)

public export
indexHomomorphismLemma :  {0 sig : Signature} -> (n: Nat) -> (a: SetoidAlgebra sig) ->
  (i : Fin n) -> (op : Op sig) ->
  (zss : Vect (arity op) (U $ FinPowerSetoid n a)) ->
  a.equivalence.relation
     (index i (map (a.Sem op) (transpose zss)))
     (a.algebra.Sem op (map (index i) zss))
indexHomomorphismLemma n a i op zss = CalcWith @{cast a} $
        |~ index i (map (a.Sem op) (transpose zss))
        ~~ a.Sem op (     index i $ transpose zss)
             ...(indexNaturality _ _ _)
        <~ a.Sem op (map (index i)            zss)
             ...(a.congruence op _ _ $ reflect (VectSetoid _ $ cast a)
                 $ indexTranspose _ _)

public export
FinPowerSetoidAlgebra : {0 sig : Signature} -> (n: Nat) -> (a: SetoidAlgebra sig) -> SetoidAlgebra sig
FinPowerSetoidAlgebra n a =
  let equiv : Equivalence (U $ FinPowerSetoid n a)
      equiv = (FinPowerSetoid n a).equivalence
  in MkSetoidAlgebra (FinPowerAlgebra n a) equiv \op,xss,yss,prf,i =>
  let lemma : (j : Fin $ arity op) ->
              a.equivalence.relation
                (index j (map (index i) xss))
                (index j (map (index i) yss))
      lemma j = CalcWith @{cast a} $
        |~ (index j (map (index i)  xss))
        ~~ index i (index j xss)        ...(      indexNaturality _ _ _)
        <~ index i (index j yss)        ...(prf j i)
        ~~ index j (map (index i)  yss) ...(sym $ indexNaturality _ _ _)
  in CalcWith @{cast a} $
  |~ index i (map (a.Sem op) (transpose xss))
  <~ a.Sem op (map (index i) xss) ...(indexHomomorphismLemma n a _ _ _)
  <~ a.Sem op (map (index i) yss) ...(a.congruence op
                                       (map (index i) xss)
                                       (map (index i) yss) lemma)
  <~ index i (map (a.Sem op)
                  (transpose yss))         ...((cast a).equivalence.symmetric
                                                _ _ $
                                               indexHomomorphismLemma n a _ _ _)

public export
eval : {0 sig : Signature} -> {n : Nat} -> {a : SetoidAlgebra sig} ->
  (x : Fin n) -> (n `FinPowerSetoidAlgebra` a) ~> a
eval x = MkSetoidHomomorphism
  (MkSetoidHomomorphism (index x)
    \xs,ys,prf => prf x)
   (indexHomomorphismLemma n a x)

public export
pointwiseBind : {0 sig : Signature} -> {n : Nat} -> {a : SetoidAlgebra sig} 
  -> (t : Term sig y) -> (env : y -> Vect n (U a)) -> (x : Fin n) ->
  a.equivalence.relation
   (index x
    ((n `FinPowerSetoidAlgebra` a).Sem t            env))
    (                           a .Sem t (index x . env))
pointwiseBind t env x = homoPreservesSem (Fin.eval x) t env

public export
representation : {0 sig : Signature} -> {n : Nat} -> {a : SetoidAlgebra sig} -> 
  (n `FinPowerSetoidAlgebra` a) <~> (cast (Fin n) ~~> a)
representation =
  let fwd : Vect n (U a) -> (U (cast (Fin n) ~~> a))
      fwd xs = MkSetoidHomomorphism
                 (\x => index x xs)
                 \x,y,x_eq_y => reflect (cast a)
                   (cong (flip index xs) x_eq_y)
  in MkIsomorphism
  { Iso = MkIsomorphism
      { Fwd = MkSetoidHomomorphism
                fwd
                \xs,ys,prf => prf
      , Bwd = MkSetoidHomomorphism
               (\phi => tabulate phi.H)
               \phis, psis, prf, i => CalcWith @{cast a} $
                 |~ index i (tabulate phis.H)
                 ~~ phis.H i ...(indexTabulate _ _)
                 <~ psis.H i ...(prf i)
                 ~~ index i (tabulate psis.H) ...(sym $ indexTabulate _ _)
      , Iso = IsIsomorphism
          { BwdFwdId = \x, i => reflect (cast a) $ indexTabulate _ _
          , FwdBwdId = \i, x => reflect (cast a) $ indexTabulate _ _
          }
      }
  , FwdHomo = \op, xss, i => CalcWith @{cast a} $
      |~ index i ((n `FinPowerSetoidAlgebra` a).Sem op xss)
      <~ a.Sem op (map (index i) xss)
           ...((eval i).preserves op xss)
      ~~ a.Sem op (map (\xs => (fwd xs).H i)      xss)
           ...(Refl)
      ~~ a.Sem op (map (\phi => phi.H i) (map fwd xss))
           ...(cong (a.Sem op) $ sym $
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
