||| A detour, teaching the type-checker to brute-force binary arithmetic
module Binary.BruteForce

import Data.Nat
import Data.Nat.Division
import Data.Nat.Order
import Data.Nat.Order.Properties
import Data.Nat.Properties

import Data.Fin
import VectReasoning

import Frex
import Frex.Free

import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Nat

import Syntax.PreorderReasoning


import Binary.Modular
import Binary.Core


-- Auto search doesn't want to solve metavariables and fails to find the right
-- instance sometimes :(
public export
mapVect : (f : a -> b) -> Vect n a -> Vect n b
mapVect = map

public export
Tabulate : {n : Nat} -> {F : Fin n -> Type}
           -> (f : (i : Fin n) -> F i)
           -> HVect (map F (range {len = n}))
Tabulate {n = 0} f = []
Tabulate {n = S k} f =
  let u = Tabulate {n = k} {F = F . FS } (\i => f (FS i)) in
  let eq : ((mapVect (F . FS) $
           Data.Vect.Fin.tabulate Prelude.Basics.id {len = k}) ~=~
           (mapVect F (Data.Vect.Fin.tabulate FS {len = k})))
      eq = let y = sym (Data.Vect.Properties.Map.mapTabulate FS id)
           in trans (sym (mapFusion F FS (tabulate id))) (cong (mapVect F) y)
  in f FZ :: replace {p = HVect} eq u

public export
ElemMap : (f : a -> b) -> x `Elem` xs -> f x `Elem` (mapVect f xs)
ElemMap f  Here         = Here
ElemMap f (There later) = There $ ElemMap f later

public export
ElemInLft : x `Elem` xs -> x `Elem` (xs ++ ys)
ElemInLft  Here         = Here
ElemInLft (There later) = There (ElemInLft later)

public export
ElemInRgt : {ys : Vect len a } -> x `Elem` xs -> x `Elem` (ys ++ xs)
ElemInRgt {ys = []} ptr = ptr
ElemInRgt {ys = (y :: ys)} ptr = There $ ElemInRgt ptr

public export
TruthTableRows : (n : Nat) -> Vect (2 `power` n) (Vect n Nat)
TruthTableRows 0 = [[]]
TruthTableRows (S n) =
  let u = TruthTableRows n
      result = map (\ row => (0 :: row)) u
             ++map (\ row => (1 :: row)) u
      eq : {n : Nat} -> (2 `power` n) + (0 * (2 `power` n)) = (2 `power` n)
      eq = Frex.solve 1 (Frex Nat.Additive) $
                     (Dyn 0 :+: Sta 0 =-= Dyn 0)
  in rewrite eq {n} in result

public export
TruthTableCovers : {n : Nat} -> (env : Vect n (b : Nat ** Bit b)) ->
  map DPair.fst env `Elem` (TruthTableRows n)
TruthTableCovers [] = Here
TruthTableCovers {n = S n} ((MkDPair 0 O) :: xs) =
  let v0 : {n:Nat} -> (2 `power` n) + (0 * (2 `power` n)) = (2 `power` n)
      v0 =  Frex.solve 1 (Frex Nat.Additive) $ (Dyn 0 :+: Sta 0 =-= Dyn 0) in
  let result = ElemInLft {ys = map (1 ::) $ TruthTableRows n}
             $ ElemMap (0 ::) (TruthTableCovers xs) in
  rewrite v0 {n} in
  result

TruthTableCovers {n = S n} ((MkDPair 1 I) :: xs) =
  let v0 : {n:Nat} -> (2 `power` n) + (0 * (2 `power` n)) = (2 `power` n)
      v0 =  Frex.solve 1 (Frex Nat.Additive) $ (Dyn 0 :+: Sta 0 =-= Dyn 0) in
  let result = ElemInRgt {ys = map (0 ::) $ TruthTableRows n}
             $ ElemMap (1 ::) (TruthTableCovers xs) in
  rewrite v0 {n} in
  result

public export
bruteForce : {n : Nat} -> (fg : Vect n Nat -> (Nat, Nat))
          -> {auto prf : HVect $ tabulate
                           (\i => fst (fg (index i $ TruthTableRows n)) =
                                  snd (fg (index i $ TruthTableRows n)))
             }
          -> (env : Vect n (b : Nat ** Bit b))
          -> fst (fg (map DPair.fst env))
           = snd (fg (map DPair.fst env))
bruteForce fg {prf} env =
  {- This is abominable. -}
  rewrite sym $ ElemToFinSpec (TruthTableCovers env) in
  rewrite sym $ indexTabulate (\i => fst (fg (index i $ TruthTableRows n)) =
                                     snd (fg (index i $ TruthTableRows n)))
                              (elemToFin $ TruthTableCovers env) in
  index (elemToFin $ TruthTableCovers env) prf

-- ------------------ end of detour --------------------------
