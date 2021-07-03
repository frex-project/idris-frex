module Modular

import Data.List
import Data.Vect
import Data.Vect.Elem
import Data.Nat
import Data.Fin

import VectReasoning
{-- rethink module hierarchy exports --}
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic
import Syntax.WithProof
import Algebras
import Models
import CMonoids
import Monoids
import Frex
import Carriers
import Signatures

import Free
import CMonoids.Coproducts
import CMonoids.Semiring
import Decidable.Equality

import VectReasoning
import Coproducts
import Powers

import CMonoids.Frex
import CMonoids.Free
import CMonoids.Integer
import Signatures
import Presentations

import Data.Primitives.Views
import Data.Integer.Properties


import Views

import Util

%default total

frexNatPlus : {n : Nat} -> Free_extender CMonoid_Th Additive_Nat (Fin n)
frexNatPlus {n} = CMonoids.Frex.Frex Additive_Nat n
{-
frexIntegerPlus : {n : Nat} -> Free_extender CMonoid_Th Additive_Integer (Fin n)
frexIntegerPlus {n} = CMonoids.Frex.Frex Additive_Integer n

-- Weird, these lines take forever to type-check
frexIntegerMult : {n : Nat} -> Free_extender CMonoid_Th Multiplicative_Integer (Fin n)
frexIntegerMult {n} = CMonoids.Frex.Frex Multiplicative_Integer n
-}
{-
infix 6 <<=, <<

data (<<=) : (a : Nat) -> (b : Nat) -> Type where
  DiffIs :  (diff : Nat) -> {auto 0 addDiff : diff + a = b} -> a <<= b
    
public export
(<<) : (a : Nat) -> (b : Nat) -> Type 
(<<) a b = (1 + a) <<= b
  
public export
diff : a <<= b -> Nat
diff (DiffIs d) = d
  
public export 
0
addDiff : (delta : a <<= b) -> delta.diff + a = b
addDiff (DiffIs _ {addDiff = ad}) = ad

prefix 5 |- , ~|

public export
(|-) : (b : Bool) -> Type
(|-) b = b = True

public export
(~|) : (b : Bool) -> Type
(~|) b = b = False

export
absurdity : (0 _ : |- b) -> (0 _ : ~| b) -> x
absurdity Refl Refl impossible

export
0
monotoneSucc : {a,b : Integer} -> (|-     a >=     b) 
                                   -----------------
                               -> (|- 1 + a >= 1 + b)
monotoneSucc _ = believe_me (Refl {x = True})

export
0
monotonePred : {a,b : Integer} -> (|-      a >=      b) 
                                   -------------------
                               -> (|- -1 + a >= -1 + b)
monotonePred _ = believe_me (Refl {x = False})

export
0
atomicity0 : {a : Integer} -> (|- a >= 0) -> (~| a >= 1)
                               -------------------------
                           -> a = 0
atomicity0 pf1 pf2 = believe_me (Refl {x = 0})

export
0
monotoneSuccFalse : {a,b : Integer} -> (~|     a >=     b) 
                                        -----------------
                                    -> (~| 1 + a >= 1 + b)
monotoneSuccFalse {a} {b} prf1 = case @@(1 + a >= 1 + b) of
  (True  ** prf2)  => let 0 lemma : (x : Integer) -> -1 + (1 + x) = x
                          lemma x = Frexify frexIntegerPlus [x] $ 
                                      sta (-1) :+: (sta 1 :+: var 0) =-= var 0
                          0 prf3 : |- a >= b
                          prf3 = rewrite sym $ lemma a in rewrite sym $ lemma b in
                                 monotonePred prf2
                      in absurdity prf3 prf1
  (False ** prf2)  => prf2

export
0
monotonePredFalse : {a,b : Integer} -> (~|      a >=      b) 
                                        -----------------
                                    -> (~| -1 + a >= -1 + b)
monotonePredFalse {a} {b} prf1 = case @@(-1 + a >= -1 + b) of
  (True  ** prf2)  => let 0 lemma : (x : Integer) -> 1 + (-1 + x) = x
                          lemma x = Frexify frexIntegerPlus [x] $ 
                                      sta 1 :+: (sta (-1) :+: var 0) =-= var 0
                          0 prf3 : |- a >= b
                          prf3 = rewrite sym $ lemma a in rewrite sym $ lemma b in
                                 monotoneSucc prf2
                      in absurdity prf3 prf1
  (False ** prf2)  => prf2


export
0
plusLeftCancel : (left, a,b : Integer) -> left + a = left + b -> a = b
plusLeftCancel left a b prf = 
  let 0 lemma : (x : Integer) -> -left + (left + x) = x
      lemma x = Calc $
                |~ -left + (left + x)
                ~~ (-left + left) + x ...(plusAssociative (-left) left x) -- or frexify
                ~~ 0 + x              ...(cong (+x) $ minusPlusInverse left)
                ~~ x                  ...(plusZeroLeftNeutral x)
  in Calc $ 
  |~ a
  ~~ -left + (left + a) ...(sym $ lemma a)
  ~~ -left + (left + b) ...(cong (-left +) prf)
  ~~ b  ...(lemma b)
  
export
0
plusRightCancel : (a, b, right : Integer) -> a + right = b + right -> a = b
plusRightCancel a b right prf = plusLeftCancel right a b $ Calc $ 
                                                        |~ right + a 
                                                        ~~ a + right ...(plusCommutative right a)
                                                        ~~ b + right ...(prf)
                                                        ~~ right + b ...(plusCommutative b right)

export
0
atomicity : {a,b : Integer} -> (|- a >= b) -> (~| a >= 1 + b) -> a = b
atomicity  {a} {b} prf prf1 with (integerRec b)
 atomicity {a = a} {b =  0} prf prf1 | IntegerZ = atomicity0 prf prf1
 atomicity {a = a} {b =  b} prf prf1 | IntegerSucc view =  
                                         plusLeftCancel (-1) a b $
                                         atomicity {a = -1 + a} {b = -1 + b} 
                                              (monotonePred prf ) 
                                              (replace {p = \u => ~| -1 + a >= u}
                                                       (Frexify frexIntegerPlus [b] $
                                                        sta (-1) :+: (sta ( 1) :+: var 0) =-=
                                                        sta   1  :+: (sta (-1) :+: var 0))
                                              $ monotonePredFalse prf1) | view
   
 atomicity {a = a} {b = -b} prf prf1 | IntegerPred view = 
                                         plusLeftCancel 1 a (-b) $
                                         atomicity {a = 1 + a} {b = 1 + (-b)}
                                              (monotoneSucc prf)
                                              -- we got lucky
                                              (monotoneSuccFalse prf1) | view

export
0
plusCongruenceLeft : (left : Integer) -> {a,b : Integer} 
                   -> (|-        a >=        b) 
                     -------------------------
                   -> (|- left + a >= left + b)
plusCongruenceLeft    left  {a} {b} aGTb with (integerRec left) 
 plusCongruenceLeft      0  {a} {b} aGTb | IntegerZ = rewrite plusZeroLeftNeutral a in
                                                      rewrite plusZeroLeftNeutral b in aGTb
 plusCongruenceLeft   left  {a} {b} aGTb | IntegerSucc view = 
   rewrite sym $ lemma a in
   rewrite sym $ lemma b in
   step2
   where
     0 step1 : |- (-1 + left) + a >= (-1 + left) + b
     step1 = plusCongruenceLeft (-1 + left) aGTb
     0 step2 : |- 1 + ((-1 + left) + a) >= 1 + ((-1 + left) + b)
     step2 = monotoneSucc step1
     0 lemma : (x : Integer) -> 1 + ((-1 + left) + x) = left + x
     lemma x = Frexify frexIntegerPlus [left, x] $ sta 1 :+: ((sta (-1) :+: var 0) :+: var 1) 
                                                   =-= var 0 :+: var 1
 plusCongruenceLeft (-left) {a} {b} aGTb | IntegerPred view = 
   rewrite sym $ lemma a in
   rewrite sym $ lemma b in
   step2
   where
     0 step1 : |- (1 + -left) + a >= (1 + -left) + b
     step1 = plusCongruenceLeft (1 + -left) aGTb
     0 step2 : |- -1 + ((1 + -left) + a) >= -1 + ((1 + -left) + b)
     step2 = monotonePred step1
     0 lemma : (x : Integer) -> -1 + ((1 + -left) + x) = -left + x
     lemma x = Frexify frexIntegerPlus [-left, x] $ sta (-1) :+: ((sta 1 :+: var 0) :+: var 1)
                                                  =-= var 0 :+: var 1
     
export
0
reflexivity : (a : Integer) -> |- a >= a
reflexivity a = rewrite sym $ plusZeroRightNeutral a in 
                step2
  where
    0 step1 : |- 0 >= 0
    step1 = Refl
    0 step2 : |- a + 0 >= a + 0
    step2 = plusCongruenceLeft a step1

export
antitoneNeg : (|- a >= b) -> (|- -b >= -a)


export
integerLeq : Equivalence
integerLeq = MkEquivalence Integer (\x,y => |- x >= y) ?hole1 ?hole2


public export
0
antisymmetry : {a, b : Integer} -> (|- a >= b) -> (|- b >= a) 
                                   --------------------------
                                ->      a = b

mutual 
  public export
  0
  compareIntegerTrue : {a : Integer} -> (a >= 0) = True -> (n : Nat ** a = cast n)
  {-
  compareIntegerTrue  {a} prf with (integerRec a) 
   compareIntegerTrue {a =  0} prf | IntegerZ = (0 ** Refl)
   compareIntegerTrue {a =  a} prf | IntegerSucc view = case @@((-1 + a) >= 0) of
     (True  ** pf)  => let (n ** pf2) = (compareIntegerTrue pf | view) in (1 + n ** Calc $
       |~ a
       ~~ 1 + (-1 + a) ...(Frexify frexIntegerPlus [a] $ var 0 =-= 
                                 sta 1 :+: (sta (-1) :+: var 0))
       ~~ 1 + cast n ...(cong (1+) pf2))
     (False ** pf)  => ?compareIntegerTrue_rhs_2
   compareIntegerTrue {a = -a} prf | IntegerPred view = ?compareIntegerTrue_rhs_
   -}
  public export
  0
  compreIntegerFalse : {a : Integer} -> (a >= 0) = True -> (n : Nat ** (IsSucc n, a = - cast n))

data IntegerLine : Integer -> Type where
  NonNeg : (0 n : Nat)                                -> {auto 0 ford : a =   cast n} -> IntegerLine a
  Neg    : (0 n : Nat) -> {auto 0 itIsSuc : IsSucc n} -> {auto 0 ford : a = - cast n} -> IntegerLine a
  
partial
integerView : (a : Integer) -> IntegerLine a
integerView   a   with (integerRec a)
 integerView  0   | IntegerZ = NonNeg 0
 integerView  a   | IntegerSucc view with (integerView (-1 + a) | view)
  integerView a   | IntegerSucc view | NonNeg n {ford = aIsn}  =  
           -- Would be much nicer if we could match on Refl and replace a with cast n?
                                       NonNeg (1 + n) {ford = 
          rewrite sym aIsn in  
          Frexify frexIntegerPlus [a] $ var 0 =-= sta 1 :+: (sta (-1) :+: var 0)}
  integerView a   | IntegerSucc view |    Neg n   = ?integerView_rhs_3
 integerView (-a) | IntegerPred view = ?integerView_rhs_

record RemainderMod (n : Nat) {auto 0 itIsSucc :  IsSucc n} where
  constructor WithRemainder
  quotient : Integer
  remainder : Nat
  0 remainderPositive : 0 <<= remainder
  0 remainderIsModulo : remainder << n

Divide : (a : Integer) -> (n : Nat) -> {auto 0 itIsSucc : IsSucc n} -> RemainderMod n {itIsSucc=itIsSucc}
--Divide  a (S n) {itIsSucc = _} with (integerRec a)
 --Divide a (S n) {itIsSucc = _} | foo = ?hole

-}

{-

%hide mod
%hide modNat

-- can't use stdlib `modNat` or `modNatNZ` as they're partial
modMinus : (a, predN : Nat) -> Nat
modMinus  0     predN = predN
modMinus  (S a) predN with (modMinus a predN)
 modMinus (S a) predN | 0    = predN
 modMinus (S a) predN | S r' = r'

modNat : (a, predN : Nat) -> Nat
modNat  0     predN = 0
modNat  (S a) predN with (modNat a predN, modMinus a predN)
  modNat (S a) predN | (_, 0) = 0
  modNat (S a) predN | (r, _) = S r

div : (a, predN : Nat) -> Nat
div  0     predN = 0
div  (S a) predN with (Modular.div a predN, modMinus a predN)
 div (S a) predN | (d, 0) = S d
 div (S a) predN | (d, _) = d

0
remainderInvariant : (a, predN : Nat) ->
  1 + (a `modNat` predN) + (a `modMinus` predN) = S predN
remainderInvariant  0     predN = Refl
remainderInvariant  (S a) predN with (@@ modMinus a predN)
 remainderInvariant (S a) predN | (0 ** prf) = rewrite prf in 
                                               rewrite sym $ remainderInvariant a predN in Refl
 remainderInvariant (S a) predN | (S r' ** prf)
            = rewrite prf in Calc $ 
            |~ 1 + ((1 + (a `modNat` predN) + r'))
            ~~ 1 + ((a `modNat` predN) + (1 + r'))
                 ...(Frexify (frexNat _) [a `modNat` predN, r']
                     let r  = var 0
                         r' = var 1 in
                     sta 1 :+: ((sta 1 :+: r) :+: r') =-=
                     sta 1 :+: (r :+: (sta 1 :+: r')))
            ~~ S predN ...(let u = remainderInvariant a predN in rewrite sym prf in u)
0
remainderSpec : (a, predN : Nat) ->
  (a `modNat` predN) + (a `div` predN) * (S predN) = a
remainderSpec  0     predN = Refl
remainderSpec  (S a) predN with (@@ modMinus a predN)
 remainderSpec (S a) predN | (0    ** prf) = 
   let v = succInjective _ _ $ remainderInvariant a predN 
       u = remainderSpec a predN 
       w = Calc $
           |~ (a `modNat` predN)
           ~~ (a `modNat` predN) + 0                     ...(sym $ plusZeroRightNeutral _)
           ~~ (a `modNat` predN) + (a `modMinus` predN)  ...(cong (a `modNat` predN +) $
                                                                  sym prf)
           ~~ predN                                   ...(v)
   in
   rewrite prf in cong S $ Calc $
   |~ predN + (a `Modular.div` predN) * (1 + predN)
   ~~ (a `modNat` predN) + (a `Modular.div` predN) * (1 + predN) 
                                    ...(cong (+ (a `Modular.div` predN) * (1 + predN)) $ sym w)
   ~~ a                             ...(u)
 remainderSpec (S a) predN | (S r' ** prf) = 
   rewrite prf in cong S (remainderSpec a predN)

0
modIdentity : (a, k : Nat) -> a `modNat` (a + k) = a
modIdentity  0     k = Refl
modIdentity  (S a) k with (@@ modMinus a (S (a + k)))
 modIdentity (S a) k | (0 ** prf) = rewrite prf in 
   -- This case is an absurdity
   let 0 u = Calc $
           |~ (a `modNat` (1 + (a + k))) 
           ~~ (a `modNat` (a + (1 + k))) ...(cong (modNat a)       $
                                                Frexify (frexNat _) [a, k] $
                                                  (sta 1 :+: (var 0 :+: var 1)) =-=
                                                   var 0 :+: (sta 1 :+: var 1))
           ~~ a                             ...(modIdentity a (S k)) 
       0 w = Calc $
           |~ a
           ~~ a + 0     ...(sym $ plusZeroRightNeutral a)
           ~~ (a `modNat` (S $ a + k)) + (a `modMinus` (S $ a + k)) 
                        ...(cong2 (+) (sym u) 
                                      (sym prf))
           ~~ S (a + k) ...(succInjective _ _ $ remainderInvariant a (S $ a + k)) 
   in absurd $ contradiction _ _ w
   where
     contradiction : (a, b : Nat) -> (0 _ : a = S (a + b)) -> Void
     contradiction 0     b Refl impossible
     contradiction (S a) b pf = contradiction a b $ succInjective _ _ pf

 modIdentity (S a) k | (S r' ** prf) = rewrite prf in
   Calc $
   |~ 1 + (a `modNat` (1 + (a + k)))
   ~~ 1 + (a `modNat` (a + (1 + k))) ...((cong (\u => 1 + (a `modNat` u)) $
                                                Frexify (frexNat _) [a, k] $
                                                  (sta 1 :+: (var 0 :+: var 1)) =-=
                                                   var 0 :+: (sta 1 :+: var 1)))
   ~~ 1 + a ...(cong (1+) $ modIdentity a (1 + k))

0
modMinusZero : (predN : Nat) -> predN `modMinus` predN = 0
modMinusZero predN = plusLeftCancel _ _ _ $ Calc $
  |~ predN + (predN `modMinus` predN)
  ~~ (predN `modNat` (predN + 0)) + (predN `modMinus` predN) 
               ...(cong (+ (predN `modMinus` predN))
                        $ sym $ modIdentity _ _)
  ~~ (predN `modNat` predN) + (predN `modMinus` predN) 
               ...(cong (\u => (predN `modNat` u)
                             + (predN `modMinus` predN))
                   $ plusZeroRightNeutral _)
  ~~ predN     ...(succInjective _ _ $ remainderInvariant _ _)
  ~~ predN + 0 ...(sym $ plusZeroRightNeutral _)

0
mod1Translate : (predN : Nat) -> (S predN) `modNat` predN = 0
mod1Translate  predN with (@@ (predN `modMinus` predN))
 mod1Translate predN | (0   ** prf) = rewrite prf in Refl
 mod1Translate predN | (S k ** prf) = rewrite prf in 
                                      absurd $ SIsNotZ $ Calc $
                                      |~ S k 
                                      ~~ (predN `modMinus` predN) ...(sym prf)
                                      ~~ 0 ...(modMinusZero predN)

0
modTranslate : (predN, a, b : Nat) -> (a + b*(S predN)) `modNat` predN = a `modNat` predN
modTranslate predN a 0     = rewrite plusZeroRightNeutral a in Refl
modTranslate predN a (S b) = 
  let n : Nat
      n = S predN in
  Calc $
  |~ ((a + (n + b*n)) `modNat` predN)
  ~~ (((a + n) + b*n) `modNat` predN) ...(cong (`modNat` predN)
                                                  $ plusAssociative a n (b*n))
  --~~ (a + n) `modNat` 
  ~~ (a `modNat` predN) ...(?just)

 --}
   



{-
public export
mod2 : Nat -> Nat
mod2 0 = 0
mod2 1 = 1
mod2 (S $ S k) = mod2 k

export
modClosure : (n : Nat) -> {auto 0 itIsSucc : IsSucc n} ->
  (a : Nat) -> a `mod` n = (a `mod` n) `mod` n
modClosure n@(S fuel) {  itIsSucc = _} 0 = ?modClosure_rhs_1
modClosure n@(S fuel) {  itIsSucc = _} (S k) = ?modClosure_rhs_

export
mod2Closure : (a : Nat) -> mod2 (a) = mod2 (mod2 a)
mod2Closure 0 = Refl
mod2Closure 1 = Refl
mod2Closure (S $ S k) = mod2Closure k

export
mod2S : (a : Nat) -> mod2 (S a) = mod2 (S (mod2 a))
mod2S 0 = Refl
mod2S 1 = Refl
mod2S (S $ S k) = mod2S k

export
mod2HomPlus : (a,b : Nat) -> mod2 (a + b) = mod2(mod2 a + mod2 b)
mod2HomPlus 0 b = mod2Closure b
mod2HomPlus 1 b = mod2S b
mod2HomPlus (S $ S k) b = mod2HomPlus k b

export
0 mod2Foo : (a, k : Nat) -> mod2 (2*k + a) = mod2 a
mod2Foo a 0 = Refl
mod2Foo a 1 = Refl
mod2Foo a (S $ S k) = Calc $
  |~ mod2 ((k + (2 + (k + 0))) + a)
  ~~ mod2 (2 + (2*k + a))
     ...(let u = Frexify (frexNat _) [k, a] $ 
              (var 0 :+: (sta 2 :+: (var 0 :+: sta 0))) :+: var 1
               =-= sta 2 :+: ((var 0 :+: (var 0 :+: sta 0)) :+: var 1)
             v = cong mod2 u in v) 
             -- Not sure why the substitution `cong mod2 $ Frexify ...` fails
  ~~ mod2 (2*k + a) ...(Refl)
  ~~ mod2 a ...(mod2Foo a k)


-}
-- hmm... surely this isn't as difficult as this/
