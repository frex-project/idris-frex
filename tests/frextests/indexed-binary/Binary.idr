||| Binary arithmetic indexed by their corresponding Nat Based on
||| "Constructing Correct Circuits: Verification of Functional Aspects
||| of Hardware Specifications with Dependent Types", by Edwin
||| C. Brady, James McKinna, Kevin Hammond, TFP2007.
module Binary

import Data.Fin

import Data.Nat
import Data.Nat.Division
import Data.Nat.Order
import Data.Nat.Order.Properties
import Data.Nat.Properties

import Data.Vect
import Data.Vect.Elem

import Frex
import Frex.Free

import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Nat

import Syntax.PreorderReasoning

import VectReasoning

NZ2 : NonZero 2
NZ2 = SIsNonZero

export
absurdSucIsZero : (k : Nat) -> (0 prf : S k = 0) -> b
absurdSucIsZero k _ impossible


public export
mod2 : Nat -> Nat
mod2 a = modNatNZ a 2 NZ2

public export
div2 : Nat -> Nat
div2 a = divNatNZ a 2 NZ2

export
keep : (0 prf : x ~=~ y) -> x ~=~ y
keep Refl = Refl

-- -- Some artihmetic facts

export
nonNegativeAddition : (b, c : Nat) -> b + c = 0 -> b = 0
nonNegativeAddition 0 c prf = Refl

export
multSucRightCancel : (a, b : Nat) -> (minusOne : Nat) -> a * (S minusOne) = b * (S minusOne) -> a = b
multSucRightCancel 0     b minusOne prf = sym $ nonNegativeAddition b (b * minusOne) $
  Calc $ 
  |~ b + (b * minusOne)
  ~~ (1 * b) + (b * minusOne) ...(Frex.solve 2 (Frex Nat.Additive) $
                                  Dyn 0 .+. Dyn 1 =-= (the Nat 1 *. Dyn 0) .+. Dyn 1)
  ~~ (b * 1) + (b * minusOne) ...(cong (+ b*minusOne) $ multCommutative 1 b)
  ~~ b * (1 + minusOne)       ...(sym $ multDistributesOverPlusRight _ _ _)
  ~~ 0                        ...(sym prf)
multSucRightCancel (S a) 0 minusOne prf = absurdSucIsZero _ prf
multSucRightCancel (S a) (S b) minusOne prf = cong S $ multSucRightCancel a b minusOne 
                                                     $ plusLeftCancel (1 + minusOne) _ _ prf


export
multSucLeftCancel : (a, b : Nat) -> (minusOne : Nat) -> (S minusOne) * a = (S minusOne) * b -> a = b
multSucLeftCancel a b minusOne prf = multSucRightCancel a b minusOne $ Calc $ 
  |~ a * (S minusOne)
  ~~ (S minusOne) * a ...(multCommutative _ _)
  ~~ (S minusOne) * b ...(prf)
  ~~ b * (S minusOne) ...(multCommutative _ _)

powerNZ : (n : Nat) -> NonZero (2 `power` n)
powerNZ   0 = SIsNonZero
powerNZ   (S n) with (powerNZ n)
 powerNZ  (S n) | prf with (2 `power` n)
  powerNZ (S n) | SIsNonZero | S _ = SIsNonZero

modAffine : (a, k, n : Nat) -> (nz : NonZero n) 
         -> modNatNZ (n*k + a) n nz 
          = modNatNZ        a  n nz
modAffine a k n nz = 
  -- We'll use the division theorem.
  let 0 r : Nat
      r = modNatNZ a n nz
      0 r_lt_n : r `LT` n
      r_lt_n = boundModNatNZ a n nz
      0 q : Nat
      q = divNatNZ a n nz
      0 mod_a_decomposition : a = r + (q * n)
      mod_a_decomposition = DivisionTheorem a n nz nz
      0 q' : Nat
      q' = k + q
      0 mod_a_translated_decomposition : (n*k + a) = (q' * n) + r
      mod_a_translated_decomposition = Calc $
        |~ n*k + a
        ~~ n*k + (r + (q*n)) ...(cong (n*k+) mod_a_decomposition)
        ~~ (n*k + q*n) + r   ...(Frex.solve 3 (Frex Nat.Additive) $
                                 Dyn 0 :+: (Dyn 2 :+: (Dyn 1))
                                 =-=
                                 (Dyn 0 :+: Dyn 1) :+: (Dyn 2)
                                 )
        ~~ (k*n + q*n) + r   ...(cong (\u => (u + q*n) + r)
                                 $ multCommutative n k)
        ~~ q' * n + r        ...(cong (+r) $ sym $ 
                                 multDistributesOverPlusLeft k q n)
      0 conclusion : modNatNZ (n*k + a) n nz = r
      conclusion = let (div_uniqueness,mod_uniqueness) =
                         DivisionTheoremUniqueness (n*k + a) n nz
                         -- decomposition
                         q' r r_lt_n
                         mod_a_translated_decomposition
                   in mod_uniqueness
  in keep conclusion
          
mod2Affine : (a, k : Nat) -> mod2 (2*k + a) = mod2 a
mod2Affine a k = modAffine a k 2 NZ2

public export
data Bit : Nat -> Type where
  O : Bit 0
  I : Bit 1
  
export
bitModulo : Bit b -> mod2 b = b
bitModulo O = Refl
bitModulo I = Refl

  
data BitPair : Nat -> Type where
  MkBitPair : Bit b -> Bit c -> {auto 0 ford : d = b + b + c} ->  BitPair d
                           -- Hopefully we could simplify once we have a semiring frexlet
                           
namespace Binary.Naive
  ||| Carry-bit-addition as a truth table
  ||| Defo demo with case splitting, can try demo-ing with proof search
  addBit : Bit c -> Bit x -> Bit y -> BitPair (c + x + y)                           
  addBit O O O = MkBitPair O O
  addBit O O I = MkBitPair O I
  addBit O I O = MkBitPair O I
  addBit O I I = MkBitPair I O
  addBit I O O = MkBitPair O I
  addBit I O I = MkBitPair I O
  addBit I I O = MkBitPair I O
  addBit I I I = MkBitPair I I


and : Nat -> Nat -> Nat
and (S n) (S k) = 1
and 0 y = 0
and x 0 = 0

public export
or : Nat -> Nat -> Nat
or (S n) k = 1
or 0    (S k) = 1
or 0     0 = 0
  
public export
xor : Nat -> Nat -> Nat
xor (S n) (S k) = 0
xor 0     (S k) = 1
xor (S n) 0     = 1
xor 0     0     = 0
  
andGate : Bit x -> Bit y -> Bit (x `and` y)
andGate I I = I
andGate O y = O
andGate I O = O 

orGate : Bit x -> Bit y -> Bit (x `or` y)
orGate O O = O
orGate O I = I
orGate I y = I

xorGate : Bit x -> Bit y -> Bit (x `xor` y)
xorGate O O = O
xorGate O I = I
xorGate I O = I
xorGate I I = O

-- ----- a detour, teaching the type-check to brute-force binary arithmetic
-- -- Weird --- type cumulativity?
mapVect : (f : a -> b) -> Vect n a -> Vect n b
mapVect = map

Tabulate : {n : Nat} -> {F : Fin n -> Type}
           -> (f : (i : Fin n) -> F i)
           -> HVect (mapVect F (range {len = n}))
Tabulate {n = 0} f = []
Tabulate {n = S k} f = 
  let u = Tabulate {n = k} {F = F . FS } (\i => f (FS i)) in
  let eq : ((mapVect (F . FS) $ Data.Vect.Fin.tabulate Prelude.Basics.id {len = k}) ~=~ (mapVect F (Data.Vect.Fin.tabulate FS {len = k})))
      eq = let y = sym (Data.Vect.Properties.Map.mapTabulate FS id)
           in trans (sym (mapFusion F FS (tabulate id))) (cong (mapVect F) y) in
     f FZ :: replace {p = HVect} eq u 
      
ElemMap : (f : a -> b) -> x `Elem` xs -> f x `Elem` (mapVect f xs)
ElemMap f  Here         = Here
ElemMap f (There later) = There $ ElemMap f later

ElemInLft : x `Elem` xs -> x `Elem` (xs ++ ys)
ElemInLft  Here         = Here
ElemInLft (There later) = There (ElemInLft later)

ElemInRgt : {ys : Vect len a } -> x `Elem` xs -> x `Elem` (ys ++ xs)
ElemInRgt {ys = []} ptr = ptr
ElemInRgt {ys = (y :: ys)} ptr = There $ ElemInRgt ptr

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

TruthTableCovers : {n : Nat} -> (env : Vect n (b : Nat ** Bit b)) -> map DPair.fst env `Elem` (TruthTableRows n)
TruthTableCovers [] = Here
TruthTableCovers {n = S n} ((MkDPair 0 O) :: xs) = 
  let v0 : {n:Nat} -> (2 `power` n) + (0 * (2 `power` n)) = (2 `power` n)
      v0 =  Frex.solve 1 (Frex Nat.Additive) $ (Dyn 0 :+: Sta 0 =-= Dyn 0) in
  let result = ElemInLft {ys = map (1 ::) $ TruthTableRows n} $ ElemMap (0 ::) (TruthTableCovers xs) in
  rewrite v0 {n} in
  result

TruthTableCovers {n = S n} ((MkDPair 1 I) :: xs) = 
  let v0 : {n:Nat} -> (2 `power` n) + (0 * (2 `power` n)) = (2 `power` n)
      v0 =  Frex.solve 1 (Frex Nat.Additive) $ (Dyn 0 :+: Sta 0 =-= Dyn 0) in
  let result = ElemInRgt {ys = map (0 ::) $ TruthTableRows n} $ ElemMap (1 ::) (TruthTableCovers xs) in
  rewrite v0 {n} in
  result
  

bruteForce : {n : Nat} -> (fg : Vect n Nat -> (Nat, Nat)) 
          -> {auto prf : HVect $ tabulate (\i => fst (fg (index i $ TruthTableRows n)) = 
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

-- Not true for general c,x,y (e.g., for (0, 0, S k) we get (S k = 1)
-- but true if we case split on l, r, and cIn
-- Tell Edwin there's a (tiny) mistake in the paper, maybe he already knows
0 addBit_Ford : (cIn : Bit c) -> (l : Bit x) -> (r : Bit y) -> 
  (c + x) + y =
  ((((x `and` y) `or` (y `and` c)) `or` (c `and` x))
  +(((x `and` y) `or` (y `and` c)) `or` (c `and` x)))
  + ((x `xor` y) `xor` c)
addBit_Ford cIn l r = 
  bruteForce (\ [c,x,y] => ((c + x) + y
                            , ((((x `and` y) `or` (y `and` c)) `or` (c `and` x))
                               +(((x `and` y) `or` (y `and` c)) `or` (c `and` x)))
                               + ((x `xor` y) `xor` c)
                              ))
                     [(_ ** cIn), (_ ** l), (_ ** r)]

addBit : Bit c -> Bit x -> Bit y -> BitPair (c + x + y)
addBit cIn l r = 
       let cOut = orGate (orGate (andGate l r)
                                 (andGate r cIn))
                         (andGate cIn l)
           s = xorGate (xorGate l r) cIn
       in MkBitPair cOut s
          {ford = bruteForce (\case [c, x, y] => ((c + x) + y
                                      , ((((x `and` y) `or` (y `and` c)) `or` (c `and` x))
                                         +(((x `and` y) `or` (y `and` c)) `or` (c `and` x)))
                                         + ((x `xor` y) `xor` c)
                                      )
          ) [(_ ** cIn), (_ ** l), (_ ** r)]}

-- -- Until we get a semiring frexlet, `little-endian` bits are probably going to be easier
-- -- The downside is that we will diverge from the paper

namespace Binary.BE
  public export
  data Number : Nat -> Nat -> Type where
    Nil : Number 0 0
    (::) : Bit b -> Number width val 
           -> {auto 0 valueFord : val'   = ((2 `power` width)*b + val)}
           -> Number (1 + width) val'

namespace Binary.LE
  public export
  data Number : Nat -> Nat -> Type where
    Nil  : Number 0 0
    (::) : Bit b -> LE.Number width val 
           -> {auto 0 valueFord : val'   = b + val + val}
           -> Number (1 + width) val'


-- -- Smart constructors, flipping the indexing methods
LENil : BE.Number 0 0
LENil = []

rightNeut : (p : Nat) -> p + 0 = p
rightNeut p = Frex.solve 1 (Frex Nat.Additive) $ Dyn 0 :+: Sta 0 =-= Dyn 0

LECons : Bit b -> BE.Number width val -> BE.Number (1 + width) (b + val + val)
LECons bit [] = [bit] 
LECons {b} bit ((::) {b = b'} {width} {val} bit' bits {valueFord = Refl}) =
   let r : {b, p, q, b', v : Nat} -> (b + (p * b' + v)) + (q * b' + v) = (p * b' + q * b') + ((b + v) + v) 
       r = Frex.solve 4 (Frex Nat.Additive) $
            (Dyn 0 :+: (Dyn 1 :+: Dyn 2)) :+: (Dyn 3 :+: Dyn 2) =-= (Dyn 1 :+: Dyn 3) :+: ((Dyn 0 :+: Dyn 2) :+: Dyn 2)
    in
  (::) bit' (LECons bit bits) { valueFord = rewrite rightNeut (power 2 width) in
                                            rewrite multDistributesOverPlusLeft (power 2 width) (power 2 width) b' in
                                            r {b,p=power 2 width,q=power 2 width,b',v=val} }

LEtoBE : LE.Number w val -> BE.Number w val
LEtoBE [] = LENil
LEtoBE ((::) x xs {valueFord = Refl})  = x `LECons` (LEtoBE xs)

BENil : LE.Number 0 0
BENil = []

BECons : Bit b -> LE.Number width val -> LE.Number (1 + width) ((2 `power` width) * b + val)
BECons bit [] = [bit]
BECons {b} bit ((::) {b = b'} {width} {val} bit' bits {valueFord = Refl}) =
  let r : {p, q, b, b', v : Nat} -> ((p + q) * b) + ((b' + v) + v) = (b' + ((p * b) + v)) + ((q * b) + v)
      r {p, q, b, b', v} = rewrite multDistributesOverPlusLeft p q b in
                           Frex.solve 4 (Frex Nat.Additive)
                           $ ((Dyn 0 :+: Dyn 1)) :+: ((Dyn 2 :+: Dyn 3) :+: Dyn 3)
                              =-= (Dyn 2 :+: (Dyn 0 :+: Dyn 3)) :+: (Dyn 1 :+: Dyn 3)
   in
   (::) bit' (BECons bit bits) { valueFord = rewrite rightNeut (power 2 width) in r }

BEtoLE : BE.Number w val -> LE.Number w val
BEtoLE [] = BENil
BEtoLE ((::) bit bits {valueFord = Refl}) = bit `BECons` (BEtoLE bits)

namespace Binary.LE
  public export
  data NumCarry : Nat -> Nat -> Type where
    Carrying : (num : LE.Number width val) -> (carry : Bit c) 
             -> {auto 0 valueFord : val' = val + (2 `power` width) * c}
             -> NumCarry width val'
  public export
  0 numVal : NumCarry width val -> Nat
  numVal (Carrying {val} _ _) = val
  
  public export
  0 carryVal : NumCarry width val -> Nat
  carryVal (Carrying {c} _ _) = c
    
  public export
  num : (nc : NumCarry width val) -> LE.Number width (numVal nc)
  num (n `Carrying` _) = n
  
  public export
  carry : (nc : NumCarry width val) -> Bit (carryVal nc)
  carry (_ `Carrying` bit) = bit

bitUnique : (x : Bit c_x) -> (y : Bit c_y) -> c_x = c_y -> x = y
bitUnique O O Refl = Refl
bitUnique I I Refl = Refl

public export
(*:) : Nat -> Term Theory.Signature (Either a (Fin n)) -> Term Theory.Signature (Either a (Fin n))
(*:) 0 x = O2 
(*:) (S k) x = x :+: (k *: x)

uip : (eq1, eq2 : x ~=~ y) -> eq1 = eq2
uip Refl Refl = Refl

bitBound : (x : Bit b) -> b `LT` 2
bitBound O =           LTESucc LTEZero
bitBound I = LTESucc $ LTESucc LTEZero

0
bitsBound : (x : LE.Number width val) -> val `LT` (2 `power` width)
bitsBound [] = LTESucc LTEZero 
bitsBound {width = S width} ((::) {b} {val} {val' = _} bit bits {valueFord = Refl}) = 
  CalcWith  $
  |~ 1 + ((b + val) + val)
  ~~ (1 + b) + (2*val)       ...(Frex.solve 2 (Frex Nat.Additive) $
                                 Sta 1 :+: ((Dyn 0 :+: Dyn 1) :+: Dyn 1)
                                 =-=
                                 (Sta 1 :+: Dyn 0) :+: (2 *: Dyn 1))
  <~ 2 + (2*val)             ...(plusLteMonotoneRight (2*val) (1 + b) 2 $ bitBound bit)
  ~~ 2*(1 + val)             ...(sym $ multDistributesOverPlusRight 2 1 val)
  <~ (2 `power` (1 + width)) ...(multLteMonotoneRight 2 (1 + val) (2 `power` width)
                                $ bitsBound bits)


0 
numberUnique : (x : LE.Number width val_x)
            -> (y : LE.Number width val_y)
            -> val_x = val_y
            -> x = y
numberUnique [] [] _ = Refl
numberUnique {width = S width}      -- coverage checker wants to replace `_` here vvvvvvvv instead of `Refl`  --- bug?
  ((::) {width = _} {b = b_x} {val = val_x} {val' = val'} bit_x bits_x {valueFord = valford_x})
  ((::) {width = _} {b = b_y} {val = val_y} {val' = _   } bit_y bits_y {valueFord = valford_y}) 
  Refl with (let 0 lemma : (a,b : Nat) -> (2*b + a = (a + b) + b)
                 lemma a b = Frex.solve 2 (Frex Nat.Additive) $
                           (Dyn 1 :+: (Dyn 1 :+: Sta 0)) :+: Dyn 0 -- (2 *: (Dyn 0)) :+: (Dyn 1)
                                 =-=
                           (Dyn 0 :+: Dyn 1) :+: Dyn 1 in
           let 
               0 w = Calc $                        
                  |~ b_x 
                  ~~ mod2 b_x ...(sym $ bitModulo (bit_x))
                  ~~ mod2 (2*val_x + b_x) ...(sym $ mod2Affine b_x val_x)
                  ~~ mod2 ((b_x + val_x) + val_x)
                     ...(cong mod2 $ lemma b_x val_x) -- frexify!
                  ~~ mod2 val' ...(cong mod2 $ sym valford_x)
                  -- similarly, go backwards. TODO: refactor these steps into a lemma
                  ~~ mod2 ((b_y + val_y) + val_y)
                          ...(cong mod2 valford_y)
                  ~~ mod2 (2*val_y + b_y)
                          ...(cong mod2 $ sym $ lemma b_y val_y) -- frexify!
                  ~~ mod2 b_y ...(mod2Affine b_y val_y)
                  ~~ b_y ...(bitModulo bit_y)
               0 u = bitUnique bit_x bit_y w
               0 v = Calc $ |~ 2*val_x + b_x
                            ~~ (b_x + val_x) + val_x ...(lemma b_x val_x) -- frexify!
                            ~~ val'                  ...(sym $ valford_x)
                            ~~ (b_y + val_y) + val_y ...(valford_y)
                            ~~ 2*val_y + b_y         ...(sym $ lemma b_y val_y) 
                            ~~ 2*val_y + b_x         ...(cong (2*val_y +) $ sym w)  
               0 z = plusRightCancel (2*val_x) (2*val_y) b_x v
               0 q = multSucLeftCancel val_x val_y 1 z
          in (w, u, q))
 numberUnique {width = S width}                  
  ((::) {width = _} {b} {val=val_x} {val'} bit bits_x {valueFord = valueFord_x})
  ((::) {width = _} {b = b} {val = val_y} {val' = val'} _ bits_y {valueFord = valueFord_y}) 
  Refl | (Refl, Refl, q) with (numberUnique bits_x bits_y q)
  numberUnique {width = S width}       
   ((::) {width = _} {b} {val} {val'} bit bits {valueFord = valueFord_x})
   ((::) {width = _} {b = b} {val = val} {val' = val'} _ _ {valueFord = valueFord_y}) 
   Refl | (Refl, Refl, Refl) | Refl = rewrite uip valueFord_x valueFord_y in Refl 

-- -- Comes later in the paper, but since type-checking `addNumber` takes
-- -- so long, it's quicker to have it here

%unbound_implicits off
partial 0
numCarryUnique : forall width, val . (x, y : NumCarry width val) -> x = y
numCarryUnique (Carrying {c = c_x} {val = val_x} {val'       } num_x carry_x {valueFord = valueFord_x}) 
               (Carrying {c = c_y} {val = val_y} {val' = val'} num_y carry_y {valueFord = valueFord_y}) 
  = let lemma : (a,b,c : Nat) -> (a * b + c = c + b*a)
        lemma a b c = Calc $ -- semiring frexlet would help here
            |~ a*b + c
            ~~ b*a + c ...(cong (+c) $ multCommutative a b)
            ~~ c + b*a ...(plusCommutative _ _)
        0 numer : Nat
        numer = c_x * (2 `power` width) + val_x 
        0 decomposition : (c_x * (2 `power` width) + val_x 
                         = c_y * (2 `power` width) + val_y)
        decomposition = 
          Calc $
          |~ c_x * (2 `power` width) + val_x 
          ~~ val_x + (2 `power` width) * c_x ...(      lemma c_x (2 `power` width) val_x)
          ~~ val'                            ...(sym $ valueFord_x)
          ~~ val_y + (2 `power` width) * c_y ...(      valueFord_y)
          ~~ c_y * (2 `power` width) + val_y ...(sym $ lemma c_y (2 `power` width) val_y)
        0 powern_neq_zero : NonZero (2 `power` width)
        powern_neq_zero = powerNZ width
        0 val_x_lt_2n : val_x `LT` (2 `power` width)
        val_x_lt_2n = bitsBound num_x
        0 val_y_lt_2n : val_y `LT` (2 `power` width)
        val_y_lt_2n = bitsBound num_y
    in let (div_eq_c_x, mod_eq_val_x) =
               DivisionTheoremUniqueness numer (2 `power` width) powern_neq_zero
               c_x val_x val_x_lt_2n
               Refl
           (div_eq_c_y, mod_eq_val_y) = 
               DivisionTheoremUniqueness numer (2 `power` width) powern_neq_zero
               c_y val_y val_y_lt_2n
               decomposition
    in let 0 val_x_eq_val_y : (val_x = val_y)
           val_x_eq_val_y = trans (sym mod_eq_val_x) mod_eq_val_y
           -- similarly:
           0 c_x_eq_c_y : (c_x = c_y)
           c_x_eq_c_y = trans (sym div_eq_c_x) div_eq_c_y
           0 num_x_eq_num_y : (num_x = num_y)
           num_x_eq_num_y = numberUnique num_x num_y val_x_eq_val_y
           0 carry_x_eq_carry_y : (carry_x = carry_y)
           carry_x_eq_carry_y = bitUnique carry_x carry_y c_x_eq_c_y
    in keep $ Calc $
      |~ Carrying {c = c_x} {val = val_x} num_x carry_x {valueFord = valueFord_x}
      ~~ Carrying {c = c_y} {val = val_y} num_y carry_y {valueFord = valueFord_y}
      ...(cong5 (\ c : Nat , val : Nat , num : LE.Number width val, carry : Bit c,
                   valueFord : (val' = val + (2 `power` width) * c) =>
                   num `Carrying` carry)
                c_x_eq_c_y
                val_x_eq_val_y
                num_x_eq_num_y
                carry_x_eq_carry_y
                (heterogenousUIP valueFord_x valueFord_y)
                )
      
    where
      heterogenousUIP : forall x,y,z . (eq1 : x ~=~ y) -> (eq2 : x ~=~ z) -> eq1 = eq2
      heterogenousUIP Refl Refl = Refl
    
      cong5 : {0 a1 : Type}       
        -> {0 a2 : a1 -> Type}
        -> {0 a3 : (x1 : a1) -> (x2 : a2 x1) -> Type}
        -> {0 a4 : (x1 : a1) -> (x2 : a2 x1) -> (x3 : a3 x1 x2) -> Type}
        -> {0 a5 : (x1 : a1) -> (x2 : a2 x1) -> (x3 : a3 x1 x2) -> (x4 : a4 x1 x2 x3) -> Type}
        -> {0 p : (z1 : a1) -> (z2 : a2 z1) -> (z3 : a3 z1 z2) -> (z4 : a4 z1 z2 z3) 
                 -> (z5 : a5 z1 z2 z3 z4) -> Type}
        -> (f : (z1 : a1) -> (z2 : a2 z1) -> (z3 : a3 z1 z2) -> (z4 : a4 z1 z2 z3) 
                 -> (z5 : a5 z1 z2 z3 z4) -> p z1 z2 z3 z4 z5)
        -> {x1,y1 : a1}                 -> x1 ~=~ y1
        -> {x2 : a2 x1} -> {y2 : a2 y1} -> x2 ~=~ y2
        -> {x3 : a3 x1 x2} -> {y3 : a3 y1 y2} -> x3 ~=~ y3
        -> {x4 : a4 x1 x2 x3} -> {y4 : a4 y1 y2 y3} -> x4 ~=~ y4
        -> {x5 : a5 x1 x2 x3 x4} -> {y5 : a5 y1 y2 y3 y4} -> x5 ~=~ y5
        -> f x1 x2 x3 x4 x5 ~=~ f y1 y2 y3 y4 y5
      cong5 _ Refl Refl Refl Refl Refl = Refl
%unbound_implicits on

export 0
numCarryUniqueForded : (x : NumCarry width val_x)
                    -> (y : NumCarry width val_y)
                    -> {auto 0 ford : (val_x = val_y)}
                    -> x = y
numCarryUniqueForded x y {ford = Refl} = numCarryUnique x y
                                                             
export
addNumber : LE.Number width x -> LE.Number width y -> Bit c -> NumCarry width (x + y + c)
addNumber []          []   carry = Carrying [] carry 
  {valueFord = Frex.solve 1 (Frex Nat.Additive) $ (Dyn 0 =-= Dyn 0 :+: Sta 0)} 
    -- could also discharge by permuting the terms in the second index of `NumCarry`

addNumber {c = c} {width = S width} 
          ((::) {b = b_a} {val = val_a} a aits {valueFord = Refl}) 
          ((::) {b = b_b} {val = val_b} b bits {valueFord = Refl}) 
          carry 
          with (addBit a b carry)
 addNumber
          {c = c} {width = S width} 
          ((::) {b = b_a} {val = val_a} a aits {valueFord = Refl}) 
          ((::) {b = b_b} {val = val_b} b bits {valueFord = Refl}) 
          carry 
          | MkBitPair {b = b_s} {c = c_s} 
             carry0 s {ford} with (addNumber aits bits carry0)
  addNumber 
          {c = c} {width = S width} 
          ((::) {b = b_a} {val = val_a} a aits {valueFord = Refl}) 
          ((::) {b = b_b} {val = val_b} b bits {valueFord = Refl}) 
          carry 
          | MkBitPair {b = b_s} {c = c_s} carry0 s {ford}
          | Carrying {val = val_s} {c = c0} sits carry1 {valueFord}  
            = Carrying ((::) s sits) 
                        carry1 
                        {valueFord = 
                          Calc $
                          |~ (((b_a + val_a) + val_a) + ((b_b + val_b) + val_b)) + c
                          -- rearrange terms so we can use `ford` on left summand
                          ~~ ((b_a + b_b) + c) + (val_a + val_a + val_b + val_b)
                               ...(Frex.solve 5 (Frex Nat.Additive) $
                                   let b_a   = Dyn 0
                                       b_b   = Dyn 1
                                       c     = Dyn 2
                                       val_a = Dyn 3
                                       val_b = Dyn 4
                                   in (((b_a :+: val_a) :+: val_a) :+: ((b_b :+: val_b) :+: val_b)) :+: c
                                    =-=((b_a :+: b_b) :+: c) :+: (((val_a :+: val_a) :+: val_b) :+: val_b)
                                  )
                          ~~ ((b_s + b_s) + c_s) + (val_a + val_a + val_b + val_b)
                               ...(cong (+ (val_a + val_a + val_b + val_b))
                                        ford)
                          -- rearrange terms again so we can use valueFord
                          ~~ c_s + 2*((val_a + val_b) + b_s)
                               ...(Frex.solve 4 (Frex Nat.Additive) $
                                   let b_s   = Dyn 0
                                       c_s   = Dyn 1
                                       val_a = Dyn 2
                                       val_b = Dyn 3
                                   in  ((b_s :+: b_s) :+: c_s) 
                                        :+: (((val_a :+: val_a) :+: val_b) :+: val_b)
                                   =-= c_s :+: (((val_a :+: val_b) :+: b_s) :+:
                                               (((val_a :+: val_b) :+: b_s) :+: Sta 0)))
                                                                   -- the `sta 0` comes from
                                                                   -- the definition of 2*x = x + (x + 0)
                          ~~ c_s + 2*(val_s + ((2 `power` width) * c0))
                               ...(cong (\u => c_s + 2*u) 
                                        valueFord)
                          -- rearrange terms to conclude
                          ~~ (((c_s + val_s) + val_s) + (2*((2 `power` width)*c0 )))
                           ...(Frex.solve 3 (Frex Nat.Additive) $
                             let c_s   = Dyn 0
                                 val_s = Dyn 1
                                 expc0 = Dyn 2
                             in c_s :+: ((val_s :+: expc0) :+: ((val_s :+: expc0) :+: Sta 0))
                             =-= ((c_s :+: val_s) :+: val_s) :+: (expc0 :+: (expc0 :+: Sta 0)) 
                           )
                         -- Since we don't have a semiring frexlet, we need another step
                         -- to associate brackets 
                         -- TODO: discharge with a multiplicative cmonoids frexlet
                         ~~ ((c_s + val_s) + val_s) + ((2*(2 `power` width))*c0)
                            ... (cong (((c_s + val_s) + val_s) +) $
                                      multAssociative 2 (2 `power` width) c0)
                        } 

commutativeAddNumber : (l : LE.Number w lft) -> (r : LE.Number w rgt) -> (carry : Bit c)
                     -> addNumber l r carry ~=~ addNumber r l carry
commutativeAddNumber num_l num_r carry = keep $
  numCarryUniqueForded
                  (addNumber num_l num_r carry)
                  (addNumber num_r num_l carry)
                  {ford = cong (+c) (plusCommutative lft rgt)} -- or frexify
