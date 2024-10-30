module Binary.Modular

import Data.Nat
import Data.Nat.Division

import Syntax.PreorderReasoning

import Frex
import Frex.Free

import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Nat


NZ2 : NonZero 2
NZ2 = %search

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

-- Some artihmetic facts

export
nonNegativeAddition : (b, c : Nat) -> b + c = 0 -> b = 0
nonNegativeAddition 0 c prf = Refl

export
multSucRightCancel : (a, b : Nat) -> (minusOne : Nat) ->
  a * (S minusOne) = b * (S minusOne) -> a = b
multSucRightCancel 0     b minusOne prf =
  sym $ nonNegativeAddition b (b * minusOne) $
  Calc $
  |~ b + (b * minusOne)
  ~~ (1 * b) + (b * minusOne) ...(Frex.solve 2 (Frex Nat.Additive) $
                                  Dyn 0 .+. Dyn 1 =-=
                                  (the Nat 1 *. Dyn 0) .+. Dyn 1)
  ~~ (b * 1) + (b * minusOne) ...(cong (+ b*minusOne) $ multCommutative 1 b)
  ~~ b * (1 + minusOne)       ...(sym $ multDistributesOverPlusRight _ _ _)
  ~~ 0                        ...(sym prf)
multSucRightCancel (S a) 0 minusOne prf = absurdSucIsZero _ prf
multSucRightCancel (S a) (S b) minusOne prf =
  cong S $ multSucRightCancel a b minusOne
         $ plusLeftCancel (1 + minusOne) _ _ prf


export
multSucLeftCancel : (a, b : Nat) -> (minusOne : Nat) -> (S minusOne) * a
  = (S minusOne) * b -> a = b
multSucLeftCancel a b minusOne prf = multSucRightCancel a b minusOne $
  Calc $
  |~ a * (S minusOne)
  ~~ (S minusOne) * a ...(multCommutative _ _)
  ~~ (S minusOne) * b ...(prf)
  ~~ b * (S minusOne) ...(multCommutative _ _)

export
powerNZ : (n : Nat) -> NonZero (2 `power` n)
powerNZ   0 = %search
powerNZ   (S n) with (powerNZ n)
 powerNZ  (S n) | prf with (2 `power` n)
  powerNZ (S n) | _ | S _ = %search

export
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

export
mod2Affine : (a, k : Nat) -> mod2 (2*k + a) = mod2 a
mod2Affine a k = modAffine a k 2 NZ2
