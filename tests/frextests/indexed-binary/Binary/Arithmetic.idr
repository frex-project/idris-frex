module Binary.Arithmetic

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

import Binary.Modular
import Binary.Core
import Binary.BruteForce
import Binary.Number
import Binary.Bits
import Binary.Properties

export
addNumber : LE.Number width x -> LE.Number width y -> Bit c ->
  NumCarry width (x + y + c)
addNumber []          []   carry = Carrying [] carry
  {valueFord = Frex.solve 1 (Frex Nat.Additive) $ (Dyn 0 =-= Dyn 0 :+: Sta 0)}
    -- could also discharge by permuting the terms in the second index
    -- of `NumCarry`

addNumber {c = c} {width = S width}
          ((a :: aits) {b = b_a, val = val_a, valueFord = Refl})
          ((b :: bits) {b = b_b, val = val_b, valueFord = Refl})
          carry
          with (addBit a b carry)
 addNumber
          {c = c} {width = S width}
          ((a :: aits) {b = b_a, val = val_a, valueFord = Refl})
          ((b :: bits) {b = b_b, val = val_b, valueFord = Refl})
          carry
          | MkBitPair carry0 s
             {b = b_s, c = c_s, ford}
          with (addNumber aits bits carry0)
  addNumber
          {c = c} {width = S width}
          ((a :: aits) {b = b_a, val = val_a, valueFord = Refl})
          ((b :: bits) {b = b_b, val = val_b, valueFord = Refl})
          carry
          | MkBitPair carry0 s {b = b_s, c = c_s, ford}
          | Carrying sits carry1 {val = val_s, c = c0, valueFord}
            = Carrying
                (s :: sits)
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
                           in (((b_a :+: val_a) :+: val_a) :+:
                                ((b_b :+: val_b) :+: val_b)) :+: c
                              =-=
                              ((b_a :+: b_b) :+: c) :+:
                                (((val_a :+: val_a) :+: val_b) :+: val_b)
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
                           =-= c_s :+: 2 *:(((val_a :+: val_b) :+: b_s)))
                  ~~ c_s + 2*(val_s + ((2 `power` width)*c0))
                       ...(cong (\u => c_s + 2*u)
                                valueFord)
                  -- rearrange terms to conclude
                  ~~ ((c_s + val_s) + val_s) + (2*((2 `power` width)*c0))
                   ...(Frex.solve 3 (Frex Nat.Additive) $
                     let c_s   = Dyn 0
                         val_s = Dyn 1
                         expc0 = Dyn 2
                     in c_s :+: (2 *: (val_s :+: expc0))
                     =-= ((c_s :+: val_s) :+: val_s) :+: (2 *: expc0)
                   )
                 -- Since we don't have a semiring frexlet, we need another step
                 -- to associate brackets
                 -- TODO: discharge with a multiplicative cmonoids frexlet
                 ~~ ((c_s + val_s) + val_s) + ((2*(2 `power` width))*c0)
                    ... (cong (((c_s + val_s) + val_s) +) $
                              multAssociative 2 (2 `power` width) c0)
                }
