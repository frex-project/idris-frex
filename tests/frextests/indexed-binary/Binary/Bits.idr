module Binary.Bits

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
import Syntax.PreorderReasoning.Generic

import VectReasoning

import Binary.Modular
import Binary.Core
import Binary.BruteForce
import Binary.Number


public export
(*:) : Nat -> Term Theory.Signature (Either a (Fin n)) ->
       Term Theory.Signature (Either a (Fin n))
(*:) 0 x = O2
(*:) (S k) x = x :+: (k *: x)




-- Not true for general c,x,y (e.g., for (0, 0, S k) we get (S k = 1)
-- but true if we case split on l, r, and cIn
-- Tell Edwin there's a (tiny) mistake in the paper, maybe he already knows
export
0 addBit_Ford : (cIn : Bit c) -> (l : Bit x) -> (r : Bit y) ->
  (c + x) + y =
  ((((x `and` y) `or` (y `and` c)) `or` (c `and` x))
  +(((x `and` y) `or` (y `and` c)) `or` (c `and` x)))
  + ((x `xor` y) `xor` c)
addBit_Ford cIn l r =
  bruteForce (\ [c,x,y] =>
    ((c + x) + y
    , ((((x `and` y) `or` (y `and` c)) `or` (c `and` x))
      +(((x `and` y) `or` (y `and` c)) `or` (c `and` x)))
      + ((x `xor` y) `xor` c)
    ))
    [(_ ** cIn), (_ ** l), (_ ** r)]

public export
addBit : Bit c -> Bit x -> Bit y -> BitPair (c + x + y)
addBit cIn l r =
       let cOut = orGate (orGate (andGate l r)
                                 (andGate r cIn))
                         (andGate cIn l)
           s = xorGate (xorGate l r) cIn
       in MkBitPair cOut s
          {ford = bruteForce (\ [c, x, y] =>
            ((c + x) + y
            , ((((x `and` y) `or` (y `and` c)) `or` (c `and` x))
              +(((x `and` y) `or` (y `and` c)) `or` (c `and` x)))
              + ((x `xor` y) `xor` c)
            ))
            [(_ ** cIn), (_ ** l), (_ ** r)]}

export
bitUnique : (x : Bit c_x) -> (y : Bit c_y) -> c_x = c_y -> x = y
bitUnique O O Refl = Refl
bitUnique I I Refl = Refl

export
bitBound : (x : Bit b) -> b `LT` 2
bitBound O =           LTESucc LTEZero
bitBound I = LTESucc $ LTESucc LTEZero

export 0
bitsBound : (x : LE.Number width val) -> val `LT` (2 `power` width)
bitsBound [] = LTESucc LTEZero
bitsBound {width = S width} ((bit :: bits)
                             {b, val, val' = _, valueFord = Refl}) =
  CalcWith  $
  |~ 1 + ((b + val) + val)
  ~~ (1 + b) + (2*val)       ...(Frex.solve 2 (Frex Nat.Additive) $
                                 Sta 1 :+: ((Dyn 0 :+: Dyn 1) :+: Dyn 1)
                                 =-=
                                 (Sta 1 :+: Dyn 0) :+: (2 *: Dyn 1))
  <~ 2 + (2*val)             ...(plusLteMonotoneRight (2*val) (1 + b) 2 $
                                 bitBound bit)
  ~~ 2*(1 + val)             ...(sym $ multDistributesOverPlusRight 2 1 val)
  <~ (2 `power` (1 + width)) ...(multLteMonotoneRight 2 (1 + val)
                                                        (2 `power` width) $
                                 bitsBound bits)
