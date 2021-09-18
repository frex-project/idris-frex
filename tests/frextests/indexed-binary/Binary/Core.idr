module Binary.Core

import Data.Nat
import Data.Nat.Division
import Data.Nat.Order
import Data.Nat.Order.Properties
import Data.Nat.Properties

import Frex
import Frex.Free

import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Nat

import Syntax.PreorderReasoning


import Binary.Modular


public export
data Bit : Nat -> Type where
  O : Bit 0
  I : Bit 1

export
bitModulo : Bit b -> mod2 b = b
bitModulo O = Refl
bitModulo I = Refl

public export
data BitPair : Nat -> Type where
  MkBitPair : Bit b -> Bit c -> {auto 0 ford : d = b + b + c} ->  BitPair d
                           -- Hopefully we could simplify
                           -- once we have a semiring frexlet

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


public export
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

public export
andGate : Bit x -> Bit y -> Bit (x `and` y)
andGate I I = I
andGate O y = O
andGate I O = O

public export
orGate : Bit x -> Bit y -> Bit (x `or` y)
orGate O O = O
orGate O I = I
orGate I y = I

public export
xorGate : Bit x -> Bit y -> Bit (x `xor` y)
xorGate O O = O
xorGate O I = I
xorGate I O = I
xorGate I I = O
