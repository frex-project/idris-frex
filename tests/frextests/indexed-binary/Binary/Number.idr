module Binary.Number

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

-- Until we get a semiring frexlet, `little-endian` bits are easier
-- The downside is that we will diverge from the paper

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


-- Smart constructors, flipping the indexing methods
public export
LENil : BE.Number 0 0
LENil = []

export
rightNeut : (p : Nat) -> p + 0 = p
rightNeut p = Frex.solve 1 (Frex Nat.Additive) $ Dyn 0 :+: Sta 0 =-= Dyn 0

public export
LECons : Bit b -> BE.Number width val -> BE.Number (1 + width) (b + val + val)
LECons bit [] = [bit]
LECons {b} bit ((bit' :: bits)
                {b = b', width, val, valueFord = Refl}) =
   let r : {b, p, q, b', v : Nat} ->
           (b + (p * b' + v)) + (q * b' + v) =
           (p * b' + q * b') + ((b + v) + v)
       r = Frex.solve 4 (Frex Nat.Additive) $
            (Dyn 0 :+: (Dyn 1 :+: Dyn 2)) :+: (Dyn 3 :+: Dyn 2) =-=
            (Dyn 1 :+: Dyn 3) :+: ((Dyn 0 :+: Dyn 2) :+: Dyn 2)
    in
  (bit' :: LECons bit bits) { valueFord
    = rewrite rightNeut (power 2 width) in
      rewrite multDistributesOverPlusLeft
                (power 2 width) (power 2 width) b' in
      r {b,p=power 2 width,q=power 2 width,b',v=val} }

public export
LEtoBE : LE.Number w val -> BE.Number w val
LEtoBE [] = LENil
LEtoBE ((x :: xs) {valueFord = Refl})  = x `LECons` (LEtoBE xs)

public export
BENil : LE.Number 0 0
BENil = []

public export
BECons : Bit b -> LE.Number width val ->
  LE.Number (1 + width) ((2 `power` width) * b + val)
BECons bit [] = [bit]
BECons {b} bit ((bit' :: bits)
                {b = b', width, val, valueFord = Refl}) =
  let r : {p, q, b, b', v : Nat} ->
          ((p + q) * b) + ((b' + v) + v) =
          (b' + ((p * b) + v)) + ((q * b) + v)
      r {p, q, b, b', v}
        = rewrite multDistributesOverPlusLeft p q b in
          Frex.solve 4 (Frex Nat.Additive)
          $   ((Dyn 0 :+: Dyn 1)) :+: ((Dyn 2 :+: Dyn 3) :+: Dyn 3)
          =-= (Dyn 2 :+: (Dyn 0 :+: Dyn 3)) :+: (Dyn 1 :+: Dyn 3)
   in
   (bit' :: BECons bit bits)
   {valueFord = rewrite rightNeut (power 2 width) in r}

public export
BEtoLE : BE.Number w val -> LE.Number w val
BEtoLE [] = BENil
BEtoLE ((bit :: bits) {valueFord = Refl}) = bit `BECons` (BEtoLE bits)

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
