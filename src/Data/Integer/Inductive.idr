module Data.Integer.Inductive

import Data.Setoid
import Syntax.PreorderReasoning

import Syntax.WithProof
import Data.Primitives.Views
-- Let's validate the monoid axioms!

%default total

-- TODO: multiplication. Much easier once we have semiring frexlet.

public export
data INTEGER : Type where
  ||| ANat n : the integer n
  ANat : Nat -> INTEGER
  ||| NegS n : the integer -(S n)
  NegS : Nat -> INTEGER

public export
minus : (m, n : Nat) -> INTEGER
minus    m   0    = ANat m
minus  0    (S n) = NegS n
minus (S m) (S n) = minus m n

public export
plus : (m,n : INTEGER) -> INTEGER
plus (ANat m) (ANat n) = ANat (m + n)
plus (ANat m) (NegS n) = minus m (S n)
plus (NegS m) (ANat n) = minus n (S m)
plus (NegS m) (NegS n) = NegS (S (m + n))

public export
mult : (m,n : INTEGER) -> INTEGER
mult (ANat m) (ANat n) = ANat (m * n)
mult (ANat 0) (NegS n) = ANat 0
mult (ANat (S m)) (NegS n) = NegS (m + n + m*n)
mult (NegS m) (ANat 0) = ANat 0
mult (NegS m) (ANat (S n)) = NegS (m + n + m*n)
mult (NegS m) (NegS n) = ANat ((S m) * (S n))

public export
Num INTEGER where
  fromInteger x = case compare x 0 of
    LT => NegS (fromInteger $ negate (1 + x))
    _  => ANat (fromInteger x)
  (+) = plus
  (*) = mult

public export
Neg INTEGER where
  negate = (ANat 0 -)
  (ANat m) - (ANat n) = minus m n
  (ANat m) - (NegS n) = ANat (S (m + n))
  (NegS m) - (ANat n) = NegS (S (m + n))
  (NegS m) - (NegS n) = minus n m

public export
Show INTEGER where
  show (ANat m) = show m
  show (NegS n) = "-\{show (S n)}"

