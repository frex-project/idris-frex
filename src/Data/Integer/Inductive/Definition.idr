module Data.Integer.Inductive.Definition

import Data.Setoid
import Syntax.PreorderReasoning

import Syntax.WithProof
import Data.Primitives.Views

import Frex
import Frexlet.Monoid.Commutative

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
minusCancelLeft : (left,mid,right : Nat) ->
  (left + mid) `Definition.minus` (left + right) = mid `minus` right
minusCancelLeft 0       mid rgt  = Refl
minusCancelLeft (S lft) mid rgt  = minusCancelLeft lft mid rgt

public export
minusCancelRight : (left,mid,right : Nat) -> (left + right) `Definition.minus` (mid + right) = left `minus` mid
minusCancelRight a b c = Calc $
  |~ ((a + c) `minus` (b + c))
  ~~ ((c + a) `minus` (c + b)) ...(cong2 minus (plusCommutative _ _) (plusCommutative _ _))
  ~~ (a `minus` b)             ...(minusCancelLeft _ _ _)

