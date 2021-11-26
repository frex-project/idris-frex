module Data.Integer.Inductive

import public Data.Integer.Inductive.Definition

import Data.Setoid
import Syntax.PreorderReasoning

import Syntax.WithProof
import Data.Primitives.Views

import Frex
import Frexlet.Monoid.Commutative

import Data.Integer.Quotient
import Data.Integer.Connections

-- Let's validate the monoid axioms!

%default total

public export
Additive : Monoid
Additive = transportSetoid Quotient.Operations.Additive representationInteger

public export
plus : (m,n : INTEGER) -> INTEGER
plus m n = (Inductive.Additive).Sem Prod [m,n]

public export
mult : (m,n : INTEGER) -> INTEGER
-- TODO: implement. Much easier once we have semiring frexlet.

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

