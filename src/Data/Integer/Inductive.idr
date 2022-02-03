module Data.Integer.Inductive

import public Data.Integer.Inductive.Definition

import Data.Setoid
import Syntax.PreorderReasoning

import Syntax.WithProof
import Data.Primitives.Views

import Frex
import Frexlet.Monoid.Commutative
import Frexlet.Group

import Data.Integer.Quotient
import Data.Integer.Connections

-- Let's validate the monoid axioms!

%default total
namespace Monoid
  public export
  Additive : Monoid
  Additive = transportSetoid Quotient.Operations.Monoid.Additive representationInteger

public export
plus : (m,n : INTEGER) -> INTEGER
plus m n = (Inductive.Monoid.Additive).Sem Prod [m,n]

public export
mult : (m,n : INTEGER) -> INTEGER
-- TODO: implement. Much easier once we have semiring frexlet.

namespace Group
  public export
  Additive : Group
  Additive = transportSetoid Quotient.Operations.Group.Additive representationInteger

public export
Num INTEGER where
  fromInteger x = case compare x 0 of
    LT => NegS (fromInteger $ negate (1 + x))
    _  => ANat (fromInteger x)
  (+) = plus
  (*) = mult

public export
Neg INTEGER where
  negate = Algebra.curry $ (Inductive.Group.Additive).Algebra.algebra.Semantics Invert
  m - n = m + negate n

public export
Show INTEGER where
  show (ANat m) = show m
  show (NegS n) = "-\{show (S n)}"
