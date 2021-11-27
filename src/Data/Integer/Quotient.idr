||| Representation of the integers using the INT-construction on Nat,
||| and quotients. Hopefully it'll be easier to prove its properties
module Data.Integer.Quotient

import public Data.Integer.Quotient.Definition
import public Data.Integer.Quotient.Operations

import Frex
import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Nat

import Frexlet.Group

import Frexlet.Monoid.Notation

import Data.Primitives.Views
import Data.Setoid
import Syntax.PreorderReasoning

import Syntax.WithProof
-- Let's validate the monoid axioms!

%default total

-- TODO: multiplication. Much easier once we have semiring frexlet.
