module Frexlet.Monoid.Commutative

import Frex

import Notation
import Notation.Action

import public Frexlet.Monoid.Theory
import public Frexlet.Monoid.Commutative.Theory
import public Frexlet.Monoid.Commutative.Notation.Core
import public Frexlet.Monoid.Commutative.Nat
import public Frexlet.Monoid.Commutative.Coproduct
import public Frexlet.Monoid.Commutative.Free

public export
Frex : (a : CommutativeMonoid) -> {x : Setoid} -> Frex a x
Frex a = CoproductsAndFreeFrex CoproductCospan (Free CommutativeMonoidTheory x) a

