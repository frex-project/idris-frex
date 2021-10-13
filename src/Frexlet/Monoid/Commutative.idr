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

%default total

public export
Frex : Frexlet {pres = CommutativeMonoidTheory}
Frex a = CoproductsAndFreeFrex CoproductCospan Frexlet.Monoid.Commutative.Free.Free a
