||| CommutativeMonoid structures over the Nats
module Frexlet.Monoid.Commutative.Nat

import Frex
import public Frexlet.Monoid
import public Frexlet.Monoid.Nat
import Frexlet.Monoid.Commutative.Theory

import Notation
import Notation.Action
import Frexlet.Monoid.Commutative.Notation.Core
import Frexlet.Monoid.Commutative.NatSemiLinear

import Data.Nat

import Syntax.PreorderReasoning

||| Additive commutative monoid structure over the natural numbers
public export
Additive : CommutativeMonoid
Additive
  = MkCommutativeMonoid Monoid.Nat.Additive       \env => plusCommutative _ _

||| Multiplicative monoid structure over the natural numbers
public export
Multiplicative : CommutativeMonoid
Multiplicative
  = MkCommutativeMonoid Monoid.Nat.Multiplicative \env => multCommutative _ _

public export
multActionNat : (m, n : Nat) ->
  let %hint
      notationA : Action1 Nat Nat
      notationA = NatAction1 Additive
  in m *. n = m * n
multActionNat 0 n = Refl
multActionNat (S m) n =
  let %hint
      notationA : Action1 Nat Nat
      notationA = NatAction1 Additive
  in Calc $
  |~ (1 + m) *. n
  ~~ n  +  m *. n  ...(Refl)
  ~~ n  +  m *  n  ...(cong (n +) (multActionNat m n))
  ~~ (1 + m) *  n  ...(Refl)

public export
actionNatCommutative : (m, n : Nat) ->
  let %hint
      notationA : Action1 Nat Nat
      notationA = NatAction1 Additive
  in m *. n = n *. m
actionNatCommutative m n =
  let %hint
      notationA : Action1 Nat Nat
      notationA = NatAction1 Additive
  in Calc $
  |~ m *. n
  ~~ m *  n ...(multActionNat _ _)
  ~~ n *  m ...(multCommutative _ _)
  ~~ n *. m ...(sym $ multActionNat _ _)

