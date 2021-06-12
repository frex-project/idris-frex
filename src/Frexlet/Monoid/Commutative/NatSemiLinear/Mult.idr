||| Properties to do with sums
module Frexlet.Monoid.Commutative.NatSemiLinear.Mult

import Frex

import Notation
import Notation.Action

import Frexlet.Monoid.Commutative.Theory
import Frexlet.Monoid.Commutative.Notation.Core
import Data.Vect.Properties

import Syntax.PreorderReasoning.Generic

import Frex.Free
import Frex.Free.Construction

import Frexlet.Monoid.Commutative.NatSemiLinear.Sum

%default total

-- ----------------------------------------------------------------- --- [Mult]

public export
multUnit : (a : CommutativeMonoid) -> 
  let %hint 
      notation : Action1 Nat (U a)
      notation = NatAction1 a 
  in  (x : U a) -> a.rel (the Nat 1 *. x)
                                       x
multUnit a x = 
  let %hint 
      notation : Action1 Nat (U a)
      notation = NatAction1 a 
  in CalcWith @{cast a} $
  |~ the Nat 1 *. x
  ~~ x .+. O1  ...(Refl)
  <~ x         ...(a.Validate (Mon RgtNeutrality) (flip index [_]))
  
public export
multDistributesOverPlusLeft : (a : CommutativeMonoid) ->
  let %hint 
      notation : Action1 Nat (U a)
      notation = NatAction1 a 
  in (n, m : Nat) -> (x : U a) ->
      a.rel
        ((n + m) *. x)
        (n *. x .+. m *. x)
multDistributesOverPlusLeft a 0     m x = 
  let %hint 
      notation : Action1 Nat (U a)
      notation = NatAction1 a 
  in CalcWith @{cast a} $
  |~ (0 + m) *. x
  ~~      m  *. x          ...(Refl)
  <~ (Z *. x) .+. (m *. x) ...( a.equivalence.symmetric _ _ 
                              $ a.validate (Mon LftNeutrality) [_])
  
multDistributesOverPlusLeft a (S n) m x = 
  let %hint 
      notation : Action1 Nat (U a)
      notation = NatAction1 a 
  in CalcWith @{cast a} $
  |~ (1 + (n + m)) *. x
  ~~ x .+.(n + m) *. x        ...(Refl)
  <~ x .+.(n *. x .+. m *. x) ...(a.cong 1 (Sta x .+. Dyn 0) [_] [_]
                                      [multDistributesOverPlusLeft a n m x])
  <~x .+. n *. x .+. m *. x   ...(a.validate (Mon Associativity) [_,_,_])
  ~~ (1 + n) *. x .+. m *. x  ...(Refl)

-- Not used here, but for completeness:

public export
multDistributesOverPlusRight : (a : CommutativeMonoid) ->
  let %hint 
      notation : Action1 Nat (U a)
      notation = NatAction1 a 
  in (n : Nat) -> (x,y : U a) ->
      a.rel
        (n *. (x .+. y))
        (n *. x .+. n *. y)
  
multDistributesOverPlusRight a 0 x y = a.equivalence.symmetric _ _ $
                                       a.validate (Mon LftNeutrality) [_]
multDistributesOverPlusRight a (S n) x y = 
  let %hint 
      notation : Action1 Nat (U a)
      notation = NatAction1 a 
  in CalcWith @{cast a} $
  |~ (1 + n) *. (x .+. y) 
  ~~ (x .+. y) .+. n *. (x .+. y)          ...(Refl)
  <~ (x .+. y) .+. ((n *. x) .+. (n *. y)) ...(a.cong 1 (Sta _ .+. Dyn 0) [_] [_]
                                               [multDistributesOverPlusRight a n x y])
  <~ (x .+. n *. x) .+. (y .+. n *. y)     ...(interchange a _ _ _ _)
  ~~ (1 + n) *. x .+. (1 + n) *. y         ...(Refl)

||| NB: a,b are explicit since we can't recover them from the
||| homomorphism between them as algebras alone.
public export
multPreservation : (a, b : CommutativeMonoid) ->
  let %hint 
      notationA : Action1 Nat (U a)
      notationA = NatAction1 a 
      %hint
      notationB : Action1 Nat (U b)
      notationB = NatAction1 b
  in (h : a ~> b) -> (n : Nat) -> (x : U a) ->
  b.rel (h.H.H (n *. x))
        (n *. h.H.H x)
multPreservation a b h  0    x = h.preserves Zero []
multPreservation a b h (S n) x = 
  let %hint 
      notationA : Action1 Nat (U a)
      notationA = NatAction1 a 
      %hint
      notationB : Action1 Nat (U b)
      notationB = NatAction1 b
  in CalcWith @{cast b} $
  |~ h.H.H ((1 + n) *. x)
  ~~ h.H.H (x .+. n *. x)       ...(Refl)
  <~ h.H.H x .+. h.H.H (n *. x) ...(h.preserves Plus [x, n *.x])
  <~ h.H.H x .+. n *. h.H.H x   ...(b.cong 1 (Sta (h.H.H x) .+. Dyn 0) [_] [_]
                                    [multPreservation a b h n x])
  ~~ (1 + n) *. h.H.H x         ...(Refl)

