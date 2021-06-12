||| An inductive construction of the free commutative monoid over a
||| finite set.
module Frexlet.Monoid.Commutative.Free

import Frex

import Notation
import Notation.Action

import Frexlet.Monoid.Commutative.Theory
import Frexlet.Monoid.Commutative.Notation.Core
import Data.Vect.Properties

import Syntax.PreorderReasoning.Generic
import Syntax.PreorderReasoning

import Frexlet.Monoid.Commutative.NatSemiLinear

import public Frexlet.Monoid.Commutative.Nat

import Decidable.Equality
import Data.Bool.Decidable
import Data.Nat

%default total

public export
Model : (n : Nat) -> CommutativeMonoid
Model n = (Commutative.Nat.Additive ^ n).Data.Model

||| Monadic unit
public export
unit : (n : Nat) -> Fin n -> U (Model n)
unit n i = Fin.tabulate \j => dirac i j

public export
FreeCommutativeMonoidOver : (n : Nat) -> CommutativeMonoidTheory `ModelOver` (cast $ Fin n)
FreeCommutativeMonoidOver n = 
  MkModelOver
  { Model = Model n
  , Env   = mate (\i => unit n i)
  }

export
FreeModelZeroRepresentation : (n : Nat) -> (Model n).sem Neutral = replicate n 0
FreeModelZeroRepresentation  n = vectorExtensionality _ _ \i => Calc $
  |~ index i (map (uncurry 0) (replicate n Vect.Nil))
  ~~ uncurry 0 (index i $ replicate n Vect.Nil) ...(indexNaturality _ _ _)
  ~~ 0                                          ...(Refl)
  ~~ index i (replicate n 0)                    ...(sym $ indexReplicate _ _)

export
pointwiseSum : (n : Nat) -> (xss : Vect m (U $ Model n)) -> (i : Fin n) ->
  index i ((Model n).sum xss) = (Nat.Additive).sum (map (index i) xss)
pointwiseSum n xss i = sumPreservation (Model n) (Nat.Additive) (Fin.eval i) xss

export
pointwiseMult : (n : Nat) -> (m : Nat) -> (xs : (U $ Model n)) -> (i : Fin n) ->
  let %hint 
      notation : Action1 Nat (U $ Model n)
      notation = NatAction1 (Model n)
  in 
  index i (m *. xs) = m * (index i xs)
pointwiseMult n m xs i = 
  let %hint 
      notation : Action1 Nat (U $ Model n)
      notation = NatAction1 (Model n)
      %hint
      notation' : Action1 Nat (U $ Commutative.Nat.Additive)
      notation' = NatAction1 (Nat.Additive)
  in Calc $ 
  |~ index i (m *. xs)
  ~~ m *. (index i xs) ...(multPreservation (Model n) (Nat.Additive) (Fin.eval i) m xs)
  ~~ m * (index i xs) ...(multActionNat _ _)

export
diracPointMass : (i, j : Fin n) -> 
           (i = j, index j (unit n i) = 1) 
  `Either` (index j (unit n i) = 0)
diracPointMass  i j with (decEq i j)
 diracPointMass i i | Yes Refl = Left (Refl, Calc $
   |~ index i (unit n i)
   ~~ dirac i i ...(indexTabulate (dirac i) i)
   ~~ 1         ...(diracOnDiagonal _))
 diracPointMass i j | No i_neq_j = Right $ Calc $
   |~ index j (unit n i)
   ~~ dirac i j ...(indexTabulate (dirac i) j)
   ~~ 0         ...(diracOffDiagonal i j i_neq_j)

