||| Binary arithmetic indexed by their corresponding Nat Based on
||| "Constructing Correct Circuits: Verification of Functional Aspects
||| of Hardware Specifications with Dependent Types", by Edwin
||| C. Brady, James McKinna, Kevin Hammond, TFP2007.
module Binary

import Data.Fin

import Data.Nat
import Data.Nat.Division
import Data.Nat.Order
import Data.Nat.Order.Properties
import Data.Nat.Properties

import Data.Vect
import Data.Vect.Elem

import Frex
import Frex.Free

import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Nat

import Syntax.PreorderReasoning

import VectReasoning

import Binary.Modular
import Binary.Core
import Binary.BruteForce
import Binary.Number
import Binary.Bits
import Binary.Properties
import Binary.Arithmetic

commutativeAddNumber : (l : LE.Number w lft) -> (r : LE.Number w rgt) ->
  (carry : Bit c) -> addNumber l r carry ~=~ addNumber r l carry
commutativeAddNumber num_l num_r carry = keep $
  numCarryUniqueForded
                  (addNumber num_l num_r carry)
                  (addNumber num_r num_l carry)
                  {ford = cong (+c) (plusCommutative lft rgt)} -- or frexify
