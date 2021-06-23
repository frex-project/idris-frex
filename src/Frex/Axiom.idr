||| Definitions and functions dealing with single-sorted finitary signatures
module Frex.Axiom

import Frex.Signature
import Frex.Presentation
import Frex.Algebra

import Notation
import public Notation.Additive

import Data.Fin

infix 1 =-=

||| Smart constructor for making equations look nicer
public export
(=-=) : {0 a : Type} -> (t, s : Term sig a)
                  -> (Term sig a, Term sig a)
t =-= s = (t, s)

||| Smart constructor for equations over finitely many variables
public export
MkEquation : (n : Nat) -> (eq : (Term sig (Fin n), Term sig (Fin n))) -> Equation sig
MkEquation n (t,s) = MkEq (Fin n) t s

||| Auxiliary: extract additive notation for two given operations
public export
additiveNotation : {sig : Signature} -> (neutral : OpWithArity sig 0) -> (product : OpWithArity sig 2)
  -> Additive1 (Term sig (Fin k))
additiveNotation {sig} neutral product = MkAdditive1 (call neutral) (call product)

||| Metaprogramming: the type of an equation parameterised by
||| operations of the given arity vecotr
public export
EqSpec : (sig : Signature) -> (arities : Vect n Nat) ->  Type
EqSpec sig [] = Equation sig
EqSpec sig (n :: arities) = (op : OpWithArity sig n) -> EqSpec sig arities


-- Common axioms

||| O + x = x
public export
lftNeutrality : {sig : Signature} -> EqSpec sig [0,2]
lftNeutrality neutral product =
  let uvw = additiveNotation neutral product in
  MkEquation 1 $ O1 .+. X 0 =-= X 0

||| x + O = x
public export
rgtNeutrality : {sig : Signature} -> EqSpec sig [0,2]
rgtNeutrality neutral product =
  let uvw = additiveNotation neutral product in
  MkEquation 1 $ X 0 .+. O1 =-= X 0

||| x + (y + z) = (x + y) + z
public export
associativity : {sig : Signature} -> EqSpec sig [2]
associativity product =
  let (+) = call product in
  MkEquation 3 $ X 0 + (X 1 + X 2) =-= (X 0 + X 1) + X 2

||| x + y = y + x
public export
commutativity : {sig : Signature} -> EqSpec sig [2]
commutativity product =
  let (+) = call product in
  MkEquation 2 $ X 0 + X 1 =-= X 1 + X 0

public export
involutivity : {sig : Signature} -> EqSpec sig [1]
involutivity involution =
  let (.inv) = call involution in
  MkEquation 1 $ (X 0).inv.inv  =-= X 0

public export
antidistributivity : {sig : Signature} -> EqSpec sig [1, 2]
antidistributivity involution product =
  let (.inv) = call involution 
      (*)    = call product
  in 
  MkEquation 2 $ (X 0 * X 1).inv  =-= (X 1).inv * (X 0).inv
