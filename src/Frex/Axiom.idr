||| Definitions and functions dealing with single-sorted finitary signatures
module Frex.Axiom

import Frex.Signature
import Frex.Presentation
import Frex.Algebra

import Notation
import Notation.Additive

import Data.Fin


infix 1 =-=

public export
(=-=) : {0 a : Type} -> (t, s : Term sig a) 
                  -> (Term sig a, Term sig a)

public export
MkEquation : (n : Nat) -> (eq : (Term sig (Fin n), Term sig (Fin n))) -> Equation sig
MkEquation n (t,s) = MkEq (Fin n) t s


data OpWithArity : Signature -> Nat -> Type where
  MkOp : {sig : Signature} -> (f : Op sig) -> OpWithArity sig (sig.arity f)

op : OpWithArity sig n -> Op sig
op (MkOp f) = f

call : OpWithArity sig n -> n `ary` (Term sig x)
call (MkOp f) = curry (Call f) 



public export
notation : {sig : Signature} -> (neutral : OpWithArity sig 0) -> (product : OpWithArity sig 2)
  -> Additive1 (Term sig (Fin k))
notation neutral product = MkAdditive1 (call neutral) (call product)

public export
X : {sig : Signature} -> Fin k -> Term sig (Fin k)
X = Done

public export
EqSpec : (sig : Signature) -> (arities : Vect n Nat) ->  Type
EqSpec sig [] = Equation sig
EqSpec sig (n :: arities) = (op : OpWithArity sig n) -> EqSpec sig arities

public export
lftNeutrality : {sig : Signature} -> EqSpec sig [0,2]
lftNeutrality neutral product =
    let uvw = notation neutral product in
    MkEquation 2 $ O1 .+. X 0 =-= X 0

public export
rgtNeutrality : {sig : Signature} -> EqSpec sig [0,2]
rgtNeutrality neutral product =
    let uvw = notation neutral product in
    MkEquation 2 $ X 0 .+. O1 =-= X 0

public export
associativity : {sig : Signature} -> EqSpec sig [2]
associativity product =
    let (.+.) = call product in
    MkEquation 3 $ X 0 .+. (X 1 .+. X 2) =-= (X 0 .+. X 1) .+. X 2


