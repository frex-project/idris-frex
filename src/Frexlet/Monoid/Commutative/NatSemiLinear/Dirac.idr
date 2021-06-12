||| Properties relating to Kronecker's delta function, also known as
||| Dirac's delta distribution
module Frexlet.Monoid.Commutative.NatSemiLinear.Dirac

import Frex

import Notation
import Notation.Action

import Frexlet.Monoid.Commutative.Theory
import Frexlet.Monoid.Commutative.Notation.Core
import Data.Vect.Properties

import Syntax.PreorderReasoning.Generic
import Syntax.PreorderReasoning

import Frex.Free
import Frex.Free.Construction

import Frexlet.Monoid.Commutative.NatSemiLinear.Sum
import Frexlet.Monoid.Commutative.NatSemiLinear.Mult

import Decidable.Equality
import Data.Bool.Decidable

%default total

export
easyDec : DecEq a => (x : a) -> decEq x x = Yes Refl
easyDec  x with (decEq x x)
 easyDec x | Yes Refl  = Refl
 easyDec x | No contra = void $ contra Refl


public export
dirac : {0 n : Nat} -> (i, j : Fin n) -> Nat
dirac i j = case (decEq i j) of
  Yes _ => 1
  No  _ => 0
  
export
diracOnDiagonal : (i : Fin n) -> dirac i i = 1
diracOnDiagonal i = Calc $
  |~ dirac i i
  ~~ 1 ...(cong (\u => case u of {Yes _ => 1 ; No  _ => 0})
                (easyDec i))
export
diracOffDiagonal : (i,j : Fin n) -> Not (i = j) -> dirac i j = 0
diracOffDiagonal  i j neq with (decEq i j)
 diracOffDiagonal i j neq | Yes eq = void (neq eq)
 diracOffDiagonal i j neq | No  _  = Refl

public export
convolveDirac : (a : CommutativeMonoid) -> {n : Nat} ->
  let %hint 
      notation : Action1 Nat (U a)
      notation = NatAction1 a 
  in (f : Fin n -> U a) -> (i : Fin n) ->
   a.rel (a.sum $ tabulate \j => (dirac i j ) *. f j)
         (f i)
convolveDirac a f i = 
  let %hint 
      notation : Action1 Nat (U a)
      notation = NatAction1 a 
      xs : Vect n (U a)
      xs = tabulate \j => (dirac i j) *. f j
      pointMass : (j : Fin n) -> 
        (i = j) `Either` (a.rel (index j xs)
                                O1)
      pointMass  j with (decEq i j)
       pointMass j | Yes i_eq_j = Left i_eq_j
       pointMass j | No i_neq_j = Right $ CalcWith @{cast a} $
         |~ index j xs
         ~~ (dirac i j) *. (f j) ...(indexTabulate _ _)
         ~~ O1 ...(cong (*. f j) $ diracOffDiagonal i j i_neq_j)
  in CalcWith @{cast a} $
  |~ a.sum xs
  <~ index i xs         ...(sumDegenerate a xs i pointMass)
  ~~ (dirac i i) *. f i ...(indexTabulate _ _)
  ~~ (the Nat 1) *. f i ...(cong (*. f i) $ diracOnDiagonal i)
  <~ f i                ...(multUnit a _)

export
diracSym : {0 n : Nat} -> (i, j : Fin n) -> dirac i j = dirac j i
diracSym  i j with (decEq i j)
 diracSym i i | Yes Refl   = sym $ diracOnDiagonal    i
 diracSym i j | No i_neq_j = sym $ diracOffDiagonal j i (negEqSym i_neq_j)
