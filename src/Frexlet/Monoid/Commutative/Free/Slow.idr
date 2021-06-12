module Frexlet.Monoid.Commutative.Free.Slow

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

import Frexlet.Monoid.Commutative.Free

%default total


export
normalForm : (n : Nat) -> (xs : U (Model n)) -> 
  let %hint 
      notation : Action1 Nat (U $ Model n)
      notation = NatAction1 (Model n)
  in (Model n).sum (tabulate \i => (index i xs) *. (unit n i)) = xs
normalForm n xs = vectorExtensionality _ _ $ \i => 
  let %hint 
      notation : Action1 Nat (U $ Model n)
      notation = NatAction1 (Model n)
      %hint 
      notation' : Action1 Nat (U $ Commutative.Nat.Additive)
      notation' = NatAction1 Additive
      lemma1 : (j : Fin n) -> index i ((index j xs) *. (unit n j)) = (dirac i j) *. (index j xs)
      lemma1 j = Calc $
        |~ index i ((index j xs) *. (unit n j)) 
        ~~ (index j xs) *  (index i $ unit n j) ...(pointwiseMult n (index j xs) (unit n j) i)
        ~~ (index j xs) *. (index i $ unit n j) ...(sym $ multActionNat _ _)
        ~~ (index j xs) *. (dirac j i)          ...(cong ((index j xs) *.) $ indexTabulate (dirac j) i)
        ~~ (index j xs) *. (dirac i j)          ...(cong (index j xs *.) $ diracSym _ _)
        ~~ (dirac i j ) *. (index j xs)         ...(actionNatCommutative _ _)
      lemma2 := Calc $
        |~ map (index i) (tabulate \j => (index j xs) *. (unit n j))
        ~~ tabulate (\j => (index i $ (index j xs) *. (unit n j))) ...(sym $ mapTabulate (index i) 
                                                                      \j => (index j xs) *. (unit n j))
        ~~ tabulate (\j => (dirac i j) *. (index j xs)) ...(tabulateExtensional _ _ lemma1)
  in Calc $
  |~ index i ((Model n).sum (tabulate \i => (index i xs) *. (unit n i)))
  ~~ (Additive).sum (map (index i) (tabulate \i => (index i xs) *. (unit n i))) 
                                                                 ...(pointwiseSum n _ _)
  ~~ (Additive).sum (tabulate \j => (dirac i j) *. (index j xs)) ...(cong (Additive).sum lemma2)
  ~~ index i xs                                                  ...(convolveDirac Additive _ _)
  
