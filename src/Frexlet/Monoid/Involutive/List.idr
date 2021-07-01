module Frexlet.Monoid.Involutive.List

import Frex
import Frexlet.Monoid.Involutive.Theory
import Frexlet.Monoid
import Data.Setoid
import Data.List

%default total

ltrans : {A:Setoid} -> {l1, l2, l3 : List (U A)} -> A .ListEquality l1 l2 -> A .ListEquality l2 l3 -> A .ListEquality l1 l3
ltrans {l1,l2,l3} = A .ListEqualityTransitive l1 l2 l3

lsym : {A:Setoid} -> {l1, l2 : List (U A)} -> A .ListEquality l1 l2 -> A .ListEquality l2 l1
lsym {l1,l2} = A .ListEqualitySymmetric l1 l2

lrefl : {A:Setoid} -> {l1 : List (U A)} -> A .ListEquality l1 l1
lrefl {l1} = A .ListEqualityReflexive l1

reverseHomomorphic : {A : Setoid} -> (x, y : List (U A)) -> (A .ListEquality x y) -> A .ListEquality (reverse x) (reverse y)
reverseHomomorphic l1 l2 prf = roh [] [] l1 l2 lrefl prf
  where roh  : {A : Setoid} -> (w, x, y, z : List (U A)) -> (A .ListEquality w x) ->(A .ListEquality y z) ->
               A .ListEquality (reverseOnto w y) (reverseOnto x z)
        roh w x [] [] yz Nil = yz
        roh w x (y::ys) (z::zs) wx (yzh :: yzt) = roh (y::w) (z::x) ys zs (yzh :: wx) yzt

revOnto : {A:Setoid} -> (xs, vs : List (U A)) -> A .ListEquality (reverseOnto xs vs) (reverse vs ++ xs)
revOnto xs [] = lrefl
revOnto xs (v :: vs) =
   let h1 = revOnto (v :: xs) vs in
   let h2 = assocAppend (reverseOnto [] vs) [v] xs in
   let h4 = lsym (revOnto [v] vs) in
   let h5 = prodCong _ _ _ _ h4 lrefl in
  ltrans h1 (ltrans h2 h5)

revAppend : {A:Setoid} -> (vs, ns : List (U A)) -> A .ListEquality (reverse ns ++ reverse vs) (reverse (vs ++ ns))
revAppend [] ns = rightAppendNeutral _
revAppend (v::vs) ns =
  let h1 = revAppend vs ns in
  let h2 = revOnto [v] (vs ++ ns) in
  let h3 = prodCong _ _ (reverseOnto [] (vs ++ ns)) [v] h1 lrefl in
  let h4 = ltrans h3 (lsym h2) in
  let h5 = assocAppend (reverseOnto [] ns) (reverseOnto [] vs) [v] in
  let h6 = prodCong _ _ _ _ lrefl (revOnto [v] vs) in
    ltrans (ltrans h6 h5) h4

revInvolutive : {A:Setoid} -> (l: List (U A)) -> (A .ListEquality (reverse (reverse l)) l)
revInvolutive [] = lrefl
revInvolutive (x::xs) = 
  let h1 = reverseHomomorphic _ _ (revOnto [x] xs) in
  let h2 = lsym (revAppend (reverse xs) [x]) in
  let h3 = revInvolutive xs in
  let h4 = prodCong [x] (reverseOnto [] (reverseOnto [] xs)) [x] xs lrefl h3 in
    (ltrans (ltrans  h1 h2) h4)

public export
List : {A: Setoid} -> InvolutiveMonoid
List = MkModel (MkInvolutiveMonoidStructure ((ListMonoid {A}) .Algebra)
                 (MkSetoidHomomorphism Data.List.reverse reverseHomomorphic))
  $ \case
     (Mon LftNeutrality) => ListMonoid .Validate LftNeutrality
     (Mon RgtNeutrality) => ListMonoid .Validate RgtNeutrality
     (Mon Associativity) => ListMonoid .Validate Associativity
     Involutivity        => \env => revInvolutive (env 0)
     Antidistributivity  => \env => lsym (revAppend (env 0) (env 1))
