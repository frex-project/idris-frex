||| Properties of the monoid frexlet and its operations
module Frexlet.Monoid.Frex.Properties

import Frex

import Frexlet.Monoid.Theory
import Frexlet.Monoid.Notation
import Frexlet.Monoid.Frex.Structure

import Notation.Multiplicative
import Notation.Action

import Data.List
import Data.List.Elem

import Data.Setoid.Pair

%default total
----------------------------- .mult properties
public export
multUnitNeutral : (a : Monoid) -> (s : Setoid) -> (is : FrexCarrier a s) ->
  let %hint
      notation : MAction1 (U a) (FrexCarrier a s)
      notation = cast $ MonAction a s
      %hint
      notation' : Multiplicative1 (U a)
      notation' = a.Multiplicative1
  in (FrexSetoid a s).equivalence.relation
       (the (U a) I1 *. is)
       is
multUnitNeutral a s (Ultimate i) = Ultimate $ a.validate LftNeutrality [_]
multUnitNeutral a s (ConsUlt i x is) = 
  ( a.validate LftNeutrality [_]
  , s.equivalence.reflexive _
  ) :: (FrexSetoid a s).equivalence.reflexive _

public export
multAssociative : (a : Monoid) -> (s : Setoid) -> (i0,i1 : U a) -> (is : FrexCarrier a s) ->
  let %hint
      notation : MAction1 (U a) (FrexCarrier a s)
      notation = cast $ MonAction a s
      %hint
      notation' : Multiplicative1 (U a)
      notation' = a.Multiplicative1
  in (FrexSetoid a s).equivalence.relation
       (i0 *. (i1 *. is))
       ((i0 .*. i1) *. is)
multAssociative a s i0 i1 (Ultimate i) = Ultimate $ a.validate Associativity [_,_,_]
multAssociative a s i0 i1 (ConsUlt i x is) = 
  ( a.validate Associativity [_,_,_]
  , s.equivalence.reflexive _
  ) :: (FrexSetoid a s).equivalence.reflexive _


public export
multMultAssociative : (a : Monoid) -> (s : Setoid) -> (i0 : U a) -> (is,js : FrexCarrier a s) ->
  let %hint
      notation : MAction1 (U a) (FrexCarrier a s)
      notation = cast $ MonAction a s
      %hint
      notation' : Multiplicative1 (U a)
      notation' = a.Multiplicative1
  in (FrexSetoid a s).equivalence.relation
       (i0 *. (is .*. js))
       ((i0 *. is) .*. js)
multMultAssociative a s i0 (Ultimate i1   ) js = multAssociative a s i0 i1 js
multMultAssociative a s i0 (ConsUlt i1 x is) js =  (FrexSetoid a s).equivalence.reflexive _

----------------------------- append properties
public export
appendUnitLftNeutral : (a : Monoid) -> (s : Setoid) -> (is : FrexCarrier a s) ->
  let %hint
      notation : MAction1 (U a) (FrexCarrier a s)
      notation = cast $ MonAction a s
  in (FrexSetoid a s).equivalence.relation
    (I1 .*. is)
    is
appendUnitLftNeutral a s is = multUnitNeutral a s is

public export
appendUnitRgtNeutral : (a : Monoid) -> (s : Setoid) -> (is : FrexCarrier a s) ->
  let %hint
      notation : MAction1 (U a) (FrexCarrier a s)
      notation = cast $ MonAction a s
  in (FrexSetoid a s).equivalence.relation
    (is .*. I1)
    is
appendUnitRgtNeutral a s (Ultimate i) = Ultimate $ a.validate RgtNeutrality [_]
appendUnitRgtNeutral a s (ConsUlt i x is) = 
  ( a.equivalence.reflexive i
  , s.equivalence.reflexive x
  ) :: appendUnitRgtNeutral a s is

public export
appendAssociative : (a : Monoid) -> (s : Setoid) -> (is,js,ks : FrexCarrier a s) ->
  let %hint
      notation : MAction1 (U a) (FrexCarrier a s)
      notation = cast $ MonAction a s
  in (FrexSetoid a s).equivalence.relation
    (is .*. (js .*. ks))
    ((is .*. js) .*. ks)
appendAssociative a s (Ultimate i) js ks = multMultAssociative a s i js ks
appendAssociative a s (ConsUlt i x is) js ks = 
  ( a.equivalence.reflexive _
  , s.equivalence.reflexive _
  ) :: appendAssociative a s is js ks

-----------------------------------------------------------------

public export
FrexValidatesAxioms : (a : Monoid) -> (s : Setoid) -> Validates MonoidTheory (FrexStructure a s)
FrexValidatesAxioms a s LftNeutrality env = appendUnitLftNeutral a s (env 0)
FrexValidatesAxioms a s RgtNeutrality env = appendUnitRgtNeutral a s (env 0)
FrexValidatesAxioms a s Associativity env = appendAssociative    a s (env 0) (env 1) (env 2)

public export
FrexMonoid : (a : Monoid) -> (s : Setoid) -> Monoid
FrexMonoid a s = MkModel 
  { Algebra = FrexStructure a s
  , Validate = FrexValidatesAxioms a s
  }
