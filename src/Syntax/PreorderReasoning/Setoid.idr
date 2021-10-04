module Syntax.PreorderReasoning.Setoid

import Data.Setoid.Definition
import Control.Relation
import Control.Order
infixl 0  ~~, :~, ~:
prefix 1  |~
infix  1  ...

%default total

public export
data Step : (eq : (x, y : a) -> Type) -> (x, y : a) -> Type where
  (...) : {0 x : a} -> (y : a) ->
          x `eq` y -> Step eq x y

public export
data FastDerivation : (s : Setoid) -> (x, y : s.U) -> Type where
  (|~) : {0 s : Setoid} -> (x : s.U) -> FastDerivation s x x
  (:~) : {x, y : s.U}
         -> FastDerivation s x y -> {z : s.U}
         -> (step : Step s.equivalence.relation y z)
         -> FastDerivation s x z
  (~:) : {x, y : s.U}
         -> FastDerivation s x y -> {z : s.U}
         -> (step : Step (flip s.equivalence.relation) y z)
         -> FastDerivation s x z

public export
CalcWith : (s : Setoid) ->
           {0 x, y : s.U} -> FastDerivation s x y ->
           s.equivalence.relation x y
CalcWith s (|~ x) = s.equivalence.reflexive x
CalcWith s ((:~) der (z ... step))
  = s.equivalence.transitive ? ? ? (CalcWith s der) step
CalcWith s ((~:) der (z ... step))
  = s.equivalence.transitive ? ? ? (CalcWith s der)
  $ s.equivalence.symmetric ? ? step

public export
(~~) : {s : Setoid} -> {0 x, y : s.U}
         -> FastDerivation s x y -> {z : s.U} -> (step : Step Equal y z)
         -> FastDerivation s x z
(~~) der (z ... Refl) = der
