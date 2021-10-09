||| Like Syntax.PreorderReasoning.Generic, but optimised for setoids
module Syntax.PreorderReasoning.Setoid

import Data.Setoid.Definition

infixl 0  ~~
prefix 1  |~
infix  1  ...,..<,..>,.=.,.=<,.=>

public export
data Step : (a : Setoid) -> (lhs,rhs : U a) -> Type where
  (...) : {0 a : Setoid} -> (0 y : U a) -> {0 x : U a} ->
    a.equivalence.relation x y -> Step a x y

public export
data FastDerivation : (a : Setoid) -> (x, y : U a) -> Type where
  (|~) : {0 a : Setoid} -> (x : U a) -> FastDerivation a x x
  (~~) : {0 a : Setoid} -> {x, y : U a}
         -> FastDerivation a x y -> {z : U a} -> (step : Step a y z)
         -> FastDerivation a x z

public export
CalcWith : (a : Setoid) -> {0 x : U a} -> {0 y : U a} -> FastDerivation a x y ->
  a.equivalence.relation x y
CalcWith a (|~ x) = a.equivalence.reflexive x
CalcWith a ((~~) der (z ... step)) = a.equivalence.transitive _ _ _
    (CalcWith a der) step

-- Smart constructors
public export
(..<) : {a : Setoid} -> (y : U a) -> {x : U a} ->
    a.equivalence.relation y x -> Step a x y
(y ..<(prf)) {x} = (y ...(a.equivalence.symmetric _ _ prf))

public export
(..>) : {0 a : Setoid} -> (0 y : U a) -> {0 x : U a} ->
    a.equivalence.relation x y -> Step a x y
(..>) = (...)

public export
(.=.) : {a : Setoid} -> (y : U a) -> {x : U a} ->
    x === y -> Step a x y
(y .=.(Refl)) = (y ...(a.equivalence.reflexive y))

public export
(.=>) : {a : Setoid} -> (y : U a) -> {x : U a} ->
    x === y -> Step a x y
(.=>) = (.=.)

public export
(.=<) : {a : Setoid} -> (y : U a) -> {x : U a} ->
    y === x -> Step a x y
(y .=<(Refl)) = (y ...(a.equivalence.reflexive y))

