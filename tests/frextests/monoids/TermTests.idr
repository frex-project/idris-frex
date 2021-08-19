module TermTests

import Frex
import Frex.Free.Construction.Combinators

import Frexlet.Monoid
import Frexlet.Monoid.Notation.Additive

%hint
notationAdd2 : Additive2 (Term Signature a)
notationAdd2= MkAdditive2
              (call {sig = Signature} Neutral)
              (call {sig = Signature} Product)

infix 0 ~~
0 (~~) : {x : Type} -> (lhs, rhs : Term Signature x) -> Type
(~~) = (Free.Construction.Free MonoidTheory (cast x)).Data.Model.rel

trivial : {x : Type} -> {a : Term Signature x} -> a ~~ a
trivial = solve {a = F _ _} 1 (FreeMonoidOver $ cast $ Fin _) (Done 0 =-= Done 0)

trivial2 : {x : Type} -> {a, b : Term Signature x} ->
           a :+: b ~~ a :+: b
trivial2 = solve {a = F _ _} 2 (FreeMonoidOver $ cast $ Fin _)
         $ Done 0 :+: Done 1 =-= Done 0 :+: Done 1

assoc : {x : Type} -> {a, b, c : Term Signature x} ->
        a :+: (b :+: c) ~~ (a :+: b) :+: c
assoc = solve {a = F _ _} 3 (FreeMonoidOver (cast $ Fin _))
      $ Done 0 :+: (Done 1 :+: Done 2) =-= (Done 0 :+: Done 1) :+: Done 2

rassoc : {x : Type} -> {a, b, c : Term Signature x} ->
         (a :+: b) :+: c ~~ a :+: (b :+: c)
rassoc = solve {a = F _ _} 3 (FreeMonoidOver (cast $ Fin _))
       $ (Done 0 :+: Done 1) :+: Done 2 =-= Done 0 :+: (Done 1 :+: Done 2)

units : {x : Type} -> {a : Term Signature x} ->
        (O2 :+: (a :+: O2)) :+: O2 ~~ a
units = solve {a = F _ _} 1 (FreeMonoidOver (cast $ Fin 1))
             $ (O2 :+: (Done 0 :+: O2)) :+: O2 =-= Done 0
