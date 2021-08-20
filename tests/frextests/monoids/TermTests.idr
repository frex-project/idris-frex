module TermTests

import Frex
import Frex.Free.Construction.Combinators

import Notation.Hints

import Frexlet.Monoid
import Frexlet.Monoid.Notation.Additive

%hint
notationAdd2 : Additive2 (Term Signature a)
notationAdd2= MkAdditive2
              (call {sig = Signature} Neutral)
              (call {sig = Signature} Product)

%hint
monoidNotation : (a : Monoid) -> NotationHint a Additive2
monoidNotation a = notationHint Additive2 a.Additive2

infix 0 ~~
0 (~~) : {auto monoid : Monoid} -> (lhs, rhs : U monoid) -> Type
(~~) = monoid.equivalence.relation

trivial : {monoid : Monoid} -> {a : U monoid} -> a ~~ a
trivial = solve 1 (FreeMonoidOver $ cast $ Fin _) (X 0 =-= X 0)

trivial2 : {monoid : Monoid} -> {a, b : U monoid} ->
           a :+: b  ~~ a :+: b
trivial2 = solve 2 (FreeMonoidOver $ cast $ Fin _)
         $ X 0 :+: X 1 =-= X 0 :+: X 1

assoc : {monoid : Monoid} -> {a, b, c : U monoid} ->
        a :+: (b :+: c) ~~ (a :+: b) :+: c
assoc = solve 3 (FreeMonoidOver (cast $ Fin _))
      $ X 0 :+: (X 1 :+: X 2) =-= (X 0 :+: X 1) :+: X 2

rassoc : {monoid : Monoid} -> {a, b, c : U monoid} ->
         (a :+: b) :+: c ~~ a :+: (b :+: c)
rassoc = solve 3 (FreeMonoidOver (cast $ Fin _))
       $ (X 0 :+: X 1) :+: X 2 =-= X 0 :+: (X 1 :+: X 2)

units : {monoid : Monoid} -> {a : U monoid} ->
        (O2 :+: (a :+: O2)) :+: O2 ~~  a
units = solve 1 (FreeMonoidOver (cast $ Fin 1))
             $ (O2 :+: (X 0 :+: O2)) :+: O2 =-= X 0
