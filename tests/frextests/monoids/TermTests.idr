module TermTests

import Frex
import Frex.Free.Construction.Combinators

import Notation.Hints

import Frexlet.Monoid
import Frexlet.Monoid.Notation.Additive

%hint
monoidNotation : (a : Monoid) -> NotationHint a Additive1
monoidNotation a = a.notationHint Additive1 a.Additive1

infix 0 ~~
0 (~~) : {auto monoid : Monoid} -> (lhs, rhs : U monoid) -> Type
(~~) = monoid.equivalence.relation

trivial : {monoid : Monoid} -> {a : U monoid} -> a ~~ a
trivial = solve 1 (FreeMonoidOver $ cast $ Fin _) (X 0 =-= X 0)

trivial2 : {monoid : Monoid} -> {a, b : U monoid} ->
           a .+. b  ~~ a .+. b
trivial2 = solve 2 (FreeMonoidOver $ cast $ Fin _)
         $ X 0 .+. X 1 =-= X 0 .+. X 1

assoc : {monoid : Monoid} -> {a, b, c : U monoid} ->
        a .+. (b .+. c) ~~ (a .+. b) .+. c
assoc = solve 3 (FreeMonoidOver (cast $ Fin _))
      $ X 0 .+. (X 1 .+. X 2) =-= (X 0 .+. X 1) .+. X 2

rassoc : {monoid : Monoid} -> {a, b, c : U monoid} ->
         (a .+. b) .+. c ~~ a .+. (b .+. c)
rassoc = solve 3 (FreeMonoidOver (cast $ Fin _))
       $ (X 0 .+. X 1) .+. X 2 =-= X 0 .+. (X 1 .+. X 2)

units : {monoid : Monoid} -> {a : U monoid} ->
        (O1 .+. (a .+. O1)) .+. O1 ~~  a
units = solve 1 (FreeMonoidOver (cast $ Fin 1))
             $ (O1 .+. (X 0 .+. O1)) .+. O1 =-= X 0
