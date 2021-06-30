module PairTests

import Frex
import Frexlet.Monoid
import Frexlet.Monoid.Notation.Multiplicative

assoc : {a, b, c : Setoid} -> Pair a (Pair b c) <~> Pair (Pair a b) c
assoc = solve 3 (MonoidFrex MonoidPair _)
         $ Dyn 0 .*. (Dyn 1 .*. Dyn 2) =-= (Dyn 0 .*. Dyn 1) .*. Dyn 2

assoc4 : {a, b, c, d : Setoid} -> Pair (Pair a (Pair b c)) d <~> Pair a (Pair b (Pair c d))
assoc4 = solve 4 (MonoidFrex MonoidPair _)
         $ (Dyn 0 .*. (Dyn 1 .*. Dyn 2)) .*. Dyn 3
            =-=
            Dyn 0 .*. (Dyn 1 .*. (Dyn 2 .*. Dyn 3))
