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

unitl : {a : Setoid} -> Pair Unit a <~> a
unitl = solve 1 (MonoidFrex MonoidPair _)
         { prf = ConsUlt leftNeut Refl $ Ultimate refl }
        $ I1 .*. Dyn 0 =-= Dyn 0

unitr : {a : Setoid} -> Pair a Unit <~> a
unitr = solve 1 (MonoidFrex MonoidPair _)
         { prf = ConsUlt refl Refl $ Ultimate rightNeut }
        $ Dyn 0 .*. I1 =-= Dyn 0

units : {a : Setoid} -> Pair (Pair Unit (Pair a Unit)) Unit <~> a
units = solve 1 (MonoidFrex MonoidPair _)
         { prf = ConsUlt leftNeut Refl $ Ultimate (trans rightNeut rightNeut) }
        $ (I1 .*. (Dyn 0 .*. I1)) .*. I1 =-= Dyn 0
