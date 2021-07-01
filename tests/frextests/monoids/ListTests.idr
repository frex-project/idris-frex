module ListTests

import Frex
import Frexlet.Monoid
import Frexlet.Monoid.Notation.Multiplicative
import Data.List

assoc : {A : Setoid} -> {a,b,c : List (U A)} -> A .ListEquality (a ++ (b ++ c)) ((a ++ b) ++ c)
assoc = solve 3 (MonoidFrex (ListMonoid {A=A}) _)
         { prf = ConsUlt (A .ListEqualityReflexive _) Refl $
                 ConsUlt (A .ListEqualityReflexive _) Refl $
                 ConsUlt (A .ListEqualityReflexive _) Refl $ Ultimate (A .ListEqualityReflexive _) }
         $ Dyn 0 .*. (Dyn 1 .*. Dyn 2) =-= (Dyn 0 .*. Dyn 1) .*. Dyn 2

assoc4 : {A : Setoid} -> {a,b,c,d : List (U A)} -> A .ListEquality ((a ++ (b ++ c)) ++ d) (a ++ (b ++ (c ++ d)))
assoc4 = solve 4 (MonoidFrex ListMonoid _)
         { prf = ConsUlt (A .ListEqualityReflexive _) Refl $
                 ConsUlt (A .ListEqualityReflexive _) Refl $
                 ConsUlt (A .ListEqualityReflexive _) Refl $
                 ConsUlt (A .ListEqualityReflexive _) Refl $ Ultimate (A .ListEqualityReflexive _) }
         $ (Dyn 0 .*. (Dyn 1 .*. Dyn 2)) .*. Dyn 3
            =-=
            Dyn 0 .*. (Dyn 1 .*. (Dyn 2 .*. Dyn 3))
