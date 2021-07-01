module ListTests

import Frex
import Frexlet.Monoid.Involutive
import Frexlet.Monoid.Involutive.Notation
import Frexlet.Monoid.Notation.Multiplicative

inv : Term (Frexlet.Monoid.Involutive.Theory.Signature) a -> Term (Frexlet.Monoid.Involutive.Theory.Signature) a
inv x = Call (MkOp Involution) [x]

test : {A : Setoid} -> {x,y : List (U A)} -> A .ListEquality (reverse (reverse y ++ ([] ++ reverse x)))
                                                             (x ++ y)
test = frexify (Frexlet.Monoid.Involutive.Frex.Frex List _) [x,y]
         { prf = ConsUlt (A .ListEqualityReflexive _) (MkAnd Refl Refl) $
                 ConsUlt (A .ListEqualityReflexive _) (MkAnd Refl Refl) $ Ultimate (A .ListEqualityReflexive _) }
         $ (((Dyn 1) .inv .*. (I1 .*. (Dyn 0) .inv)) .inv)
            =-=
           (Dyn 0 .*. Dyn 1)


