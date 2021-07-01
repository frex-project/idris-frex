module NatTests

import Frex
import Frexlet.Monoid
import Frexlet.Monoid.Notation.Additive

trivial : {a : Nat} -> a = a
trivial = solve 1 (MonoidFrex Additive _)
        $ Dyn 0 =-= Dyn 0

trivial2 : {a, b : Nat} -> a + b = a + b
trivial2 = solve 2 (MonoidFrex Additive _)
         $ Dyn 0 .+. Dyn 1 =-= Dyn 0 .+. Dyn 1

assoc : {a, b, c : Nat} -> a + (b + c) = (a + b) + c
assoc = solve 3 (MonoidFrex Additive _)
      $ Dyn 0 .+. (Dyn 1 .+. Dyn 2) =-= (Dyn 0 .+. Dyn 1) .+. Dyn 2

rassoc : {a, b, c : Nat} -> (a + b) + c = a + (b + c)
rassoc = solve 3 (MonoidFrex Additive _)
       $ (Dyn 0 .+. Dyn 1) .+. Dyn 2 =-= Dyn 0 .+. (Dyn 1 .+. Dyn 2)

mixed : {a, b : Nat} -> (a + 1) + (1 + b) = (a + 2 + b)
mixed = solve 2 (MonoidFrex Additive _)
      $ (Dyn 0 .+. Sta 1) .+. (Sta 1 .+. Dyn 1) =-= Dyn 0 .+. Sta 2 .+. Dyn 1

units : {a, b : Nat} -> (0 + (a + 0)) + 0 = a
units = solve 1 (MonoidFrex Additive _)
        $ (O1 .+. (Dyn 0 .+. O1)) .+. O1 =-= Dyn 0
