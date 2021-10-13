module MagicNatTests

import Frex
import Frex.Magic
import Frexlet.Monoid

%language ElabReflection

trivial : {a : Nat} -> a = a
trivial = %runElab frexMagic MonoidFrexlet Additive

trivial2 : {a, b : Nat} -> a + b = a + b
trivial2 = %runElab frexMagic MonoidFrexlet Additive

assoc : {a, b, c : Nat} -> a + (b + c) = (a + b) + c
assoc = %runElab frexMagic MonoidFrexlet Additive

rassoc : {a, b, c : Nat} -> (a + b) + c = a + (b + c)
rassoc = %runElab frexMagic MonoidFrexlet Additive

-- mixed : {a, b : Nat} -> (a + 1) + (1 + b) = (a + 2 + b)
-- mixed = %runElab frexMagic MonoidFrex Additive

-- units : {a, b : Nat} -> (0 + (a + 0)) + 0 = a
-- units = %runElab frexMagic MonoidFrex Additive
