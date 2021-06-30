module NatTests

import Frex
import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Notation.Core

commut : {a, b : Nat} -> a + b = b + a
commut = solve 2 (Frex Additive)
           {prf = (Refl, ByAxiom Commutativity (flip index [_,_]))}
      $ Dyn 0 .+. Dyn 1 =-= Dyn 1 .+. Dyn 0

assoc : {a, b, c : Nat} -> a + (b + c) = (a + b) + c
assoc = solve 3 (Frex Additive)
           {prf = (Refl, ByAxiom (Mon Associativity) (flip index [_,_,_]))}
      $ Dyn 0 .+. (Dyn 1 .+. Dyn 2) =-= (Dyn 0 .+. Dyn 1) .+. Dyn 2

shuffle : {a, b, c : Nat} -> a + (b + c) = c + (a + b)
shuffle = solve 3 (Frex Additive)
           {prf = (Refl, Transitive
                            (ByAxiom (Mon Associativity) (flip index [_,_,_]))
                            (ByAxiom Commutativity (flip index [_,_])))}
      $ Dyn 0 .+. (Dyn 1 .+. Dyn 2) =-= Dyn 2 .+. (Dyn 0 .+. Dyn 1)
