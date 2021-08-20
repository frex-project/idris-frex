module NatTests

import Frex
import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Notation.Core
import Frexlet.Monoid.Commutative.Nat

commut : {a, b : Nat} -> a + b = b + a
commut = Frex.solve 2 (Monoid.Commutative.Frex Nat.Additive)
      $ Dyn 0 .+. Dyn 1 =-= Dyn 1 .+. Dyn 0

assoc : {a, b, c : Nat} -> a + (b + c) = (a + b) + c
assoc = solve 3 (Monoid.Commutative.Frex Nat.Additive)
      $ Dyn 0 .+. (Dyn 1 .+. Dyn 2) =-= (Dyn 0 .+. Dyn 1) .+. Dyn 2

shuffle : {a, b, c : Nat} -> a + (b + c) = c + (a + b)
shuffle = solve 3 (Monoid.Commutative.Frex Nat.Additive)
      $ Dyn 0 .+. (Dyn 1 .+. Dyn 2) =-= Dyn 2 .+. (Dyn 0 .+. Dyn 1)

plusSuccRightSucc : (n, m : Nat) -> n + S m = S (n + m)
plusSuccRightSucc n m = solve 2 (Monoid.Commutative.Frex Nat.Additive)
  $ Dyn 0 .+. (Sta 1 .+. Dyn 1) =-= Sta 1 .+. (Dyn 0 .+. Dyn 1)

simplify : (n, m, k : Nat) -> (n + 6) + (k + n) + (m + 2) = k + 2*n + m + 8
simplify n m k = solve 3 (Monoid.Commutative.Frex Nat.Additive)
      $ (Dyn 0 .+. Sta 6) .+. (Dyn 1 .+. Dyn 0) .+. (Dyn 2 .+. Sta 2) =-=
      Dyn 1 .+. ((the Nat 2) *. Dyn 0) .+. Dyn 2 .+. Sta 8
