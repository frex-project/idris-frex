module MagicNatTests

import Frex
import Frex.Magic
import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Nat

%language ElabReflection

namespace Commut -- TODO remove when hole names are no longer leaked
  commut : {a, b : Nat} -> a + b = b + a
  commut = %runElab frexMagic Monoid.Commutative.Frex Nat.Additive

namespace Assoc -- TODO remove when hole names are no longer leaked
  assoc : {a, b, c : Nat} -> a + (b + c) = (a + b) + c
  assoc = %runElab frexMagic Monoid.Commutative.Frex Nat.Additive

namespace Shuffle -- TODO remove when hole names are no longer leaked
  shuffle : {a, b, c : Nat} -> a + (b + c) = c + (a + b)
  shuffle = %runElab frexMagic Monoid.Commutative.Frex Nat.Additive

-- plusSuccRightSucc : (n, m : Nat) -> n + S m = S (n + m)
-- plusSuccRightSucc n m = %runElab frexMagic Monoid.Commutative.Frex Nat.Additive
