module Frexlet.Monoid.Free

import Frex
import Frexlet.Monoid.Theory

%default total

public export
Syntactic : Type -> Monoid
Syntactic x = F ? (cast x)
