module Main

import Data.Nat
import Frex
import Frex.Free.Construction
import Frexlet.Monoid
import Frexlet.Monoid.Frex.Construction
import Frexlet.Monoid.Frex.Properties
import Frexlet.Monoid.Frex.Structure
import Frexlet.Monoid.Nat

(+.) : Term Signature a -> Term Signature a -> Term Signature a
(+.) x y = Call (MkOp Product) [x, y]

trivial : {a : Nat} -> a = a
trivial = frexify (MonoidFrex Additive _) [a]
            (Dyn 0, Dyn 0)

trivial2 : {a, b : Nat} -> a + b = a + b
trivial2 = frexify (MonoidFrex Additive _) [a, b]
            (Dyn 0 +. Dyn 1, Dyn 0 +. Dyn 1)

assoc : {a, b, c : Nat} -> a + (b + c) = (a + b) + c
assoc = frexify (MonoidFrex Additive _) [a, b, c]
          (Dyn 0 +. (Dyn 1 +. Dyn 2), (Dyn 0 +. Dyn 1) +. Dyn 2)

rassoc : {a, b, c : Nat} -> (a + b) + c = a + (b + c)
rassoc = frexify (MonoidFrex Additive _) [a, b, c]
          ((Dyn 0 +. Dyn 1) +. Dyn 2, Dyn 0 +. (Dyn 1 +. Dyn 2))

mixed : {a, b : Nat} -> (a + 1) + (1 + b) = (a + 2 + b)
mixed = frexify (MonoidFrex Additive _) [a, b]
          ((Dyn 0 +. Sta 1) +. (Sta 1 +. Dyn 1), Dyn 0 +. Sta 2 +. Dyn 1)

main : IO Builtin.Unit
main = do putStrLn "ok"

