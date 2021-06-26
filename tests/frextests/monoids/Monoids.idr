module Main

import Data.Nat
import Frex
import Frex.Free.Construction
import Frexlet.Monoid
import Frexlet.Monoid.Frex.Construction
import Frexlet.Monoid.Frex.Properties
import Frexlet.Monoid.Frex.Structure
import Frexlet.Monoid.Nat
-- import Frexlet.Monoid.Notation

x1 : Term sig (Either a (Fin (S n)))
x1 = Done (Right FZ)

x2 : Term sig (Either a (Fin (S (S n))))
x2 = Done (Right (FS FZ))

x3 : Term sig (Either a (Fin (S (S (S n)))))
x3 = Done (Right (FS (FS FZ)))

sta : a -> Term sig (Either a n)
sta x = Done (Left x)

(+.) : Term Signature a -> Term Signature a -> Term Signature a
(+.) x y = Call (MkOp Product) [x, y]

trivial : {a : Nat} -> a = a
trivial = frexify {pres=MonoidTheory} {prf= ConsUlt Refl Refl (Ultimate Refl) }
            (MonoidFrex Additive _)
             [a]
            (x1, x1)

trivial2 : {a, b : Nat} -> a + b = a + b
trivial2 = frexify {pres=MonoidTheory}
            {prf= ConsUlt Refl Refl (ConsUlt Refl Refl (Ultimate Refl)) }
            (MonoidFrex Additive _)
             [a, b]
            (x1 +. x2, x1 +. x2)

assoc : {a, b, c : Nat} -> a + (b + c) = (a + b) + c
assoc = frexify {pres=MonoidTheory}
          {prf= ConsUlt Refl Refl (ConsUlt Refl Refl (ConsUlt Refl Refl (Ultimate Refl))) }
          (MonoidFrex Additive _)
           [a, b, c]
          (x1 +. (x2 +. x3), (x1 +. x2) +. x3)

rassoc : {a, b, c : Nat} -> (a + b) + c = a + (b + c)
rassoc = frexify {pres=MonoidTheory}
          {prf= ConsUlt Refl Refl (ConsUlt Refl Refl (ConsUlt Refl Refl (Ultimate Refl))) }
          (MonoidFrex Additive _)
           [a, b, c]
          ((x1 +. x2) +. x3, x1 +. (x2 +. x3))

mixed : {a, b : Nat} -> (a + 1) + (1 + b) = (a + 2 + b)
mixed = frexify {pres=MonoidTheory}
          {prf= ConsUlt Refl Refl (ConsUlt Refl Refl (Ultimate Refl)) }
          (MonoidFrex Additive _)
           [a, b]
          ((x1 +. sta 1) +. (sta 1 +. x2), x1 +. sta 2 +. x2)

main : IO Builtin.Unit
main = do putStrLn "ok"

