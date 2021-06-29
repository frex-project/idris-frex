module PairTests

import Data.Setoid.Pair
import Frex
import Frexlet.Monoid
import Frexlet.Monoid.Frex.Construction
import Frexlet.Monoid.Frex.Properties
import Frexlet.Monoid.Frex.Structure
import Frexlet.Monoid.Pair

(*.) : Term Signature a -> Term Signature a -> Term Signature a
(*.) x y = Call (MkOp Product) [x, y]

assoc : {a, b, c : Setoid} -> Pair a (Pair b c) <~> Pair (Pair a b) c
assoc = frexify (MonoidFrex MonoidPair _) [a, b, c]
          (Dyn 0 *. (Dyn 1 *. Dyn 2), (Dyn 0 *. Dyn 1) *. Dyn 2)

assoc4 : {a, b, c, d : Setoid} -> Pair (Pair a (Pair b c)) d <~> Pair a (Pair b (Pair c d))
assoc4 = frexify (MonoidFrex MonoidPair _) [a, b, c, d]
           ((Dyn 0 *. (Dyn 1 *. Dyn 2)) *. Dyn 3,
            Dyn 0 *. (Dyn 1 *. (Dyn 2 *. Dyn 3)))
