module MagicPairTests

import Frex.Magic
import Frexlet.Monoid

%language ElabReflection

{-
assoc : {a, b : Setoid} -> Pair a b <~> Pair a b
assoc = %runElab frexMagic MonoidFrexlet MonoidPair

assoc4 : {a, b, c, d : Setoid} -> Pair (Pair a (Pair b c)) d <~> Pair a (Pair b (Pair c d))
assoc4 = %runElab frexMagic MonoidFrexlet MonoidPair

unitl : {a : Setoid} -> Pair Unit a <~> a
unitl = %runElab frexMagic MonoidFrexlet MonoidPair

unitr : {a : Setoid} -> Pair a Unit <~> a
unitr = %runElab frexMagic MonoidFrexlet MonoidPair

units : {a : Setoid} -> Pair (Pair Unit (Pair a Unit)) Unit <~> a
units = %runElab frexMagic MonoidFrexlet MonoidPair
-}
