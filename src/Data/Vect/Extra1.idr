||| Move these to stdlib Data.Vect.Extra
module Data.Vect.Extra

import Data.Vect
import Data.Fin
import Data.Vect.Elem

||| Version of `map` with runtime-irrelevant access to the current position
public export
mapWithPosIrrelevant : (f : (0 i : Fin n) -> a -> b) -> Vect n a -> Vect n b
mapWithPosIrrelevant f [] = []
mapWithPosIrrelevant f (x :: xs) = f 0 x :: mapWithPosIrrelevant (\i => f (FS i)) xs

