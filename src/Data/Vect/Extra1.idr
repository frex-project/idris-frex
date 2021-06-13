||| Move these to stdlib Data.Vect.Extra
module Data.Vect.Extra1

import Data.Vect
import Data.Fin
import Data.Vect.Elem
import Data.Vect.Extra
import Data.Vect.Properties

import Syntax.PreorderReasoning

export
mapWithPosTabulate : {n : Nat} -> (f : Fin n -> a -> b) -> (x : a) ->
  mapWithPos f (replicate n x) = tabulate (flip f x) 
mapWithPosTabulate {n = 0  } f x = Refl
mapWithPosTabulate {n = S n} f x = Calc $
  |~ mapWithPos f (replicate (1 + n) x)
  ~~ f FZ x :: mapWithPos (\i => f (FS i)) (replicate n x) ...(Refl)
  ~~ flip f x FZ :: tabulate (flip (\i => f (FS i)) x)     ...(cong (flip f x FZ ::) $ 
                                                               mapWithPosTabulate {n} 
                                                               (\ i => f (FS i)) x)
  ~~ tabulate (flip f x) ...(Refl)

export
mapWithPosAsTabulate : {n : Nat} -> (f : Fin n -> a -> b) -> (xs : Vect n a) -> 
  mapWithPos f xs = tabulate \i => f i (index i xs)
mapWithPosAsTabulate f xs = vectorExtensionality _ _ $ \i => Calc $
  |~ index i (mapWithPos f xs)
  ~~ f i (index i xs)                          ...(indexMapWithPos _ _ _)
  ~~ index i (tabulate \j => f j (index j xs)) ...(sym $ indexTabulate _ _)

-- Currently not used
||| Version of `map` with runtime-irrelevant access to the current position
public export
mapWithPosIrrelevant : (f : (0 i : Fin n) -> a -> b) -> Vect n a -> Vect n b
mapWithPosIrrelevant f [] = []
mapWithPosIrrelevant f (x :: xs) = f 0 x :: mapWithPosIrrelevant (\i => f (FS i)) xs

export
mapWithPosFusion : forall n, a, b, c. (f : Fin n -> b -> c) -> (g : a -> b) -> (xs : Vect n a) ->
  mapWithPos f (map g xs) = mapWithPos (\i => f i . g) xs                                        
mapWithPosFusion f g    []     = Refl
mapWithPosFusion f g (x :: xs) = Calc $
  |~ mapWithPos f (map g (x :: xs))
  ~~ f 0 (g x) :: mapWithPos (f . FS) (map g xs)     ...(Refl)
  ~~ f 0 (g x) :: mapWithPos (\i => f (FS i) . g) xs ...(cong (f 0 (g x) ::) $ mapWithPosFusion _ _ _)
  ~~ mapWithPos (\i => f i . g) (x :: xs)            ...(Refl)
