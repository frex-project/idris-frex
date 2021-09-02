module Data.Relation.Closure.ReflexiveTransitive

import Data.Maybe
import Data.Relation
import Decidable.Equality
import Data.SnocList
import Data.SortedMap.Dependent

%default total

public export
data RTList : Rel a -> Rel a where
  Nil  : RTList r x x
  (::) : {0 r : Rel a} -> {y : a} -> r x y -> RTList r y z -> RTList r x z

public export
data SnocRTList : Rel a -> Rel a where
  Lin  : SnocRTList r x x
  (:<) : {0 r : Rel a} -> {y : a} -> SnocRTList r x y -> r y z -> SnocRTList r x z

export
(<>>) : {y : a} -> SnocRTList r x y -> RTList r y z -> RTList r x z
[<]       <>> acc = acc
(rs :< r) <>> acc = rs <>> r :: acc

export
reflexive : (===) ~> RTList r
reflexive Refl = []

export
(++) : RTList r x y -> RTList r y z -> RTList r x z
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys

export
concat : RTList (RTList r) ~> RTList r
concat [] = []
concat (xs :: xss) = xs ++ concat xss

export
gmap : (f : a -> b) -> p ~> (q `on` f) -> RTList p ~> (RTList q `on` f)
gmap _ f [] = []
gmap _ f (x :: xs) = f x :: gmap _ f xs

export
map : (p ~> q) -> RTList p ~> RTList q
map = gmap id

export
reverseAcc : {y : a} -> (r ~> flip s) ->
             flip (RTList s) x y -> RTList r y z ->
             flip (RTList s) x z
reverseAcc f acc [] = acc
reverseAcc f acc (x :: xs) = reverseAcc f (f x :: acc) xs

export
reverse : (r ~> flip s) -> RTList r ~> flip (RTList s)
reverse f = reverseAcc f []

||| Deloop detects whenever a proof forms a loop, and removes it e.g.
|||
|||         x7 <-r- x6 <-r- x5
|||         |               ^
|||         r               r
|||         v               |
||| x1 -r-> x2 -r-> x3 -r-> x4 -r-> x8
|||
||| becomes
|||
||| x1 -r-> x2 -r-> x3 -r-> x4 -r-> x8

export
deloop : (Ord a, DecEq a) => RTList {a} r ~> RTList r
deloop = go (singleton x [<]) where

  alreadySeen : SortedDMap a v -> (k : a) -> v k
  alreadySeen acc k = case lookupPrecise k acc of
    Just val => val
    Nothing  => assert_total
              $ idris_crash "The IMPOSSIBLE has happened in deloop"

  -- Invariant: the accumulator already contains (the shortest) subproof
  -- that `RTList r begin middle` holds
  go : {begin, middle, end : a} ->
       SortedDMap a (SnocRTList r begin) ->
       RTList r middle end -> RTList r begin end
  go acc [] = alreadySeen acc middle <>> []
  go acc ((r :: rs) {y = nextMiddle}) = case lookupPrecise nextMiddle acc of
    -- we have a hit: we already know how to prove this!
    Just {} => go acc rs
    -- we don't have a hit: we need to record a proof!
    Nothing =>
      let prf = alreadySeen acc middle :< r in
      go (insert nextMiddle prf acc) rs
