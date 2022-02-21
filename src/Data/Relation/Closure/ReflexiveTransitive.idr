module Data.Relation.Closure.ReflexiveTransitive

import Data.Relation
import Decidable.Equality
import Data.SnocList -- only for the (<>>) fixity declaration
import Data.SortedMap.Dependent

%default total

public export
data RTList : Rel a -> Rel a where
  Nil  : RTList r x x
  (::) : {0 r : Rel a} -> {y : a}
         -> r x y -> RTList r y z
         -> RTList r x z

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
deloop = go {begin = x} (singleton x (0, [<])) (0, [<]) where

  -- Invariant: the accumulator contains the shortest subproofs for all
  -- of the values encountered on the way to middle.
  -- The candidate witnesses the fact that we always have a proof for the
  -- path we've already trodden from begin to middle. It is the shortest
  -- currently known such proof.
  go : {begin, middle, end : a} ->
       SortedDMap a (\ end => (Nat, SnocRTList r begin end)) ->
       (Nat, SnocRTList r begin middle) ->
       RTList r middle end -> RTList r begin end
  go _ (_, prf) [] = prf <>> []
  go acc (n, nprf) ((r :: rs) {y = nextMiddle}) =
    let snprf := (S n, nprf :< r) in
    case lookupPrecise nextMiddle acc of
      -- We have a hit: is it a smaller proof?
      -- We may have taken a different, shorter, path this time!
      Just (m, mprf) =>
        ifThenElse (m <= n)
          (go acc (m, mprf) rs)
          (go (insert nextMiddle snprf acc) snprf rs)
      -- No hit: the current candidate is our best bet
      Nothing => go (insert nextMiddle snprf acc) snprf rs
