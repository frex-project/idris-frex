module Data.Relation.Closure.ReflexiveTransitive

import Data.Relation

public export
data RTList : Rel a -> Rel a where
  Nil  : RTList r x x
  (::) : {0 r : Rel a} -> {y : a} -> r x y -> RTList r y z -> RTList r x z

export
reflexive : x === y -> RTList r x y
reflexive Refl = []

export
(++) : RTList r x y -> RTList r y z -> RTList r x z
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys

export
concat : RTList (RTList r) x y -> RTList r x y
concat [] = []
concat (xs :: xss) = xs ++ concat xss

export
map : (p ~> q) -> RTList p ~> RTList q
map f []        = []
map f (x :: xs) = f x :: map f xs

export
reverseAcc : {y : a} -> (r ~> flip s) ->
             flip (RTList s) x y -> RTList r y z ->
             flip (RTList s) x z
reverseAcc f acc []        = acc
reverseAcc f acc (x :: xs) = reverseAcc f (f x :: acc) xs

export
reverse : (r ~> flip s) -> RTList r ~> flip (RTList s)
reverse f = reverseAcc f []
