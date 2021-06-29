module Data.Fun.Nary

import Data.Vect

public export
data Visibility = Visible | Hidden | Auto

public export
Pi : Visibility -> (a : Type) -> (a -> Type) -> Type
Pi Visible a b = (x : a) -> b x
Pi Hidden  a b = {x : a} -> b x
Pi Auto    a b = {auto x : a} -> b x

public export
lam : (vis : Visibility) -> (0 b : a -> Type) ->
      ((x : a) -> b x) -> Pi vis a b
lam Visible b f = f
lam Hidden  b f = f _
lam Auto    b f = f %search

public export
app : (vis : Visibility) -> (0 b : a -> Type) ->
      Pi vis a b -> ((x : a) -> b x)
app Visible b f x = f x
app Hidden  b f x = f
app Auto    b f x = f

public export
PI : (n : Nat) -> Visibility -> (a : Type) -> (Vect n a -> Type) -> Type
PI Z     vis a b = b []
PI (S n) vis a b = Pi vis a (\ x => PI n vis a (b . (x ::)))

public export
curry : (n : Nat) -> (vis : Visibility) ->
        (0 b : Vect n a -> Type) ->
        ((as : Vect n a) -> b as) ->
        PI n vis a b
curry 0 vis b f = f []
curry (S n) vis b f
  = lam vis _ $ \ x => curry n vis (b . (x ::)) (\ xs => f (x :: xs))

public export
uncurry : (n : Nat) -> (vis : Visibility) ->
          (0 b : Vect n a -> Type) ->
          PI n vis a b ->
          (as : Vect n a) -> b as
uncurry 0 vis b f [] = f
uncurry (S n) vis b f (x :: xs)
  = uncurry n vis (b . (x ::)) (app vis _ f x) xs
