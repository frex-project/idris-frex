module Data.Finite

%default total

public export
interface Finite (0 a : Type) where
  enumerate : List a
