module Data.Finite

public export
interface Finite (0 a : Type) where
  enumerate : List a
