module Notation

import public Data.Fun

namespace SingleSorted
  public export
  ary : Nat -> (a : Type) -> Type
  0     `ary` a = a
  (S n) `ary` a = a -> n `ary` a

namespace MultiSorted
  ||| Compare with contrib's Data.Fun
  public export
  ary : List Type -> (a : Type) -> Type
  ary [] a = a
  ary (ty :: tys) a = ty -> ary tys a

