||| A type is semantic w.r.t. two other types if it can interpret one type as another
module Notation.Semantic

%default total

public export
interface Semantic a b where
  0 (.SemType) : a -> b -> Type
  (.Sem) : (x : a) -> (y : b) -> x.SemType y
