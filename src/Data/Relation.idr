module Data.Relation

public export
0 Rel : Type -> Type
Rel a = a -> a -> Type

infix 5 ~>
public export
0 (~>) : Rel a -> Rel a -> Type
p ~> q = {x, y : a} -> p x y -> q x y
