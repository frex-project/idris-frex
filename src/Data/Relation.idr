module Data.Relation

%default total

public export
0 Rel : Type -> Type
Rel a = a -> a -> Type

export infix 5 ~>
public export
0 (~>) : Rel a -> Rel a -> Type
p ~> q = {x, y : a} -> p x y -> q x y
