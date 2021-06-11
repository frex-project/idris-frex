||| Definitions and functions dealing with single-sorted finitary signatures
module Frex.Signature

||| A single-sorted finitary signature
public export
record Signature where
  constructor MkSignature
  OpWithArity : Nat -> Type


public export
Op : Signature -> Type
Op sig = (n : Nat ** sig.OpWithArity n)

public export
arity : {auto 0 sig : Signature} -> Op sig -> Nat
arity = fst

public export
MkOp : {0 sig : Signature} -> {n : Nat} -> (op : sig.OpWithArity n) -> Op sig
MkOp {n} op = (n ** op)
