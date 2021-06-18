||| Definitions and functions dealing with single-sorted finitary signatures
module Frex.Signature

||| A single-sorted finitary signature
public export
record Signature where
  constructor MkSignature
  OpWithArity : Nat -> Type


public export
record Op (Sig : Signature) where
  constructor MkOp
  {fst : Nat}
  snd : (Sig).OpWithArity fst

public export
arity : {auto 0 sig : Signature} -> Op sig -> Nat
arity = fst
