||| Definitions and functions dealing with single-sorted finitary signatures
module Frex.Signature

||| A single-sorted finitary signature
public export
record Signature where
  constructor MkSignature
  Op    : Type
  arity : Op -> Nat


