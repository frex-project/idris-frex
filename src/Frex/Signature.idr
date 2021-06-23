||| Definitions and functions dealing with single-sorted finitary signatures
module Frex.Signature

||| A single-sorted finitary signature
public export
record Signature where
  constructor MkSignature
  ||| Type family of operators indexed by their arity.
  OpWithArity : Nat -> Type

public export
record Op (Sig : Signature) where
  constructor MkOp
  {fst : Nat}
  snd : (Sig).OpWithArity fst

public export
arity : {auto 0 sig : Signature} -> Op sig -> Nat
arity = fst

public export
data Precedence : Nat -> Type where
  Prefix : Nat -> Precedence 1
  InfixL : Nat -> Precedence 2
  InfixR : Nat -> Precedence 2

export
level : Precedence n -> Nat
level (Prefix lvl) = lvl
level (InfixL lvl) = lvl
level (InfixR lvl) = lvl

public export
interface HasPrecedence (0 sig : Signature) where
  OpPrecedence : (f : sig.OpWithArity (S n)) -> Maybe (Precedence (S n))

export
precedence : HasPrecedence sig => (f : Op sig) ->
             {auto 0 eq : arity @{sig} f = S n} -> Maybe (Precedence (S n))
precedence (MkOp {fst = S _} f) {eq = Refl} = OpPrecedence f
