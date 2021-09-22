||| Definitions and functions dealing with single-sorted finitary signatures
module Frex.Signature

import Data.Finite
import Data.String
import Text.PrettyPrint.Prettyprinter

%default total

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
Show (Precedence n) where
  show (Prefix lvl) = "prefix " ++ show lvl
  show (InfixL lvl) = "infixl " ++ show lvl
  show (InfixR lvl) = "infixr " ++ show lvl

export
level : Precedence n -> Nat
level (Prefix lvl) = lvl
level (InfixL lvl) = lvl
level (InfixR lvl) = lvl

public export
interface HasPrecedence (0 sig : Signature) where
  OpPrecedence : {0 n : Nat} -> (f : sig.OpWithArity (S n)) ->
                 Maybe (Precedence (S n))

export
precedence : HasPrecedence sig => (f : Op sig) ->
             {auto 0 eq : arity @{sig} f = S n} -> Maybe (Precedence (S n))
precedence (MkOp {fst = S _} f) {eq = Refl} = OpPrecedence f


export
display :
  (sig : Signature) ->
  (Finite (Op sig), HasPrecedence sig, Show (Op sig)) =>
  Doc ()
display sig = vcat $ map showOp enumerate where

  nary : Nat -> List String
  nary Z = ["a"]
  nary (S n) = "a" :: "->" :: nary n

  showOp : Op sig -> Doc ()
  showOp op@(MkOp {fst = 0} _) = hsep [pretty (show op), ": a"]
  showOp op@(MkOp {fst = n@(S _)} _) =
    let base = [ parenthesise (n == 2) (pretty $ show op)
               , ":", pretty (unwords (nary n))]
    in case precedence op of
      Nothing   => hsep base
      Just prec => hsep (base ++ [parens (pretty $ show prec)])
