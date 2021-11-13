||| Definitions and functions dealing with single-sorted finitary signatures
module Frex.Signature

import Data.Finite
import Data.Maybe
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
record Op (sig : Signature) where
  constructor MkOp
  {arity : Nat}
  snd : sig.OpWithArity arity

public export
data Precedence : Nat -> Type where
  Prefix : Nat -> Precedence 1
  InfixL : Nat -> Precedence 2
  InfixR : Nat -> Precedence 2

namespace Precedence

  export
  isInfix : Precedence n -> Bool
  isInfix (Prefix _) = False
  isInfix _ = True

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
             {auto 0 eq : arity f = S n} -> Maybe (Precedence (S n))
precedence (MkOp {arity = S _} f) {eq = Refl} = OpPrecedence f

export
isInfix : HasPrecedence sig => Op sig -> Bool
isInfix (MkOp {arity = S _} f) = maybe False isInfix (OpPrecedence f)
isInfix _ = False

public export
record Printer (sig : Signature) (a : Type) where
  constructor MkPrinter
  ||| Printing the carrier type
  carrier    : String
  ||| Variable printing
  varShow    : Show a
  ||| Patterns for operators
  opPatterns : Show (Op sig)
  ||| Operator printing
  opShow     : Show (Op sig)
  ||| Operator precedences
  opPrec     : HasPrecedence sig
  ||| Should all infix operators be wrapped in parens
  opParens   : Bool
  ||| Should we wrap a term in parens at the toplevel
  topParens  : Bool

||| The modified names we are using when printing a context rather than
||| a term (i.e. a term with an extra variable in scope: the focus).
export
withQuoted : Printer sig a -> Printer sig a
withQuoted p = { opShow := opShow } p where

  [opShow] Show (Op sig) where
    showPrec d op =
      ifThenElse (isInfix @{p.opPrec} op)
        (":" ++ show @{p.opShow} op)
        (show @{p.opShow} op ++ "'")

namespace Operators

  export
  display : Printer sig () ->
            Op sig -> Doc ()
  display p op@(MkOp {arity = 0} _)
      = hsep [ pretty (show @{p.opShow} op)
             , ":", pretty p.carrier
             ]
  display p op@(MkOp {arity = n@(S _)} _)
      = hsep [ parenthesise (isJust (precedence @{p.opPrec} op))
                    $ pretty $ show @{p.opShow} op
             , ":", pretty (unwords (nary n))]

    where

    nary : Nat -> List String
    nary Z = [p.carrier]
    nary (S n) = p.carrier :: "->" :: nary n

namespace Precedence

  export
  display : Printer sig () -> Op sig -> Maybe (Doc ())
  display p (MkOp {arity = 0} _) = Nothing
  display p op@(MkOp {arity = S _} _)
      = case precedence @{p.opPrec} op of
            Nothing => Nothing
            Just prec => pure (pretty (show prec))

namespace Signature

  export
  display : (sig : Signature) ->
            Finite (Op sig) =>
            Printer sig () -> Doc ()
  display sig p = vcat $ enumerate <&> \ op =>
    hsep $ display p op :: toList (parens <$> display p op)
