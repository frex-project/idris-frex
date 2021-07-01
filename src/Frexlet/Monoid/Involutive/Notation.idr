||| Notation for working with involutive monoids (mostly boilerplate)
module Frexlet.Monoid.Involutive.Notation

import Frex
import Frex.Free.Construction

import Frexlet.Monoid.Theory
import Frexlet.Monoid.Involutive.Theory

import Notation.Multiplicative
import Frexlet.Monoid.Notation

%default total

public export
interface Involutive a where
  constructor MkInvolutive
  (.inv) : a -> a

public export
(.Involutive) : (monoid : InvolutiveMonoid) -> Involutive (U monoid)
monoid.Involutive = MkInvolutive (monoid.sem Involution)

%hint
public export
fstInvulotive : (Involutive a, _) -> Involutive a
fstInvulotive = fst

%hint
public export
sndInvolutive : (_, Involutive a) -> Involutive a
sndInvolutive = snd

public export
InvMult1 : (a : Type) -> Type
InvMult1 a = (Involutive a , Multiplicative1 a)

public export
InvMult2 : (a : Type) -> Type
InvMult2 a = (Involutive a , Multiplicative2 a)

public export
InvMult3 : (a : Type) -> Type
InvMult3 a = (Involutive a , Multiplicative3 a)

public export
(.Notation1) : (monoid : InvolutiveMonoid) -> InvMult1 (U monoid)
(.Notation1) monoid = (monoid.Involutive, (cast monoid).Multiplicative1)

public export
(.Notation2) : (monoid : InvolutiveMonoid) -> InvMult2 (U monoid)
(.Notation2) monoid = (monoid.Involutive, (cast monoid).Multiplicative2)

public export
(.Notation3) : (monoid : InvolutiveMonoid) -> InvMult3 (U monoid)
(.Notation3) monoid = (monoid.Involutive, (cast monoid).Multiplicative3)

public export
notationSyntax : Involutive (Term (InvolutiveMonoidTheory).signature x)
notationSyntax = MkInvolutive
  (call {sig = (InvolutiveMonoidTheory).signature} Involution)

%hint
public export
notation1 : InvMult1 (Term (InvolutiveMonoidTheory).signature (a `Either` (Fin n)))
notation1 = (notationSyntax, MkMultiplicative1
              (call {sig = (InvolutiveMonoidTheory).signature} $ Mono Neutral)
              (call {sig = (InvolutiveMonoidTheory).signature} $ Mono Product))
