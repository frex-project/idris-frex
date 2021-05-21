module Syntax.TransitiveReasoning

infixl 0  ~~
infixl 0  <~
prefix 1  |~
infix  1  ...

public export
interface Transitive a (0 leq : a -> a -> Type) where
  constructor MkTransitive
  transitive : (x, y, z : a) -> x `leq` y  -> y `leq` z -> x `leq` z

public export
data Step : (leq : a -> a -> Type) -> a -> a -> Type where
  (...) : (y : a) -> x `leq` y -> Step leq x y

namespace Workaround
  public export
  (<~) : (x : a) -> (step : Step leq x y) -> (x : a ** Step leq x y)
  (<~) x step = (x ** step)

public export
data FastDerivation : (leq : a -> a -> Type) -> (x : a) -> (y : a) -> Type where
  (|~) : (xstep : (x : a ** Step leq x y)) -> FastDerivation leq (xstep.fst) y
  (<~) : {x, y : a}
         -> FastDerivation leq x y -> {z : a} -> (step : Step leq y z)
         -> FastDerivation leq x z

public export
CalcWith : Transitive dom leq => {0 x : dom} -> {0 y : dom} -> FastDerivation leq x y -> x `leq` y
CalcWith (|~ (x ** (...) {x = x} y reason)) = reason
CalcWith ((<~) der (z ... step)) = transitive {leq} _ _ _ (CalcWith der) step

public export
(~~) : {0 x : dom} -> {0 y : dom}
         -> FastDerivation leq x y -> {z : dom} -> (step : Step Equal y z)
         -> FastDerivation leq x z
(~~) der (z ... Refl) = der
