{--
  
  Until Idris2 starts supporting the 'syntax' keyword, here's a
  poor-man's equational reasoning
--}
module PreorderReasoning

public export
data Derivation : (0 x : a) -> (0 y : b) -> Type where
  Nil : Derivation x x
  (::) : (x ~=~ y) -> Derivation y z -> Derivation x z
  
infix 1 ==|

public export
(==|) : (0 x : a) -> (pf : x ~=~ y) -> x ~=~ y
(==|) x Refl = Refl

public export
Calculate : Derivation x y -> x ~=~ y
Calculate [] = Refl
Calculate (Refl :: der) = Calculate der

public export
QED : {0 x : a} -> x ~=~ x
QED = Refl

{--
example : (x : Nat) -> (x + 1) + 0 = 1 + x
example x = Calculate [
  (x + 1) + 0 
  ==| plusZeroRightNeutral (x + 1) ,
  x + 1
  ==| plusCommutative x 1 ,
  1 + x  
  ==| QED
  ]
--}
