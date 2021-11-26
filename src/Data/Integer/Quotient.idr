||| Representation of the integers using the INT-construction on Nat,
||| and quotients. Hopefully it'll be easier to prove its properties
module Data.Integer.Quotient

import public Data.Integer.Quotient.Definition

import Data.Primitives.Views
import Data.Setoid
import Syntax.PreorderReasoning

public export
plus : (x,y : INT) -> INT
plus x y = MkINT
  { pos = x.pos + y.pos
  , neg = x.neg + y.neg
  }

public export
mult : (x,y : INT) -> INT
mult x y = MkINT
  { pos = x.pos*y.pos + x.neg*y.neg
  , neg = x.neg*y.pos + x.pos*y.neg
  }

public export
Num INT where
  fromInteger x = case compare x 0 of
    LT => MkINT {pos = 0, neg = cast x}
    EQ => MkINT {pos = 0, neg = 0     }
    GT => MkINT {pos = cast x, neg = 0}
  (*) = mult
  (+) = plus

public export
plusHom : (IntegerSetoid `Pair` IntegerSetoid) ~> IntegerSetoid
plusHom = MkSetoidHomomorphism
  { H = \xy => fst xy `plus` snd xy
  , homomorphic = \xy1,xy2,xy1_eq_xy2 =>
    let x1,y1,x2,y2 : INT
        x1 = fst xy1
        y1 = snd xy1
        x2 = fst xy2
        y2 = snd xy2
    in Calc $
    |~ (x1.pos + y1.pos) + (x2.neg + y2.neg)
    ~~ (x2.pos + y2.pos) + (x1.neg + y1.neg) ...(?h29)
  }
