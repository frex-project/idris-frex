module Data.Integer.Quotient.Definition

import Data.Setoid
import Syntax.PreorderReasoning

import Frex
import Frexlet.Monoid.Commutative.Nat
import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Notation.Additive

import Data.Nat

import Frex.Magic
%language ElabReflection


public export
record INT where
  constructor MkINT
  pos,neg : Nat

public export
INTEq : (x,y : INT) -> Type
INTEq x y = x.pos + y.neg === y.pos + x.neg

public export
IntegerSetoid : Setoid
IntegerSetoid = MkSetoid
  { U = INT
  , equivalence  = MkEquivalence
    { relation   = INTEq
    , reflexive  = \x => Refl
    , symmetric  = \x,y,prf => sym prf
    , transitive = \x,y,z,x_eq_y,y_eq_z =>
      plusRightCancel _ _ y.pos $
      Calc $
      |~ (x.pos + z.neg) + y.pos
      ~~  x.pos +(y.pos + z.neg) ...(solve 3 {a = Additive} (Commutative.Free.Free) $
                                    (X 0 .+. X 2) .+. X 1 =-=
                                    X 0 .+. (X 1 .+. X 2))
                                -- ^ Getting weird errors with this alternative:
                                -- (%runElab frexMagic Frex Additive)
      ~~  x.pos +(z.pos + y.neg) ...(cong (x.pos +) y_eq_z)
      ~~  z.pos +(x.pos + y.neg) ...(solve 3 {a = Additive} (Commutative.Free.Free) $
                                    X 0 .+. (X 2 .+. X 1) =-=
                                    X 2 .+. (X 0 .+. X 1))
      ~~  z.pos +(y.pos + x.neg) ...(cong (z.pos +) x_eq_y)
      ~~ (z.pos + x.neg) + y.pos ...(solve 3 {a = Additive} (Commutative.Free.Free) $
                                    X 2 .+. (X 1 .+. X 0) =-=
                                    (X 2 .+. X 0).+. X 1)
    }
  }
