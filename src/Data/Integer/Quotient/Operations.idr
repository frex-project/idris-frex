module Data.Integer.Quotient.Operations
import Data.Integer.Quotient.Definition

import Frex
import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Nat

import Frexlet.Monoid.Notation

import Data.Primitives.Views
import Data.Setoid
import Syntax.PreorderReasoning
import Syntax.WithProof

%default total

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
Neg INT where
  m - n = MkINT 
    { pos = m.pos + n.neg
    , neg = m.neg + n.pos
    }

  negate m = MkINT
    { pos = m.neg
    , neg = m.pos
    }

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
        lemma : {x,y,z,w : Nat} -> (x + y) + (z + w) === (x + z) + (y + w)
          := solve 4 Monoid.Commutative.Free.Free
               {a = Nat.Additive} $
               (X 0 .+. X 1) .+. (X 2 .+. X 3)
               =-=
               (X 0 .+. X 2) .+. (X 1 .+. X 3)
    in Calc $
    |~ (x1.pos + y1.pos) + (x2.neg + y2.neg)
    ~~ (x1.pos + x2.neg) + (y1.pos + y2.neg) ...(lemma)
    ~~ (x2.pos + x1.neg) + (y2.pos + y1.neg) ...(cong2 (+) xy1_eq_xy2.fst xy1_eq_xy2.snd)
    ~~ (x2.pos + y2.pos) + (x1.neg + y1.neg) ...(lemma)
  }

public export
IntegerMonoid : Monoid
IntegerMonoid = MkModel
  { Algebra  = MkSetoidAlgebra
      { algebra     = MkAlgebra
        { U   = U IntegerSetoid
        , Sem = \case
            Neutral => 0
            Product => plus
        }
      , equivalence = (IntegerSetoid).equivalence
      , congruence  = \case
          (MkOp Neutral) => \[],[],_ => Refl
          (MkOp Product) => \[x1,y1],[x2,y2],prf => plusHom.homomorphic (x1,y1) (x2,y2) $
                MkAnd (prf 0) (prf 1)
      }
  , Validate = \case
      LftNeutrality => \env => case @@(env 0) of
        (MkINT _ _ ** prf) => rewrite prf in Refl
         {- Bug? Refl doesn't discharge h1
         env : Fin 1 -> INT
         ------------------------------
         h1 : {a = Nat} {b = Nat}
              ((env (FZ {k = 0}).pos) + (env (FZ {k = 0}).neg)) ===
              ((env (FZ {k = 0}).pos) + (env (FZ {k = 0}).neg))
         -}
      RgtNeutrality => \env => case @@(env 0) of
        (u@(MkINT pos neg) ** prf) => rewrite prf in 
         solve 2 Free {a = Nat.Additive} $
         (X 0 .+. O1) .+. X 1 =-=
          X 0 .+.(X 1 .+. O1)
      Associativity => \env => case (@@(env 0), @@(env 1), @@(env 2)) of
        ((u@(MkINT _ _) ** prf1), (v@(MkINT _ _) ** prf2), (w@(MkINT _ _) ** prf3)) =>
          rewrite prf1 in
          rewrite prf2 in
          rewrite prf3 in
          solve 6 Free {a = Nat.Additive} $
          (X 0 .+. (X 1 .+. X 2)) .+. ((X 3 .+. X 4) .+. X 5) =-=
          ((X 0 .+. X 1) .+. X 2) .+. ( X 3 .+.(X 4 .+. X 5))
  }
