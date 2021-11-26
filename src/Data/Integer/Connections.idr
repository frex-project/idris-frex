module Data.Integer.Connections

import Frex
import Frexlet.Monoid.Commutative

import Data.Integer.Quotient
import Data.Integer.Inductive.Definition

import Syntax.PreorderReasoning

public export
normalise : INT -> INTEGER
normalise x = x.pos `minus` x.neg

public export
quotient : INTEGER -> INT
quotient (ANat m) = MkINT {pos = m, neg = 0}
quotient (NegS m) = MkINT {pos = 0, neg = S m}

public export
auxBack : (m,n : Nat) -> (IntegerSetoid).equivalence.relation
  (quotient (m `minus` n))
  (MkINT m n)
auxBack  m     0    = (IntegerSetoid).equivalence.reflexive $ MkINT m 0
auxBack  0    (S m) = (IntegerSetoid).equivalence.reflexive $ MkINT 0 (S m)
auxBack (S n) (S m) =
  let q : INT
      q = quotient (minus n m)
      IH : q.pos + m === n + q.neg
         := auxBack n m
  in Calc $
  |~ q.pos + (1 + m)
  ~~ 1 + (q.pos + m) ...(solve 2 (Frex Nat.Additive) $
                         Dyn 0 .+. (Sta 1 .+. Dyn 1)
                         =-=
                         Sta 1 .+. (Dyn 0 .+. Dyn 1))
  ~~ 1 + (n + q.neg) ...(cong S IH)

public export
back : (x : INT) -> (IntegerSetoid).equivalence.relation
   (quotient (normalise x))
   x
back x = auxBack x.pos x.neg

public export
from : (a : INTEGER) ->
   (normalise (quotient a)) === a
from (ANat k) = Refl
from (NegS k) = Refl

public export
normaliseHom : SetoidHomomorphism IntegerSetoid (cast INTEGER) Connections.normalise
normaliseHom x y prf = Calc $
  |~ (x.pos `minus` x.neg)
  ~~ ((x.pos + y.neg) `minus` (x.neg + y.neg)) ...(sym $ minusCancelRight _ _ _)
  ~~ ((y.pos + x.neg) `minus` (y.neg + x.neg)) ...(cong2 minus prf (plusCommutative _ _))
  ~~ (y.pos `minus` y.neg) ...(minusCancelRight _ _ _)

public export
representationInteger : IntegerSetoid <~> cast INTEGER
representationInteger = MkIsomorphism
  { Fwd = MkSetoidHomomorphism
          { H = normalise
          , homomorphic = normaliseHom
          }
  , Bwd = mate $ quotient
  , Iso = IsIsomorphism
    { BwdFwdId = back
    , FwdBwdId = from
    }
  }

