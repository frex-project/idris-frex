||| Representation of the integers using the INT-construction on Nat,
||| and quotients. Hopefully it'll be easier to prove its properties
module Data.Integer.Quotient

import public Data.Integer.Quotient.Definition
import public Data.Integer.Quotient.Operations

import Frex
import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Nat

import Frexlet.Monoid.Notation

import Data.Primitives.Views
import Data.Setoid
import Syntax.PreorderReasoning

-- Let's validate the monoid axioms!

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
      LftNeutrality => \env => ?h1
         {- Bug? Refl doesn't discharge h1
         env : Fin 1 -> INT
         ------------------------------
         h1 : {a = Nat} {b = Nat}
              ((env (FZ {k = 0}).pos) + (env (FZ {k = 0}).neg)) ===
              ((env (FZ {k = 0}).pos) + (env (FZ {k = 0}).neg))

         -}
      RgtNeutrality => ?h2_2
      Associativity => ?h2_3
  }
