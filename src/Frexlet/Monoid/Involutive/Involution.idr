||| We have an involution functor `.rev : Monoid -> Monoid`
||| that sends a monoid `a : Monoid` to the monoid with the same
||| carrier, but with reversed multiplication:
||| a.rev.Sem Prod [x,y] = a.Sem Prod [y,x]
||| 
||| We can use this functor to characterise involutions as
||| self-inverse homomorphisms, and this characterisation allows us to
||| treat involutive monoids quite abstractly.
||| 
||| For a more general set-up, see Bar Jacobs "Involutive Categories
||| and Monoids, with a GNS-correspondence", QPL'10,
||| https://arxiv.org/abs/1003.4552
module Frexlet.Monoid.Involutive.Involution

import Frex

import Notation
import Notation.Multiplicative
import Frexlet.Monoid.Notation
import Frexlet.Monoid.Theory

import Frexlet.Monoid.Involutive.Theory
import Frexlet.Monoid.Involutive.Notation

namespace Algebra
  ||| Same monoid structure with the order of multiplication reversed:
  |||
  ||| a.rev.Sem Prod [x,y] = a.Sem Prod [y,x]
  public export
  (.rev) : (a : MonoidStructure) -> MonoidStructure
  a.rev = MkSetoidAlgebra
    { algebra = MakeAlgebra 
      { U = U a
      , Semantics = \case
          MkOp Neutral => a.algebra.Semantics Unit
          MkOp Product => \[x,y] => a.algebra.Semantics Prod [y,x]
      }
    , equivalence = a.equivalence
    , congruence = \case
        MkOp Neutral => \x,y,prf => a.congruence Unit x y prf
        MkOp Product => \[x1,x2],[y1,y2],prf => a.congruence Prod [x2,x1] [y2,y1] \case
          0 => prf 1
          1 => prf 0
    }

||| Same monoid with the order of multiplication reversed:
|||
||| a.rev.Sem Prod [x,y] = a.Sem Prod [y,x]
public export
(.rev) : (a : Monoid) -> Monoid
(.rev) a = MkModel 
  { Algebra = a.Algebra.rev
  , Validate = \case
      LftNeutrality => a.Validate RgtNeutrality
      RgtNeutrality => a.Validate LftNeutrality
      Associativity => \env => a.equivalence.symmetric _ _ 
                         $ a.Validate Associativity \case
                         0 => env 2
                         1 => env 1
                         2 => env 0
  }

namespace Functor
  ||| Functorial action of .rev on monoid structure homomorphisms
  public export
  (.rev) : {a,b : MonoidStructure} -> a ~> b -> a.rev ~> b.rev
  (.rev) h = MkSetoidHomomorphism 
    { H = h.H
    , preserves = \case
        MkOp Neutral => h.preserves Unit
        MkOp Product => \[x,y] => h.preserves Prod [y,x]
    }

||| .rev is an Involution on the category of monoids
public export
(.revInvolution) : (a : Monoid) -> a.Algebra <~> a.Algebra.rev.rev
(a.revInvolution) = MkIsomorphism
  { Iso = MkIsomorphism
      { Fwd = id (cast a)
      , Bwd = id (cast a)
      , Iso = IsIsomorphism
        { BwdFwdId = a.equivalence.reflexive
        , FwdBwdId = a.equivalence.reflexive
        }
      }
  , FwdHomo = \case
      MkOp Neutral => \[] => a.equivalence.reflexive _
      MkOp Product => \[x,y] => a.equivalence.reflexive _
  }
  
||| Jacobs's axiom for the involution on the category of monoids
public export
(.revInvolutionAxiom) : (a : Monoid) -> 
  (a.Algebra.rev ~~> a.Algebra.rev.rev.rev).equivalence.relation
    (cast {to = a ~> a.rev.rev} a.revInvolution).rev
    (cast {to = a.rev ~> a.rev.rev.rev} a.rev.revInvolution)
a.revInvolutionAxiom = a.equivalence.reflexive
