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
import Frexlet.Monoid.Involutive.Properties

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

-- The next two definitions and the two constructions following it are
-- the main point of this module:

||| Characterises the involution axiom abstractly.
public export 0
(.Involution) : (a : Monoid) -> (h : a ~> a.rev) -> Type
a.Involution h =
  (a ~~> a.rev.rev).equivalence.relation
    (h.rev . h)
    (cast a.revInvolution)


||| A characterisation of the structure and properties of an
||| involution over a monoid.
public export
record Involution (a : Monoid) where
  constructor MkInvolution
  H : a ~> a.rev
  involutive : a.Involution H

||| Repackage the data and properties in an involutive monoid abstractly
public export
InvolutiveMonoidToInvolution : (a : InvolutiveMonoid) -> Involution (cast a)
InvolutiveMonoidToInvolution a = MkInvolution
  { H = MkSetoidHomomorphism
    { H = MkSetoidHomomorphism
      { H = a.sem Involution
      , homomorphic = \x,y,prf => a.Algebra.congruence Involute [x] [y] (\case {0 => prf})
      }
    , preserves = \case
        MkOp Neutral => \[] => invNeutral a
        MkOp Product => \[x,y] => a.validate Antidistributivity [_,_]
    }
  , involutive = \x => a.validate Involutivity [x]
  }

public export
InvolutionToInvolutiveMonoid : (a : Monoid) -> Involution (cast a) -> InvolutiveMonoid
InvolutionToInvolutiveMonoid a involution =
  let %hint
      notation : Multiplicative1 (U a)
      notation = a.Multiplicative1
  in MkInvolutiveMonoid
     a
     involution.H.H
     (\env => involution.involutive (env 0))
     (\env => involution.H.preserves Prod [_,_])

-------- functoriality of (.ev) : (a ~> b) -> a.rev ~> b.rev  -------

||| Composition is preserved by (.ev) : (a ~> b) -> a.rev ~> b.rev
public export
revFunctorialityCompose : {a,b,c : MonoidStructure} -> (f : b ~> c) -> (g : a ~> b) ->
  ((a.rev) ~~> (c.rev)).equivalence.relation
    ((f . g).rev)
    (f.rev . g.rev)
revFunctorialityCompose f g x = (c.rev).equivalence.reflexive _
||| Identities are preserved by (.ev) : (a ~> b) -> a.rev ~> b.rev
public export
revFunctorialityId : {a : MonoidStructure} ->
  ((a.rev) ~~> (a.rev)).equivalence.relation
    ((id a).rev)
    (id (a.rev))
revFunctorialityId x = (a.rev).equivalence.reflexive _

-- No idea why the corresponding record doesn't work
||| a setoid homomorphism `H : (Bool, s) ~> U a` satisfying:
|||          H
|||   U a <---- (Bool, s)
|||    | inv       | bimap not id
|||    v           v
|||   U a <---- (Bool, s)
|||          H
public export
data Env : (s : Setoid) -> (a : Monoid) -> (inv : Involution a) -> Type where
  MkEnv : {0 s : Setoid} -> {0 a : Monoid} -> {0 inv : Involution a} ->
    (H : ((cast Bool) `Pair` s) ~> cast a) ->
     (compatibility : (((cast Bool) `Pair` s) ~~> cast {to = Setoid} a).equivalence.relation
        ((inv).H.H . H)
        (H . (bimap (mate {b = cast Bool} Prelude.not) (id s))))
    -> Env s a inv

public export
(.H) : Env s a inv -> ((cast Bool) `Pair` s) ~> cast a
(.H) (MkEnv h _) = h

public export
(.compatibility) : (env : Env s a inv) ->
   (((cast Bool) `Pair` s) ~~> cast a).equivalence.relation
      ((inv).H.H . env.H)
      ( env.H . (bimap (mate {b = cast Bool} Prelude.not) (id s)))
(.compatibility) (MkEnv _ c) = c


-- The point is that having a function `f : s -> U b` for some
-- involutive monoid is the same thing as having an `Env`.

namespace To
  public export
  cast : {s : Setoid} -> {c : InvolutiveMonoid} -> (f : s ~> cast c) ->
    Env s (cast c) (InvolutiveMonoidToInvolution c)
  cast f = MkEnv
    { H = (either f ((InvolutiveMonoidToInvolution c).H.H . f)) . distribute
    , compatibility = \case
        (False, x) => c.equivalence.reflexive _
        (True , x) => c.validate Involutivity [_]
    }

namespace Back
  public export
  cast : {s : Setoid} -> {c : Monoid} -> {inv : Involution c} -> Env s c inv -> (s ~> cast c)
  cast env = env.H . (tuple (const {b = cast Bool} False) (id s))

