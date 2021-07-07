||| An involutive monoid a is a monoid equipped with a unary involution
||| operator .inv : U a -> U a satisfying:
|||
||| x.inv.inv = x
|||
||| (x .*. y).inv = y.inv .*. x.inv
module Frexlet.Monoid.Involutive

import public Frexlet.Monoid.Involutive.Theory
import public Frexlet.Monoid.Involutive.Properties
import public Frexlet.Monoid.Involutive.Involution
import public Frexlet.Monoid.Involutive.Frex

import Frex
import Notation
import Notation.Multiplicative
import Frexlet.Monoid.Notation.Multiplicative
import Frexlet.Monoid.Theory
import Frexlet.Monoid.Involutive.Theory
import Frexlet.Monoid.Frex

import Frexlet.Monoid.Involutive.Notation

import Data.Bool
import Data.Setoid

%default total
{-

public export
InvExtender : (a : InvolutiveMonoid) -> (s : Setoid) ->
  Frex.Frex.Extender (InvMonoidExtension a s)
%nf_metavar_threshold 40000
InvExtender a s other = MkExtensionMorphism
  { H = ExtenderHomomorphism a s other
  , PreserveEmbed = ((AuxFrex a s).UP.Exists
      (ExtensionToInvolutiveExtension other).MonoidExtension).PreserveEmbed
  , PreserveVar   = \i =>
      ((AuxFrex a s).UP.Exists
      (ExtensionToInvolutiveExtension other).MonoidExtension).PreserveVar
      (False, i)
  }
%nf_metavar_threshold 50

public export
Uniqueness : (a : InvolutiveMonoid) -> (s : Setoid) -> Uniqueness (InvMonoidExtension a s)
%nf_metavar_threshold 80000
Uniqueness a s other =
  let otherIExt : InvolutiveExtension a s
      otherIExt = ExtensionToInvolutiveExtension other
      aInvolution : Involution (cast a)
      aInvolution = InvolutiveMonoidToInvolution a
      h : AuxFrexExtension a s ~> otherIExt.MonoidExtension
      h = (AuxFrex a s).UP.Exists otherIExt.MonoidExtension
      %hint frexNotation : InvMult1 (U $ FrexInvolutiveMonoid a s)
      frexNotation = (FrexInvolutiveMonoid a s).Notation1
      %hint aNotation : InvMult1 (U a)
      aNotation = a.Notation1
      %hint otherNotation : InvMult1 (U $ other.Model)
      otherNotation = other.Model.Notation1
      bid : ((cast Bool) `Pair` s) ~> ((cast Bool) `Pair` s)
      bid = bimap (mate {b = cast Bool} not) (id s)
      -- An extension morphism gives an extension morphism from the auxiliary extension
      lemma : (extend : InvMonoidExtension a s ~> other) ->
              (AuxFrexExtension a s) ~> otherIExt.MonoidExtension
      lemma extend =
        let extend' : cast {to = Monoid} (InvMonoidExtension a s).Model ~> cast other.Model
            extend' = Homomorphism.cast extend.H
        in MkExtensionMorphism
        { H = MkSetoidHomomorphism          -- Can't just cast this because of
          { H = extend'.H                   -- the intensional structure of the
          , preserves = extend'.preserves   -- source and target
          }
        , PreserveEmbed = extend.PreserveEmbed
        , PreserveVar   = \case
            (False,x) => extend.PreserveVar x
            {- This is the only real proof obligation:
                               Var               tuple True x
                AuxFrex a s  <------ (Bool, s) <--------------- s
                     |    |          not x id\    tuple False x/|
                     |    | FrexInv-ExtMorph  ---,     =      |||
                     |    \ inv     =        Var v   Refl     //|
                     |     ---> AuxFrex a s <--- (Bool, s) <- / |
                     | =    extend.H |    extend.PreserveVar /  | tuple True x
            extend.H | preserve      v         other.Var    /   |
                     |  Involute other.Model <--------------    |
                     |        inv        /     def              |
                     v   v---------------        =              v
               other.Model <------------------------------- (Bool,s)
                             otherIExt.MonoidExtension.Var
            -}
            (True ,x) => CalcWith @{cast other.Model} $
              |~ extend.H.H.H ((AuxFrexExtension a s).Var.H (True, x))
              <~  extend.H.H.H ((InvMonoidExtension a s).Var.H x ).inv
                                      ...( other.Model.equivalence.symmetric _ _
                                         $ extend.H.H.homomorphic _ _
                                         $ (FrexInvolutionExtensionMorphism a s).PreserveVar (False, x))
              <~ (extend.H.H.H ((InvMonoidExtension a s).Var.H x)).inv
                                      ...(extend.H.preserves Involute [_])
              <~ (other.Var.H x).inv  ...(other.Model.cong 1 (Dyn 0).inv [_] [_]
                                          [extend.PreserveVar _])
        }
  in \extend1,extend2 => (AuxFrex a s).UP.Unique otherIExt.MonoidExtension
                            (lemma extend1) (lemma extend2)
%nf_metavar_threshold 50

public export
Frex : (a : InvolutiveMonoid) -> (s : Setoid) -> Frex a s
%nf_metavar_threshold 80000
Frex a s = MkFrex
  { Data = InvMonoidExtension a s
  , UP = IsUniversal
    { Exists = InvExtender a s
    , Unique = Uniqueness a s
    }
  }
%nf_metavar_threshold 50

-}

||| Auxiliary monoid frex used to construct the involutive monoid frex
public export
AuxFrex : (a : InvolutiveMonoid) -> (s : Setoid) -> AuxFrexType a s
AuxFrex a s = MonoidFrex (cast a) (cast Bool `Pair` s)
