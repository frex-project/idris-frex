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

public export
Uniqueness : (a : InvolutiveMonoid) -> (s : Setoid) -> (auxFrex : AuxFrexType a s) ->
  Uniqueness (InvMonoidExtension a s auxFrex)
%nf_metavar_threshold 80000
Uniqueness a s auxFrex other =
  let otherIExt : InvolutiveExtension a s
      otherIExt = ExtensionToInvolutiveExtension other
      aInvolution : Involution (cast a)
      aInvolution = InvolutiveMonoidToInvolution a
      h : AuxFrexExtension a s auxFrex ~> otherIExt.MonoidExtension
      h = auxFrex.UP.Exists otherIExt.MonoidExtension
      %hint frexNotation : InvMult1 (U $ FrexInvolutiveMonoid a s auxFrex)
      frexNotation = (FrexInvolutiveMonoid a s auxFrex).Notation1
      %hint aNotation : InvMult1 (U a)
      aNotation = a.Notation1
      %hint otherNotation : InvMult1 (U $ other.Model)
      otherNotation = other.Model.Notation1
      bid : ((cast Bool) `Pair` s) ~> ((cast Bool) `Pair` s)
      bid = bimap (mate {b = cast Bool} not) (id s)
      -- An extension morphism gives an extension morphism from the auxiliary extension
      preserveVar : (extend : InvMonoidExtension a s auxFrex ~> other) ->
                    (((cast Bool) `Pair` s) ~~>
                                cast otherIExt.MonoidExtension.Model).equivalence.relation
                     ((Homomorphism.cast extend.H).H . (AuxFrexExtension a s auxFrex).Var)
                     otherIExt.MonoidExtension.Var
      preserveVar extend (False,x) = extend.PreserveVar x
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
      preserveVar extend (True ,x) = CalcWith @{cast other.Model} $
                  |~ extend.H.H.H ((AuxFrexExtension a s auxFrex).Var.H (True, x))
                  <~  extend.H.H.H ((InvMonoidExtension a s auxFrex).Var.H x ).inv
                                          ...( other.Model.equivalence.symmetric _ _
                                             $ extend.H.H.homomorphic _ _
                                             $ (FrexInvolutionExtensionMorphism a s auxFrex).PreserveVar
                                                 (False, x))
                  <~ (extend.H.H.H ((InvMonoidExtension a s auxFrex).Var.H x)).inv
                                          ...(extend.H.preserves Involute [_])
                  <~ (other.Var.H x).inv  ...(other.Model.cong 1 (Dyn 0).inv [_] [_]
                                              [extend.PreserveVar _])
      lemma : (extend : InvMonoidExtension a s auxFrex ~> other) ->
              (AuxFrexExtension a s auxFrex) ~> otherIExt.MonoidExtension
      lemma extend = MkExtensionMorphism
        { H = MkSetoidHomomorphism           -- Can't just cast this because of
          { H = Homomorphism.cast extend.H.H -- the intensional structure of the
          , preserves = extend'.preserves    -- source and target
          }
        , PreserveEmbed = extend.PreserveEmbed
        , PreserveVar   = preserveVar extend
        }
  in \extend1,extend2 => auxFrex.UP.Unique otherIExt.MonoidExtension
                            (lemma extend1) (lemma extend2)
%nf_metavar_threshold 50

{-

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
