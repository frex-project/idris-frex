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

%nf_metavar_threshold 40000
public export
InvMonoidExtension : (a : InvolutiveMonoid) -> (s : Setoid) -> (auxFrex : AuxFrexType a s)
  -> Extension a s
{- The definition of the involution operation on FrexInvMonoid is:

       Embed                                    Var
   a -------------------> FrexInvMonoid a s  <---------------- (Bool, s)
   | a.inv   =                 | FrexInvolution a s              | bimap not id
   v                           v        =                        v
   a.rev --> (FrexInvMonoid a s).rev <------------------------ (Bool, s)
       Embed.rev                             Var

  The LHS square tells us the monoid homomorphism `Embed` preserves the involution.
  The RHS square gives us the compatibility condition to make an
  `Env s (FrexInvMonoid a s) (FrexInvolution a s)`
  which in turn gives the required `Var` map.
-}
InvMonoidExtension a s auxFrex = InvolutiveExtensionToExtension $
  MkInvolutiveExtension
  { MonoidExtension  = AuxFrexExtension a s auxFrex
  , ModelInvolution  = FrexInvolutionInvolution a s auxFrex
  , PreserveInvolute = (FrexInvolutionExtensionMorphism a s auxFrex).PreserveEmbed
  , VarCompatibility = (FrexInvolutionExtensionMorphism a s auxFrex).PreserveVar
  }
{-

public export
(.Env) : (ext : InvolutiveExtension a s) ->
  Env s ext.MonoidExtension.Model
    ext.ModelInvolution
(.Env) ext = MkEnv
    { H = ext.MonoidExtension.Var
    , compatibility = ext.VarCompatibility
    }

public export
ExtenderHomomorphism : (a : InvolutiveMonoid) -> (s : Setoid) ->
  ExtenderHomomorphism (InvMonoidExtension a s)
ExtenderHomomorphism a s other =
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
      {- The main proof obligation is that `h` preserves the involution.
         We appeal to the universal property of AuxFrex a s:
         for the following extension:

            inv      Embed.rev                Var         bimap not id
         a ----> a.rev ---> other.Model.rev <---- (Bool, s) <--- (Bool, s)
      -}
      presExt : AuxExtensionType a s
      presExt = MkExtension
        { Model = otherIExt.MonoidExtension.Model.rev
        , Embed = otherIExt.MonoidExtension.Embed.rev . aInvolution.H
        , Var   = otherIExt.MonoidExtension.Var .
                  bid
        }
      {- So the lef and right halves of the next two diagram give us
         extension morphism: AuxFrexExtension a s ~> presExt

                                  h.H
          AuxFrexExtension a s -------------------------> other.Model
                 |      ^       = (h.PreserveEmbed)      ^      |
                 |      \   Embed          Embed        /       |
                 |  =    ------------- a ---------------        |
            inv  | (Embed.H.preserves) |inv              =      | inv
                 |                     |(other.Embed.preserves) |
                 |          Embed.rev  v      Embed.rev         |
                 |      /------------  a.rev -----------\       |
                 |     |      (h.PreseveEmbed).rev      |       |
                 v     v               =                v       v
         (AuxFrexExtension a s).rev ------------------> (other.Model).rev
                                        h.H.rev
                                   h.H
          AuxFrexExtension a s -------------------------> other.Model
                 |      ^       = (h.PreserveVar)        ^      |
                 |      \   Var          Var            /       |
                 |  =    -------- (Bool, s) ------------        |
            inv  |    (PreserveVar)    |bimap not id     =      | inv
                 |                     |(IExt.VarCompatibility) |
                 |          Var        v      Var               |
                 |      /-------- (Bool, s) ------------\       |
                 |     |      (h.PreseveVar)            |       |
                 v     v               =                v       v
         (AuxFrexExtension a s) ---------------------> (other.Model).rev
                                   h.H.H
      -}
      extendLHS,extendRHS : AuxFrexExtension a s ~> presExt
      extendLHS = MkExtensionMorphism
        { H =  h.H.rev . FrexInvolution a s
        , PreserveEmbed = \i => other.Model.equivalence.reflexive _
        , PreserveVar   = \bx => CalcWith @{cast other.Model} $
            |~ h.H.H.H ((AuxFrexExtension a s).Var.H bx).inv
            <~ h.H.H.H ((AuxFrexExtension a s).Var.H $ bid.H bx)
               ...(h.H.H.homomorphic _ _ $
                   (FrexInvolutionExtensionMorphism a s).PreserveVar _)
            <~ otherIExt.MonoidExtension.Var.H (bid.H bx)
               ...(h.PreserveVar _)
         }
      extendRHS = MkExtensionMorphism
        { H = otherIExt.ModelInvolution.H . h.H
        , PreserveEmbed = \i => CalcWith @{cast other.Model} $
          |~ (h.H.H.H $ (AuxFrexExtension a s).Embed.H.H i ).inv
          <~ (otherIExt.MonoidExtension.Embed.H.H i).inv
             ...(other.Model.cong 1 (Dyn 0).inv [_] [_] [h.PreserveEmbed i])
          <~ (otherIExt.MonoidExtension.Embed.H.H i.inv)
            ...( other.Model.equivalence.symmetric _ _
               $ other.Embed.preserves Involute [_])
        , PreserveVar   = \bx => CalcWith @{cast other.Model} $
          |~ (h.H.H.H $ (AuxFrexExtension a s).Var.H bx).inv
          <~ (otherIExt.MonoidExtension.Var.H bx).inv
             ...(other.Model.cong 1 (Dyn 0).inv [_] [_] [h.PreserveVar bx])
          <~ (otherIExt.MonoidExtension.Var.H $ bid.H bx)
             ...(otherIExt.VarCompatibility _)
        }
  in MkSetoidHomomorphism
  { H = h.H.H
  , preserves = \case
      MkOp (Mono op)  => h.H.preserves (MkOp op)
      MkOp Involution => \ [i] =>
        (AuxFrex a s).UP.Unique presExt extendLHS extendRHS i
  }

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
