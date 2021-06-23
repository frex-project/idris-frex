||| Cosntructing the involutive monoid frex.
||| 
||| This implementation uses the fact that if `a` is an involutive
||| monoid, then `Frex a s` can be represented by `Frex a.monoid (Bool, s)`.
module Frexlet.Monoid.Involutive.Frex

import Frex

import Notation
import Notation.Multiplicative
import Frexlet.Monoid.Notation
import Frexlet.Monoid.Theory
import Frexlet.Monoid.Frex

import Frexlet.Monoid.Involutive.Theory
import Frexlet.Monoid.Involutive.Notation
import Frexlet.Monoid.Involutive.Properties
import Frexlet.Monoid.Involutive.Involution

-- Our construction uses an auxiliary frex for the underlying monoid

||| Type of auxiliary monoid frex used to construct the involutive monoid frex
public export 0
AuxFrexType : (a : InvolutiveMonoid) -> (s : Setoid) -> Type
AuxFrexType a s = Frex (cast {to = Monoid} a) (cast Bool `Pair` s)

||| Auxiliary monoid frex used to construct the involutive monoid frex
public export
AuxFrex : (a : InvolutiveMonoid) -> (s : Setoid) -> AuxFrexType a s
AuxFrex a s = MonoidFrex (cast a) (cast Bool `Pair` s)

||| The monoid part of the involutive monoid frex
public export
FrexInvMonoid : (a : InvolutiveMonoid) -> (s : Setoid) -> Monoid
FrexInvMonoid a s = FrexMonoid (cast a) (cast Bool `Pair` s)

||| We use the following extension to define the involution on the frex
|||
||| a                                      (Bool, s)
||| | a.inv                                    | bimap not id
||| v                                          v
||| a.rev --> (FrexInvMonoid a s).rev <--- (Bool, s)
|||     sta.rev                        dyn
public export
FrexInvolutionExtension : (a : InvolutiveMonoid) -> (s : Setoid) ->
  Extension (cast {to=Monoid} a) (cast Bool `Pair` s)
FrexInvolutionExtension a s =
  let %hint
      notation : InvMult1 (U a)
      notation = a.Notation1
      frex : AuxFrexType a s
      frex = AuxFrex     a s
  in MkExtension
  { Model = (FrexInvMonoid a s).rev
  , Embed = frex.Data.Embed.rev . (InvolutiveMonoidToInvolution a).H
  , Var   = frex.Data.Var . bimap (mate {b = cast Bool} not) (id s)
  }

||| The involution on the frex is given by the universal property:
|||
||| a ------> FrexInvMonoid a s  <------- (Bool, s)
||| | a.inv   =      | FrexInvolution a s     | bimap not id
||| v  (in Monoids)  v        =   (in Set)    v
||| a.rev --> (FrexInvMonoid a s).rev <--- (Bool, s)
|||     sta.rev                        dyn
public export
FrexInvolutionExtensionMorphism : (a : InvolutiveMonoid) -> (s : Setoid) ->
  (AuxFrex a s).Data ~> FrexInvolutionExtension a s
FrexInvolutionExtensionMorphism a s = (AuxFrex a s).UP.Exists (FrexInvolutionExtension a s)

||| The involution homomorphism for the frex
public export
FrexInvolution : (a : InvolutiveMonoid) -> (s : Setoid) ->
  FrexInvMonoid a s ~> (FrexInvMonoid a s).rev
FrexInvolution a s = (FrexInvolutionExtensionMorphism a s).H

||| The involution axiom boils down to this equation:
|||
|||  FrexInvMonoid a s  ---------------------
|||         |                               |
|||         | FrexInvolution a s            | cast (cast a).revInvolution
|||         |                               |
|||         V                               V
||| (FrexInvMonoid a s).rev -------> (FrexInvMonoid a s).rev.rev
|||                 (FrexInvolution a s).rev
public export
FrexInvolutionIsInvolution : (a : InvolutiveMonoid) -> (s : Setoid) ->
  (FrexInvMonoid a s).Involution (FrexInvolution a s)
FrexInvolutionIsInvolution a s =
  let %hint
      notation : InvMult1 (U a)
      notation = a.Notation1
      frex : Extension (cast {to = Monoid} a)  (cast Bool `Pair` s)
      frex = (AuxFrex a s).Data
      inv  : (cast a) ~> (cast a).rev
      inv  = (InvolutiveMonoidToInvolution a).H
      bid  : (cast Bool `Pair` s) ~> (cast Bool `Pair` s)
      bid  = bimap (mate {b = cast Bool} not) (id s)
      frexInv : frex.Model ~> frex.Model.rev
      frexInv = FrexInvolution a s
      j : frex.Model.Algebra <~> frex.Model.Algebra.rev.rev
      j = frex.Model.revInvolution
      ||| We'll use frex's universal property with respect to this extension:
      |||
      |||   a                                         (Bool, s)
      |||   | inv                                         |  bimap not id
      |||   v                                             v
      |||   a.rev                                     (Bool, s)
      |||   | inv.rev                                     |  bimap not id
      |||   v                                             v
      |||   a.rev.rev ---> frex.Model.rev.rev <------ (Bool, s)
      |||          frex.Embed.rev.rev          frex.Var
      doubleInvExtension : Extension (cast {to = Monoid}  a) (cast Bool `Pair` s)
      doubleInvExtension = MkExtension
        { Model = frex.Model.rev.rev
        , Embed = frex.Embed.rev.rev . inv.rev . inv
        , Var   = frex.Var   . bid . bid
        }
      -- and we'll construct two extension morphisms from frex.Model into it.
      ||| The first extension morphism:
      |||      frex.Embed                frex.Var
      |||   a -----------> frex.Model <-------------- (Bool, s)
      |||   | inv    = (def)      |inv       = (def)      |  bimap not id
      |||   v     ditto.rev       v        frex.Var       v
      |||   a.rev -------> frex.Model.rev <---------  (Bool, s)
      |||   | inv.rev = (functor) |inv.rev   = (def)      |  bimap not id
      |||   v     dittor.rev.rev  v        frex.Var       v
      |||   a.rev.rev ---> frex.Model.rev.rev <------ (Bool, s)
      |||          frex.Embed.rev.rev          frex.Var
      invInvMorphism : frex ~> doubleInvExtension
      invInvMorphism = MkExtensionMorphism
        { H = (FrexInvolution a s).rev . (FrexInvolution a s)
        , PreserveEmbed = \i => CalcWith @{cast $ frex.Model.rev.rev} $
          |~ (frexInv.rev.H.H $ frexInv.H.H $ frex.Embed.H.H i)
          <~ (frexInv.rev.H.H $ frex.Embed.rev.H.H $ inv.H.H i)
            ...(frexInv.rev.H.homomorphic _ _ $
                (FrexInvolutionExtensionMorphism a s).PreserveEmbed _)
          <~ (frex.Embed.rev.rev.H.H $ inv.rev.H.H  $ inv.H.H i)
            ...((FrexInvolutionExtensionMorphism a s).PreserveEmbed _)
        , PreserveVar   = \x => CalcWith @{cast $ frex.Model.rev.rev} $
          |~ (frexInv.rev.H.H $ frexInv.H.H $ frex.Var.H x)
          <~ (frexInv.rev.H.H $ frex.Var.H $ bid.H x)
            ...(frexInv.rev.H.homomorphic _ _ $
                (FrexInvolutionExtensionMorphism a s).PreserveVar _)
          <~ (frex.Var.H $ bid.H $ bid.H x)
            ...((FrexInvolutionExtensionMorphism a s).PreserveVar (bid.H x))
        }
      ||| The second extension morphism:
      |||      frex.Embed                frex.Var
      |||   a -----------> frex.Model <-------------- (Bool, s)
      |||   | inv \  = (j nat)  |   = ( not . not = id)   |  bimap not id
      |||   v      \            |                         v
      |||   a.rev   \ cast j    | cast j              (Bool, s)
      |||   | inv.rev\          |                         |  bimap not id
      |||   v        v          v                         v
      |||   a.rev.rev ---> frex.Model.rev.rev <------ (Bool, s)
      |||          frex.Embed.rev.rev          frex.Var
      jMorphism : frex ~> doubleInvExtension
      jMorphism = MkExtensionMorphism
        { H = cast j
        , PreserveEmbed = ?h2
        , PreserveVar   = ?h1
        }
  in ?FrexInvolutionIsInvolution_rhs

