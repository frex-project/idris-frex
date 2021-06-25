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

-------
import Frex
import Frex.Algebra
import Frex.Model
import Notation
import Notation.Multiplicative
import Frexlet.Monoid.Involutive.Notation
import Data.Setoid
import Frexlet.Monoid
import Frexlet.Monoid.Theory
import Frexlet.Monoid.Notation

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
      {- The main proof obligation is that `h` preserves the involution.
         We appeal to the universal property of AuxFrex a s:
         for the following extension:
         
            inv      Embed.rev           (cast otherIExt.Var).H
         a ----> a.rev ---> other.Model.rev <---- (Bool, s)
      -}
      presExt : AuxExtensionType a s
      presExt = MkExtension
        { Model = otherIExt.MonoidExtension.Model.rev
        , Embed = otherIExt.MonoidExtension.Embed.rev . aInvolution.H
        , Var   = (cast otherIExt.Var).H 
        }
      
  in MkSetoidHomomorphism
  { H = h.H.H
  , preserves = \case
      MkOp (Mono op)  => h.H.preserves (MkOp op)
      
      

      {-
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
      -}
      MkOp Involution => ?h2__
  }
