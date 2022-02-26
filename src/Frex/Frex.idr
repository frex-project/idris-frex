||| Definitions and constructions for free extensions
module Frex.Frex

import Data.Setoid
import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model

import Frex.Free
import Frex.Coproduct

import Syntax.PreorderReasoning.Generic

%default total

public export
record Extension {Pres : Presentation}
    (A : Model Pres)(X : Setoid) where
  constructor MkExtension
  Model : Model Pres
  Embed : A ~> Model
  Var   : X ~> cast Model

public export
(ford : pres.signature = sig) => Semantic (Extension {Pres = pres} a x) (Op sig) where
  (.SemType) c = c.Model.SemType
  (.Sem)     c = c.Model.Sem

public export
(ford : pres.signature = sig) => Semantic (Extension {Pres = pres} a x) (Term sig y) where
  (.SemType) c = c.Model.SemType
  (.Sem)     c = c.Model.Sem

public export
record (~>) {Pres : Presentation}
       {A : Model Pres} {X : Setoid}
    (Extension1, Extension2 : Extension A X) where
  constructor MkExtensionMorphism
  H : (Extension1).Model ~> (Extension2).Model
  PreserveEmbed :
    (cast A ~~> (Extension2).Model)
      .equivalence.relation
        (H . (Extension1).Embed)
             (Extension2).Embed
  PreserveVar   :
    (X ~~> cast (Extension2).Model)
      .equivalence.relation
        ((H).H . (Extension1).Var)
                 (Extension2).Var

public export
Extender : {pres : Presentation} -> {a : Model pres} -> {x : Setoid} ->
  (frex : Extension a x) -> Type
Extender frex = (other : Extension a x) -> frex ~> other

-- The usual boilerplate since we don't have copatterns

public export 0
ExtenderFunction : {pres : Presentation} -> {a : Model pres} -> {x : Setoid} ->
  (frex : Extension a x) -> Type
ExtenderFunction frex = (other : Extension a x) -> U frex.Model -> U other.Model

public export 0
ExtenderIsHomomorphism : {pres : Presentation} -> {a : Model pres} -> {x : Setoid} ->
  (frex : Extension a x) -> (extender : ExtenderFunction frex) -> Type
ExtenderIsHomomorphism frex extender = (other : Extension a x) ->
  Homomorphism frex.Model.Algebra other.Model.Algebra (extender other)

public export 0
ExtenderIsAlgebraHomomorphism : {pres : Presentation} -> {a : Model pres} -> {x : Setoid} ->
  (frex : Extension a x) -> (extender : ExtenderFunction frex) -> Type
ExtenderIsAlgebraHomomorphism frex extender = (other : Extension a x) ->
  (f : Op pres.signature) -> CongruenceWRT (cast frex.Model) (frex.Model.Sem f)

public export 0
ExtenderHomomorphism : {pres : Presentation} -> {a : Model pres} -> {x : Setoid} ->
  (frex : Extension a x) -> Type
ExtenderHomomorphism frex = (other : Extension a x) -> frex.Model ~> other.Model

public export 0
ExtenderPreservesEmbedding :  {pres : Presentation} -> {a : Model pres} -> {x : Setoid} ->
  (frex : Extension a x) -> (extender : ExtenderHomomorphism frex) -> Type
ExtenderPreservesEmbedding frex extender = (other : Extension a x) ->
  (a ~~> other.Model).equivalence.relation
    ((extender other) . frex.Embed)
                       other.Embed
public export 0
ExtenderPreservesVars :  {pres : Presentation} -> {a : Model pres} -> {x : Setoid} ->
  (frex : Extension a x) -> (extender : ExtenderHomomorphism frex) -> Type
ExtenderPreservesVars frex extender = (other : Extension a x) ->
  (x ~~> cast other.Model).equivalence.relation
    ((extender other).H . frex.Var)
                         other.Var

public export 0
extenderIsUnique :  {pres : Presentation} -> {a : Model pres} -> {x : Setoid} ->
  (frex : Extension a x) -> (extender : Extender frex) -> Type
extenderIsUnique frex extender = (other : Extension a x) -> (extend : frex ~> other)
  -> (frex.Model ~~> other.Model).equivalence.relation
        extend.H
        (extender other).H

public export 0
Uniqueness :  {pres : Presentation} -> {a : Model pres} -> {x : Setoid} ->
  (frex : Extension a x) -> Type
Uniqueness frex = (other : Extension a x) -> (extend1, extend2 : frex ~> other)
  -> (frex.Model ~~> other.Model).equivalence.relation
        extend1.H
        extend2.H

public export 0
SinceExtenderIsUnique : {pres : Presentation} -> {a : Model pres} -> {x : Setoid} ->
  (frex : Extension a x) -> (extender : Extender frex) -> extenderIsUnique frex extender
  -> Uniqueness frex
SinceExtenderIsUnique frex extender prf other extend1 extend2
  = CalcWith @{cast $ frex.Model ~~> other.Model} $
  |~ extend1.H
  <~ (extender other).H ...(prf other extend1)
  <~ extend2.H          ...((frex.Model ~~> other.Model).equivalence.symmetric _ _ $
                            prf other extend2)

public export
record Universality {Pres : Presentation} {A : Model Pres} {X : Setoid}
            (Frex : Extension A X) where
  constructor IsUniversal
  Exists : Extender Frex
  Unique : Uniqueness Frex

public export
record Frex {Pres : Presentation} (A : Model Pres) (X : Setoid) where
  constructor MkFrex
  Data : Extension A X
  UP   : Universality Data

public export
(ford : pres.signature = sig) => Semantic (Frex {Pres = pres} a x) (Op sig) where
  (.SemType) c = c.Data.SemType
  (.Sem)     c = c.Data.Sem

public export
(ford : pres.signature = sig) => Semantic (Frex {Pres = pres} a x) (Term sig y) where
  (.SemType) c = c.Data.SemType
  (.Sem)     c = c.Data.Sem

public export
CoproductAlgebraWithFree : {pres : Presentation} -> {a : Model pres} -> {x : Setoid} ->
  (free : Free pres x) ->
  (coprod : Coproduct a free.Data.Model) ->
  Frex a x
CoproductAlgebraWithFree free coprod =
  let Fx : pres `ModelOver` x
      Fx = free.Data
      Tx : Model pres
      Tx = (Fx).Model
      aPlusFx : a <~.~> Tx
      aPlusFx = coprod.Data
      frexModel : Model pres
      frexModel = coprod.Data.Sink
      embed : a ~> frexModel
      embed = coprod.Data.Lft
      var : x ~> cast frexModel
      var = aPlusFx.Rgt.H . (Fx).Env
      frex  : Extension a x
      frex  = MkExtension frexModel embed var
      (.Over) : (other : Extension a x) -> pres `ModelOver` x
      (.Over) other = MkModelOver other.Model other.Var
      (.rgtOver) : (other : Extension a x) -> Fx ~> other.Over
      (.rgtOver) other = free.UP.Exists other.Over
      (.rgt)     : (other : Extension a x) -> Tx ~> other.Model
      (.rgt) other = other.rgtOver.H
      (.Cospan) : (other : Extension a x) -> a <~.~> (Fx).Model
      (.Cospan) other = MkCospan other.Model other.Embed other.rgt
      extenderCospan : (other : Extension a x) -> aPlusFx ~> other.Cospan
      extenderCospan other = coprod.UP.Exists other.Cospan
      extenderHomomorphism : ExtenderHomomorphism frex
      extenderHomomorphism other = (extenderCospan other).H
      extenderPreservesEmbed : ExtenderPreservesEmbedding frex extenderHomomorphism
      extenderPreservesEmbed other = (extenderCospan other).preserve.Lft
      extenderPreservesVar : ExtenderPreservesVars frex extenderHomomorphism
      extenderPreservesVar other i = CalcWith @{cast other.Model} $
        |~ (extenderHomomorphism other).H.H (var.H i)
        ~~ (extenderHomomorphism other).H.H (aPlusFx.Rgt.H.H ((Fx).Env.H i)) ...(Refl)
        <~ other.rgt.H.H ((Fx).Env.H i) ...((extenderCospan other).preserve.Rgt _)
        <~ other.Var.H i ...(other.rgtOver.preserves _)
      extender : Extender frex
      extender other = MkExtensionMorphism
        { H = extenderHomomorphism other
        , PreserveEmbed = extenderPreservesEmbed other
        , PreserveVar   = extenderPreservesVar   other
        }
      (.cospanMorphism) : {other : Extension a x} -> (extend : frex ~> other) ->
        aPlusFx ~> other.Cospan
      (.cospanMorphism) extend = MkCospanMorphism
        { H = extend.H
        , preserve = IsPreserving
          { Lft = extend.PreserveEmbed
          , Rgt = free.UP.Unique other.Over
                                (MkHomomorphism
                                  { H = extend.H . aPlusFx.Rgt
                                  , preserves = extend.PreserveVar
                                 })
                                other.rgtOver
          }
        }
      uniqueness : Uniqueness frex
      uniqueness other extend1 extend2 =
        coprod.UP.Unique
          other.Cospan
          extend1.cospanMorphism
          extend2.cospanMorphism
  in MkFrex
    { Data = frex
    , UP = IsUniversal
      { Exists = extender
      , Unique = uniqueness
      }
    }

public export
CoproductsAndFreeFrex : {pres : Presentation} ->
  (hasCoproducts : (a,b : Model pres) -> Coproduct a b) -> {x : Setoid} ->
  (free : Free pres x) -> (a : Model pres) -> Frex a x
CoproductsAndFreeFrex hasCoproducts free a =
  CoproductAlgebraWithFree free (hasCoproducts a free.Data.Model)

public export
Frexlet : {pres : Presentation} -> Type
Frexlet {pres} = (a : Model pres) -> {n : Nat} -> Frex a (cast $ Fin n)
