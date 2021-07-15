||| Construct the free monoid over a setoid `s` by freely extending
||| the free monoid over the empty setoid by the setoid `s`
module Frex.Free.Construction.ByFrex

import Data.Setoid
import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model
import Frex.Free.Definition
import Frex.Frex

public export
record Parameters (Pres : Presentation) (s : Setoid) where
  constructor MkParameters
  Initial : Free Pres (cast Void)
  FrexBy  : Frex (Initial).Data.Model s

%name Parameters param

-- A model over s has the same data as an extension of the initial model by s
public export
(.toModelOver) : {auto param : Parameters pres s} ->
  Extension param.Initial.Data.Model s -> pres `ModelOver` s
ext.toModelOver = MkModelOver
  { Model = ext.Model
  , Env   = ext.Var
  }

public export
(.OverVoid) : (model : Model pres) -> pres `ModelOver` (cast Void)
model.OverVoid = MkModelOver
  { Model = model
  , Env   = mate $ \case _ impossible
  }

public export
(.initiality) : {auto param : Parameters pres s} ->
  (model : Model pres) -> param.Initial.Data.Model ~> model
model.initiality = (param.Initial.UP.Exists model.OverVoid).H

public export
(.homomorphism) : {a : pres `ModelOver` (cast Void)} -> {b : Model pres} ->
  (h : a.Model ~> b) -> a ~> b.OverVoid
h.homomorphism = MkHomomorphism
  { H = h
  , preserves = \case _ impossible
  }

public export
(.toExtension) : {auto param : Parameters pres s} ->
  pres `ModelOver` s -> Extension param.Initial.Data.Model s
modelOver.toExtension = MkExtension
  { Model = modelOver.Model
  , Embed = modelOver.Model.initiality
  , Var   = modelOver.Env
  }

public export
(.toExtensionMorphism) : {auto param : Parameters pres s} ->
  {mod1 : Extension param.Initial.Data.Model s} -> {mod2 : pres `ModelOver` s} ->
  (h : mod1.toModelOver ~> mod2) ->
  mod1 ~> mod2.toExtension
h.toExtensionMorphism = MkExtensionMorphism
  { H = h.H
  , PreserveEmbed = param.Initial.UP.Unique
      mod2.Model.OverVoid
      (h.H . mod1.Embed).homomorphism
      (mod2.toExtension.Embed).homomorphism
  , PreserveVar   = h.preserves
  }

public export
FreeModelOver : Parameters pres s -> pres `ModelOver` s
FreeModelOver param = param.FrexBy.Data.toModelOver

public export
Extender : (param : Parameters pres s) -> Extender (FreeModelOver param)
Extender param other = MkHomomorphism
  { H = (param.FrexBy.UP.Exists other.toExtension).H
  , preserves = (param.FrexBy.UP.Exists other.toExtension).PreserveVar
  }

public export
Uniqueness : (param : Parameters pres s) -> Uniqueness (FreeModelOver param)
Uniqueness param other extend1 extend2 = param.FrexBy.UP.Unique
  other.toExtension
  extend1.toExtensionMorphism
  extend2.toExtensionMorphism

public export
ByFrex : (initial : Free pres (cast Void)) -> Frex initial.Data.Model s -> Free pres s
ByFrex initial frex =
  let params = MkParameters
        { Initial = initial
        , FrexBy  = frex
        }
  in MkFree
    { Data = FreeModelOver params
    , UP   = IsFree
        { Exists = Extender params
        , Unique = Uniqueness params
        }
    }
