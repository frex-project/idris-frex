||| The definition of what a power is
module Frex.Powers.Definition

import Data.Setoid
import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model

import Data.Vect
import Data.Vect.Properties

||| A parameterisation 
public export
record Parameterisation (Pres : Presentation)(X : Setoid)(A : Model Pres) where
  constructor MkParameterisation
  Model : Model Pres
  Eval : X ~> (Model ~~> A)
  
parameters {Pres : Presentation} {X : Setoid} {A : Model Pres}
  ||| Model/algebra homomorphism that is also a parametrisation morphism
  public export 0
  PreservesEvaluation : (v,w : Parameterisation Pres X A)
    -> (h : v.Model ~> w.Model) -> Type
  PreservesEvaluation v w h = (f : U v.Model) -> (i : U X) -> 
    (cast A).equivalence.relation
      ((w.Eval.H i).H.H (h.H.H f))
      ((v.Eval.H i).H.H         f)
      
-- Need to repeat this for records, see #1482
parameters {Pres : Presentation} {X : Setoid} {A : Model Pres}
  public export
  record (~>) (V, W : Parameterisation Pres X A) where
    constructor MkParameterisationMorphism
    H : V .Model ~> W .Model
    0 preserve : PreservesEvaluation V W H
    
  parameters (XtoA : Parameterisation Pres X A)
    public export 0
    Extension : Type
    Extension = (other : Parameterisation Pres X A)
               -> other  ~> XtoA

    public export 0
    UniqueExtension : (other : Parameterisation Pres X A) -> 
      (extend : other ~> XtoA) -> Type
    UniqueExtension other extend = (extend1, extend2 : other ~> XtoA) ->
       (f : U $ other.Model) -> (cast $ XtoA .Model).equivalence.relation
          (extend1.H.H.H f)
          (extend2.H.H.H f)
    
    public export 0
    Uniqueness : Extension -> Type
    Uniqueness extend = (other : Parameterisation Pres X A) ->
      UniqueExtension other (extend other)
    
parameters {Pres : Presentation} {X : Setoid} {A : Model Pres} 
  public export
  record Universality (XtoA : Parameterisation Pres X A) where
    constructor  IsUniversal
    Exists : Extension XtoA
    0 Unique : Uniqueness XtoA Exists
  
public export
record Power {Pres : Presentation} (X : Setoid) (A : Model Pres) where
  constructor MkPower
  Data : Parameterisation Pres X A
  UP   : Universality Data
