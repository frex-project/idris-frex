||| Definitions and constructions for coproducts in the category of models
module Frex.Coproduct

import Data.Setoid
import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model

infixr 3 <~.~>

||| A cospan between models of a presentation. Looks a bit like this: \o/
public export
record (<~.~>) {Pres : Presentation} (L, R : Model Pres) where
  constructor MkCospan
  ||| 'Head' of the cospan (\o/)
  Sink : Model Pres
  ||| Left 'arm' of the cospan (\o/)
  Lft  : L ~> Sink
  ||| Right 'arm' of the cospan (\o/)
  Rgt  : R ~> Sink

parameters {Pres : Presentation} {L, R : Model Pres} (C, D : L <~.~> R)
  ||| `Pres`-homomorphism preserving the Lft-arm of a cospan
  public export 0
  PreservesLft : (h : C .Sink ~> D .Sink) -> Type
  PreservesLft h = (L ~~> (D .Sink)).equivalence.relation
    (h . (C .Lft))
         (D .Lft)

  ||| `Pres`-homomorphism preserving the Rgt-arm of a cospan
  public export 0
  PreservesRgt : (h : C .Sink ~> D .Sink) -> Type
  PreservesRgt h = (R ~~> (D .Sink)).equivalence.relation
    (h . (C .Rgt))
         (D .Rgt)

||| A morphism preserving both arms of a cospan
public export
record Preserves 
    {Pres : Presentation} {L, R : Model Pres} (C, D : L <~.~> R) 
    (H : C .Sink ~> D .Sink) where
  constructor IsPreserving
  Lft : PreservesLft C D H
  Rgt : PreservesRgt C D H


||| A morphism between cospans
public export
record (~>) {Pres : Presentation} {L, R : Model Pres} (C, D : L <~.~> R) where
  constructor MkCospanMorphism
  ||| A morphism between the sinks
  H : C .Sink ~> D .Sink
  ||| Preserving both arms
  preserve : Preserves C D H

parameters {Pres : Presentation} {L, R : Model Pres} (Coprod : L <~.~> R)
  ||| Weak initiality: for any other cospan there is a cospan morphism from Coprod into it 
  public export
  Extender : Type
  Extender = (other : L <~.~> R) -> (Coprod ~> other)
  
  -- The following boilerplate lets us define a concrete `Extender` in stages.
  -- Were we to have co-pattern matching, we wouldn't need this boilerplate since we
  -- could define the various fields of Extender in stages
  
  ||| Data for function underlying an Extender   
  public export 0
  ExtenderFunction : Type
  ExtenderFunction = (other : L <~.~> R) -> U (Coprod .Sink) -> U (other.Sink)
  
  ||| Data for SetoidHomomorphism underlying an Extender
  public export 0
  ExtenderSetoidHomomorphism : Type
  ExtenderSetoidHomomorphism = (other : L <~.~> R) -> 
    cast {to = Setoid} (Coprod .Sink) ~> cast (other.Sink)
    
  ||| Data for AlgebraHomomorphism underlying an Extender
  public export 0
  ExtenderHomomorphism : Type
  ExtenderHomomorphism = (other : L <~.~> R) -> 
    (Coprod .Sink) ~> (other.Sink)
    
  ||| There's at most one cospan morphism out of `Coprod` into any other cospan
  public export 0
  Uniqueness : Type
  Uniqueness = (other : L <~.~> R) -> (extend1, extend2 : Coprod ~> other) -> 
    (Coprod .Sink ~~> other.Sink).equivalence.relation 
       extend1.H
       extend2.H

||| A cospan is (co)universal when it is initial       
public export
record Universality {Pres : Presentation} {L, R : Model Pres} (Coprod : L <~.~> R) where
  constructor IsUniversal
  Exists : Extender   Coprod
  Unique : Uniqueness Coprod

||| A coproduct of two models is a universal cospan between them
public export
record Coproduct {Pres : Presentation} (L, R : Model Pres) where
  constructor MkCoproduct
  Data : L <~.~> R
  UP : Universality Data
