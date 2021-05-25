||| Models for a `Frex.Presentation` and associated definitions
module Frex.Model

import Frex.Signature
import Frex.Algebra
import Frex.Presentation

import Data.Setoid
import Data.Vect
import Data.Vect.Extra

infix 1 =|

%default total

||| States: The `sig`-algebra `a` satisfies the equation `eq`: for all
||| environments, the interpretations of the lhs and rhs are in the
||| setoid equivalence.
public export 0
models : {sig : Signature} -> (a : SetoidAlgebra sig) -> (eq : Equation sig)
  -> (env : eq.Var -> U a.algebra) -> Type
models a eq env = a.equivalence.relation
                    (bindTerm {a = a.algebra} eq.lhs env)
                    (bindTerm {a = a.algebra} eq.rhs env)

||| Like `models`, but the arguments are reversed and packed slightly
||| more compactly, makes nice syntax sometimes
public export 0
(=|) : {sig : Signature} -> (eq : Equation sig) -> 
  (a : SetoidAlgebra sig ** eq.Var -> U a.algebra) -> Type
eq =| (a ** env) = models a eq env

||| States: `pres.signature`-algebra `a` satisfies all the axioms of `pres`.
public export 0
Validates : (pres : Presentation) -> (a : SetoidAlgebra pres.signature) -> Type
Validates pres a = (ax : pres.Axiom) -> (env : (pres.axiom ax).Var -> U a.algebra) ->
  pres.axiom ax =| (a ** env)

||| A model for an algebraic theory
public export
record Model (Pres : Presentation) where
  constructor MkModel
  ||| Algebra structure for the operations
  Algebra  : SetoidAlgebra (Pres).signature
  ||| The algebra validates all the equations
  Validate : Validates Pres Algebra

||| Type carrying the model
public export 0
U : {0 pres : Presentation} -> Model pres -> Type
U m = Algebra.U (m.Algebra.algebra)

||| Homomorphism between models
public export
(~>) : {pres : Presentation} -> (a, b : Model pres) -> Type
(~>) a b = a.Algebra ~> b.Algebra

||| Identity homomorphism between models
public export
id : (a : Model pres) -> a ~> a
id a = Setoid.id (a.Algebra)

-- Composition comes from Frex.Algebra already

||| Interpretation of an operator in a model
public export
Sem : {0 pres : Presentation} -> (a : Model pres) ->
  (f : Op pres.signature) -> (U a) ^ (arity f) -> U a
Sem a = a.Algebra.algebra.Sem

