||| Construct the free extension of a model over a setoid
||| Small print: the setoid's equivalence relation may not be decidable
|||
||| The frex `a[s]` of a `pres`-model `a` over a setoid `s` is given
||| by the free model `F s` of the following presentation over the
||| setoid `s`. First, we add all the elements `x : U a` as constants
||| `Constant x : 0`. Then, we add the following evaluation equations
||| to the `pres` axioms:
|||
|||   f (Constant x1, ..., Constant xn)
|||   = Constant $ a.Sem f (x1,..., xn)
module Frex.Frex.Construction

import Frex.Signature
import Frex.Algebra
import Frex.Presentation
import Frex.Model
import Frex.Axiom

import Frex.Frex
import Frex.Free

public export
data EvaluationSigOperation : (sig : Signature) -> (a : Type) -> Nat -> Type where
  Op : sig.OpWithArity n -> EvaluationSigOperation sig a n
  Constant : a -> EvaluationSigOperation sig a 0

public export
EvaluationSig : (sig : Signature) -> (a : Type) -> Signature
EvaluationSig sig a = MkSignature $ EvaluationSigOperation sig a

public export
EvalEmbed : (sig : Signature) -> sig ~> EvaluationSig sig a
EvalEmbed _ = OpTranslation \op => Op op

public export
data EvaluationAxiom : (sig : Signature) -> (axioms : Type) -> (a : Type) -> Type where
  Axiom : axioms -> EvaluationAxiom sig axioms a
  Evaluation  : {n : Nat} -> (f : sig.OpWithArity n) -> (cs : Vect n a) ->
    EvaluationAxiom sig axioms a

public export
EvaluationTheory : (pres : Presentation) -> (a : Algebra pres.signature) ->
  (ax : EvaluationAxiom pres.signature pres.Axiom (U a)) ->
  Equation (EvaluationSig pres.signature (U a))
EvaluationTheory pres a (Axiom ax       ) = cast @{castEqHint @{EvalEmbed pres.signature}} $
  pres.axiom ax
EvaluationTheory pres a (Evaluation f cs) = MkEq
  { Var = Fin 0
  , lhs = Call (MkOp (Op f)) (map (\x => Call (MkOp $ Constant x) []) cs)
  , rhs = Call (MkOp $ Constant $ a.Sem (MkOp f) cs) []
  }
