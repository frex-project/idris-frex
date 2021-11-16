||| Models for a `Frex.Presentation` and associated definitions
module Frex.Model

import Frex.Signature
import Frex.Algebra
import Frex.Presentation

import Data.Setoid
import Data.Vect
import Data.Vect.Extra
import Data.HVect
import Data.Fin

infix 1 =|

%default total
%ambiguity_depth 4

||| States: The `sig`-algebra `a` satisfies the equation `eq`: for all
||| environments, the interpretations of the lhs and rhs are in the
||| setoid equivalence.
public export 0
models : {sig : Signature} ->
  (a : SetoidAlgebra sig) -> (eq : Equation sig) ->
  (env : Fin eq.support -> U a.algebra) -> Type
models a eq env = a.equivalence.relation
    (a.Sem eq.lhs env)
    (a.Sem eq.rhs env)

||| Like `models`, but the arguments are reversed and packed slightly
||| more compactly, makes nice syntax sometimes
public export 0
(=|) : {sig : Signature} -> (eq : Equation sig) ->
  (a : SetoidAlgebra sig ** Fin eq.support -> U a.algebra) -> Type
eq =| (a ** env) = models a eq env

||| Homomorphisms preserve equations in an environment
public export
eqPreservation : {sig : Signature} -> (eq : (Term sig x, Term sig x)) ->
  {a,b : SetoidAlgebra sig} -> (env : x -> U a) ->
  (h : a ~> b) ->
  a.equivalence.relation
    (a.Sem (fst eq) env)
    (a.Sem (snd eq) env) ->
  b.equivalence.relation
    (b.Sem (fst eq) (h.H.H . env))
    (b.Sem (snd eq) (h.H.H . env))
eqPreservation eq env h prf = CalcWith (cast b) $
  |~ b.Sem (fst eq) (h.H.H . env)
  ~~ h.H.H (a.Sem (fst eq) env) ..<(homoPreservesSem h (fst eq) env)
  ~~ h.H.H (a.Sem (snd eq) env) ...(h.H.homomorphic _ _ prf)
  ~~ b.Sem (snd eq) (h.H.H . env) ...(homoPreservesSem h (snd eq) env)

||| States: `pres.signature`-algebra `a` satisfies the given equation.
public export 0
ValidatesEquation : (eq : Equation sig) ->
  (a : SetoidAlgebra sig) -> Type
ValidatesEquation eq a =
  (env : Fin eq.support -> U a.algebra) ->
  eq =| (a ** env)


||| States: `pres.signature`-algebra `a` satisfies all the axioms of `pres`.
public export 0
Validates : (pres : Presentation) ->
  (a : SetoidAlgebra pres.signature) -> Type
Validates pres a = (ax : pres.Axiom) ->
  ValidatesEquation (pres.axiom ax) a

parameters {0 sig : Signature} {a, b : SetoidAlgebra sig} (iso : a <~> b)
  ||| Isomorphisms let us replace the semantics of one algebra with another
  public export
  semPreservation : (t : Term sig x) -> (env : x -> U b) ->
    b.equivalence.relation
      (bindTerm {a = b.algebra} t env)
      (iso.Iso.Fwd.H $ a.Sem t (iso.Iso.Bwd.H . env))
  semPreservation {x} t env = CalcWith (cast b) $
    let id_b' : cast b ~> cast b
        id_b' = (iso.Iso.Fwd) . (iso.Iso.Bwd)
    in
    |~ b.Sem t env
    ~~ b.Sem t (iso.Iso.Fwd.H . (iso.Iso.Bwd.H . env))
             ...((eval {a = b, x = irrelevantCast x} t).homomorphic
                   (mate env)
                   (iso.Iso.Fwd . (iso.Iso.Bwd . mate env))
                $ \i => (cast {to = Setoid} b ~~> cast b).equivalence.symmetric id_b' (id b).H
                         iso.Iso.Iso.FwdBwdId
                         (env i))
    ~~ iso.Iso.Fwd.H (bindTerm {a = a.algebra} t (iso.Iso.Bwd.H . env))
             ...(b.equivalence.symmetric _ _ $
                   homoPreservesSem (cast {to = a ~> b} iso) t (iso.Iso.Bwd.H . env))

  ||| Isomorphisms preserve all equations
  public export
  isoPreservesEq : (eq : Equation sig) ->
    (env : Fin eq.support -> U b)  -> eq =| (a ** iso.Iso.Bwd.H . env) -> eq =| (b ** env)
  isoPreservesEq eq env prf = CalcWith (cast b) $
    let env' : Fin eq.support -> U a
        env' = iso.Iso.Bwd.H . env
    in
    |~ b.Sem eq.lhs env
    ~~ iso.Iso.Fwd.H (bindTerm {a = a.algebra} eq.lhs env') ...(semPreservation eq.lhs env)
    ~~ iso.Iso.Fwd.H (bindTerm {a = a.algebra} eq.rhs env') ...(_.homomorphic _ _ prf)
    ~~ b.Sem eq.rhs env                                     ..<(semPreservation eq.rhs env)

||| Algebra isomorphisms preserve transport models
public export
isoPreservesModels : (pres : Presentation) -> {a,b : SetoidAlgebra pres.signature}
  -> (a <~> b) -> Validates pres a -> Validates pres b
isoPreservesModels pres iso prf ax env = isoPreservesEq iso (pres.axiom ax) env $ prf ax _

||| A model for an algebraic theory
public export
record Model (Pres : Presentation) where
  constructor MkModel
  ||| Algebra structure for the operations
  Algebra  : SetoidAlgebra (Pres).signature
  ||| The algebra validates all the equations
  Validate : Validates Pres Algebra

{-
  So the next few lines are a bit... silly. Here's what's happening.

  What we want to write is this:

  Semantic (Model pres) (Op pres.signature) where
    (.SemType) a = a.Algebra.SemType
    (.Sem)     a = a.Algebra.Sem


  However, that's not going to work in practice.

  In this implementation above, we have a metavariable `pres`.  Idris2
  currently refuses to solve any metavariables as part of interface
  resolution. As a consequence, even if unification works out that
  `a ~ Model pres0`, it won't propagate that to solve `pres ~ pres0`.

  To get around that, we use a forded auto-implicit:
-}

public export
(ford : pres.signature = sig) => Semantic (Model pres) (Op sig) where
  (.SemType) a = (replace {p = SetoidAlgebra} ford a.Algebra).SemType
  (.Sem)     a = (replace {p = SetoidAlgebra} ford a.Algebra).Sem

public export
(ford : pres.signature = sig) => Semantic (Model pres) (Term sig x) where
  (.SemType) a = (replace {p = SetoidAlgebra} ford a.Algebra).SemType
  (.Sem)     a = (replace {p = SetoidAlgebra} ford a.Algebra).Sem

public export
Cast (Model pres) Setoid where
  cast a = cast a.Algebra

public export
cast : (a : Model pres) -> Preorder (a.Algebra.algebra.U) (a.Algebra.equivalence.relation)
cast a = cast a.Algebra

||| Type carrying the model
public export 0
U : {0 pres : Presentation} -> Model pres -> Type
U m = Algebra.U (m.Algebra.algebra)

public export
(.equivalence) : (a : Model pres) -> Equivalence (U a)
(.equivalence) a = a.Algebra.equivalence

||| Equivalence relation underlying a model
public export 0
(.rel) : (a : Model pres) -> (x, y : U a) -> Type
(.rel) a = a.equivalence.relation

||| Homomorphism between models
public export
(~>) : {pres : Presentation} -> (a, b : Model pres) -> Type
(~>) a b = a.Algebra ~> b.Algebra

||| Identity homomorphism between models
public export
id : (a : Model pres) -> a ~> a
id a = Setoid.id (a.Algebra)

-- Composition comes from Frex.Algebra already

||| nary interpretation of an operator in a model
public export
(.sem) : {n : Nat} -> (a : Model pres) -> (op : pres.signature.OpWithArity n) -> n `ary` (U a)
(.sem) a op = Algebra.curry $ a.Sem (MkOp op)

||| The setoid of homomorphisms between models with pointwise equivalence.
public export
(~~>) : (a, b : Model pres) -> Setoid
(~~>) a b = a.Algebra ~~> b.Algebra

public export
transport : {pres : Presentation} -> (a : Model pres) ->
  {b : SetoidAlgebra (pres.signature)} ->
  (a.Algebra <~> b) ->
   Model pres
transport a iso = MkModel b $
  isoPreservesModels pres iso a.Validate

%unbound_implicits off
||| N-ary congruence in a term with `n` varialbes
public export
(.cong) : {0 pres : Presentation} -> (a : Model pres) -> (0 n : Nat)
  -> (t : Term pres.signature (U a `Either` Fin n))
  -> (lhs, rhs : Vect n (U a))
  -> HVect (tabulate $ \i => (cast a).equivalence.relation
       (index i lhs)
       (index i rhs))
  -> (cast a).equivalence.relation
       (a.Sem t $ either Prelude.id $ flip index lhs)
       (a.Sem t $ either Prelude.id $ flip index rhs)
(.cong) a n t lhs rhs prfs
  = (Setoid.eval {x = cast $ U a `Either` Fin n} t).homomorphic
      (mate $ either Prelude.id $ flip index lhs)
      (mate $ either Prelude.id $ flip index rhs)
      $ \case
        Left  x => (cast a).equivalence.reflexive x
        Right i => replace {p = id}
              (indexTabulate _ _)
              (index i prfs)
%unbound_implicits on

public export
Dyn : (i : Fin n) -> Term sig (a `Either` Fin n)
Dyn i = Done (Right i)

public export
Sta : (x : a) -> Term sig (a `Either` Fin n)
Sta x = Done (Left x)

public export
(.validate) : (a : Model pres) -> (ax : Axiom pres) ->
  (env : Vect (support $ pres.axiom ax) (U a)) ->
  (pres.axiom ax) =| (a.Algebra ** \ i => index i env)
a.validate ax env = a.Validate ax (\ i => index i env)
