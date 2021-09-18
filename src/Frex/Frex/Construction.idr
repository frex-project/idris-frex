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
import public Frex.Free.Construction
import Data.Setoid

import Decidable.Equality
import Decidable.Decidable

import Syntax.PreorderReasoning

public export
data EvaluationSigOperation : (sig : Signature) -> (0 a : Type) -> Nat -> Type where
  Op : sig.OpWithArity n -> EvaluationSigOperation sig a n
  Constant : a -> EvaluationSigOperation sig a 0

public export
EvaluationSig : (sig : Signature) -> (0 a : Type) -> Signature
EvaluationSig sig a = MkSignature $ EvaluationSigOperation sig a

export
(Show (Op sig), Show a) => Show (Op $ EvaluationSig sig a) where
  show (MkOp (Op op     )) = show (MkOp op)
  show (MkOp (Constant c)) = show c

export
HasPrecedence sig => HasPrecedence (EvaluationSig sig a) where
  OpPrecedence (Op op) = OpPrecedence op


depCong : {0 p : a -> Type} -> (0 f : (x : a) -> p x) -> {0 x1, x2 : a} -> (prf : x1 = x2) ->
  f x1 = f x2
depCong f Refl = Refl

depCong2 : {0 p : a -> Type} -> {0 q : (x : a) -> (y : p x) -> Type} ->
  (0 f : (x : a) -> (y : p x) -> q x y) ->
  {0 x1, x2 : a} -> (prf : x1 = x2) ->
  {0 y1 : p x1} -> {y2 : p x2} -> (prf : y1 = y2) ->
  f x1 y1 = f x2 y2
depCong2 f Refl Refl = Refl


OpInjective : {0 op1, op2 : Op sig} -> op1 = op2 -> (op1.fst = op2.fst, op1.snd ~=~ op2.snd)
OpInjective Refl = (Refl, Refl)

OpEq : (arity1 = arity2) ->
  {0 op1 : sig.OpWithArity arity1} ->
  {0 op2 : sig.OpWithArity arity2} ->
  (op1 ~=~ op2) -> MkOp {Sig=sig, fst = arity1} op1 = MkOp {Sig=sig, fst = arity2} op2
OpEq Refl Refl = Refl

OpEqEvalSig : (arity1 = arity2) ->
  {0 op1 : sig.OpWithArity arity1} ->
  {0 op2 : sig.OpWithArity arity2} ->
  (op1 ~=~ op2) ->
  MkOp {Sig=EvaluationSig sig a, fst = arity1} (Op op1) =
  MkOp {Sig=EvaluationSig sig a, fst = arity2} (Op op2)
OpEqEvalSig Refl Refl = Refl


export
(DecEq (Op sig), DecEq a) => DecEq (Op (EvaluationSig sig a)) where
  decEq (MkOp {fst = fst1} (Op op1)) (MkOp {fst = fst2} (Op op2)) =
    case decEq (MkOp op1) (MkOp op2) of
      Yes op1_eq_op2 => Yes $ OpEqEvalSig
                          (fst $ OpInjective op1_eq_op2)
                          (snd $ OpInjective op1_eq_op2)
      No contra => No (\Refl => contra $ Refl)
  decEq (MkOp (Op op1)) (MkOp (Constant c2)) = No $ \case Refl impossible
  decEq (MkOp (Constant c1)) (MkOp (Op op2)) = No $ \case Refl impossible
  decEq (MkOp (Constant c1)) (MkOp (Constant c2)) = case decEq c1 c2 of
    Yes Refl  => Yes Refl
    No contra => No $ \Refl => contra Refl

export
(Eq (Op sig), Eq a) => Eq (Op (EvaluationSig sig a)) where
  (MkOp (Op op1     )) == (MkOp (Op op2     )) = (MkOp op1) == (MkOp op2)
  (MkOp (Op op1     )) == (MkOp (Constant c2)) = False
  (MkOp (Constant c1)) == (MkOp (Op op2     )) = False
  (MkOp (Constant c1)) == (MkOp (Constant c2)) = c1 == c2

export
(Ord (Op sig), Ord a) => Ord (Op (EvaluationSig sig a)) where
  compare (MkOp (Op op1     )) (MkOp (Op op2     )) = (MkOp op1) `compare` (MkOp op2)
  compare (MkOp (Op op1     )) (MkOp (Constant x )) = GT
  compare (MkOp (Constant c )) (MkOp (Op x       )) = LT
  compare (MkOp (Constant c1)) (MkOp (Constant c2)) = c1 `compare` c2


public export
EvalEmbed : (sig : Signature) -> sig ~> EvaluationSig sig a
EvalEmbed _ = OpTranslation Op

public export
data EvaluationAxiom : (sig : Signature) -> (axioms : Type) -> (a : Setoid) -> Type where
  Axiom : axioms -> EvaluationAxiom sig axioms a
  Evaluation  : {n : Nat} -> (f : sig.OpWithArity n) -> (cs : Vect n (U a)) ->
    EvaluationAxiom sig axioms a
  Assumption : {x,y : U a} -> a.equivalence.relation x y -> EvaluationAxiom sig axioms a

export
Show axioms => Show (EvaluationAxiom sig axioms a) where
  show (Axiom ax) = show ax
  show (Evaluation f cs) = "Evaluate"
  show (Assumption x)    = "Assumption"

public export
EvaluationTheory : (pres : Presentation) -> (a : SetoidAlgebra pres.signature) ->
  (ax : EvaluationAxiom pres.signature pres.Axiom (cast a)) ->
  Equation (EvaluationSig pres.signature (U a))
EvaluationTheory pres a (Axiom ax       ) = cast @{castEqHint @{EvalEmbed pres.signature}} $
  pres.axiom ax
EvaluationTheory pres a (Evaluation f cs) = Presentation.MkEq
  { support = 0
  , lhs = Call (MkOp (Op f)) (map (\x => Call (MkOp $ Constant x) []) cs)
  , rhs = Call (MkOp $ Constant $ a.Sem (MkOp f) cs) []
  }
EvaluationTheory pres a (Assumption {x,y} _) = Presentation.MkEq
  { support = 0
  , lhs = Call (MkOp $ Constant x) []
  , rhs = Call (MkOp $ Constant y) []
  }

public export
EvaluationPresentation : (pres : Presentation) -> (a : SetoidAlgebra pres.signature) -> Presentation
EvaluationPresentation pres a = MkPresentation
  { signature = EvaluationSig pres.signature (U a)
  , Axiom = EvaluationAxiom pres.signature pres.Axiom (cast a)
  , axiom = EvaluationTheory pres a
  }

namespace Algebra
  public export
  castEval : SetoidAlgebra (EvaluationSig sig a) ->
         SetoidAlgebra sig
  castEval a = MkSetoidAlgebra
    { algebra = MakeAlgebra
      { U = U a
      , Semantics = \op => a.algebra.Semantics $ MkOp $ Op $ snd op
      }
    , equivalence = a.equivalence
    , congruence = \op => a.congruence (MkOp $ Op $ snd op)
    }

  export
  lemma : {0 sig : Signature} -> {0 x : Type} -> {auto a : Algebra sig} ->
    (n : Nat) -> (f : Fin n -> x) -> (env : x -> U a) ->
    bindTerms {a} (map Done (tabulate f)) env = tabulate (env . f)
  lemma  0    f env = Refl
  lemma (S n) f env = cong (env (f FZ) ::) $ lemma n (f . FS) env

  export
  lemma2 : {0 sig : Signature} -> {0 x : Type} -> {auto a : Algebra sig} ->
    (i : Fin n) -> (ts : Vect n (Term sig x)) -> (env : x -> U a) ->
    index i (bindTerms {a} ts env) = bindTerm {a} (index i ts) env
  lemma2 i ts env = Calc $
    |~ index i (bindTerms {a} ts env)
    ~~ index i (map (flip a.Sem env) ts) ...(cong (index i) $ bindTermsIsMap {a} _ _)
    ~~ bindTerm {a} (index i ts) env    ...(indexNaturality _ _ _)

  export
  coherence : {sig : Signature} -> {s,x : Type} ->
    (a : SetoidAlgebra (EvaluationSig sig s)) -> (t : Term sig x) -> (env : x -> U a) ->
     a.Sem (Signature.cast @{EvalEmbed sig {a = s}} t) env ===
     (castEval a).Sem t env

  export
  coherenceTerms : {sig : Signature} -> {s, x : Type} ->
    (a : SetoidAlgebra (EvaluationSig sig s)) -> (ts : Vect n (Term sig x)) -> (env : x -> U a) ->
     bindTerms {a = a.algebra               } (castTerms (EvalEmbed sig {a = s}) ts) env ===
     bindTerms {a = (castEval a).algebra} ts env
  coherenceTerms a [] env = Refl
  coherenceTerms a (t :: ts) env = cong2 (::) (coherence a t env) (coherenceTerms a ts env)

  coherence a (Done i) env = Refl
  coherence a (Call f ts) env = cong (a.algebra.Semantics (MkOp (Op (f.snd)))) $
    irrelevantEq $ Calc $
    |~ bindTerms {a = a.algebra} (bindTerms {a = Free _ _} (map Done (tabulate Prelude.id))
         (flip index (castTerms (EvalEmbed sig {a = s}) ts))) env
    ~~ bindTerms {a = a.algebra} (map Done (tabulate Prelude.id))
         (\i => bindTerm {a = a.algebra} (index i (castTerms (EvalEmbed sig {a = s}) ts)) env)
       ...(bindTermsAssociative {a = a.algebra} _ _ _)
    ~~ tabulate (\i => bindTerm {a = a.algebra} (index i (castTerms (EvalEmbed sig {a = s}) ts)) env)
       ...(lemma {a = a.algebra} _ Prelude.id _)
    ~~ bindTerms {a = a.algebra} (castTerms (EvalEmbed sig {a = s}) ts) env
       ...(vectorExtensionality _ _ $ \i => Calc $
         -- Not my best moment, sorry
         |~ index i (Fin.tabulate _)
         ~~ _ ...(indexTabulate _ _)
         ~~ _ ...(sym $ lemma2 {a = a.algebra} _ _ _))
    ~~ bindTerms {a = (castEval a).algebra} ts env ...(coherenceTerms a _ _)

namespace Model
  public export
  castEval : {pres : Presentation} -> {a : SetoidAlgebra pres.signature} ->
    Model (EvaluationPresentation pres a) -> (Model pres)
  castEval ea = MkModel
    { Algebra = castEval ea.Algebra
    , Validate = \ax,env => CalcWith @{cast ea} $
      |~ (castEval ea.Algebra).Sem (pres.axiom ax).lhs env
      ~~ ea.Algebra.Sem (Signature.cast @{EvalEmbed pres.signature {a = U a}}
            (pres.axiom ax).lhs) env
          ...(sym $ coherence ea.Algebra _ _)
      <~ ea.Algebra.Sem (Signature.cast @{EvalEmbed pres.signature {a = U a}}
            (pres.axiom ax).rhs) env
          ...(ea.Validate (Axiom ax) env)
      ~~ (castEval ea.Algebra).Sem (pres.axiom ax).rhs env
          ...(irrelevantEq $ coherence ea.Algebra _ _)
    }

namespace Homomorphism
  public export
  castEval : {sig : Signature} -> {0 a : Type} ->
    {b,c : SetoidAlgebra (EvaluationSig sig a)} -> (b ~> c) -> (castEval b ~> castEval c)
  castEval h = MkSetoidHomomorphism
    { H = h.H
    , preserves = \op => h.preserves (MkOp $ Op op.snd)
    }

public export
freeAsExtension : {pres : Presentation} -> {a : Model pres} -> {s : Setoid} ->
  (fs : Free.Definition.Free (EvaluationPresentation pres a.Algebra) s) -> Extension a s
freeAsExtension fs = MkExtension
  { Model = castEval fs.Data.Model
  , Embed = MkSetoidHomomorphism
      { H = MkSetoidHomomorphism
        { H = \i => fs.Data.Model.sem (Constant i)
        , homomorphic = \x,y,prf => fs.Data.Model.validate (Assumption prf) []
        }
      , preserves = \(MkOp op),xs =>
        CalcWith @{cast fs.Data.Model} $
        |~ (fs.Data.Model.sem (Constant $ a.Sem (MkOp op) xs))
        <~ fs.Data.Model.Sem (Call
                    {sig = (EvaluationPresentation pres a.Algebra).signature, a = Fin 0}
                  (MkOp (Construction.Op op))
                  (map (\x => Call (MkOp $ Constant x) []) xs))
                  (flip index Vect.Nil)
           ...(fs.Data.Model.equivalence.symmetric _ _ $
                 fs.Data.Model.validate (Evaluation op xs) [])
        ~~ fs.Data.Model.Algebra.algebra.Semantics (MkOp $ Construction.Op op)
           (map (\i => fs.Data.Model.sem (Constant i)) xs)
           ...(cong (fs.Data.Model.Algebra.algebra.Semantics (MkOp $ Construction.Op op)) $
               vectorExtensionality _ _ $ \i => Calc $
               -- Sorry, this will do for now
               |~ index i (bindTerms {a = fs.Data.Model.Algebra.algebra}
                    (map (\x => Call (MkOp (Constant x)) []) xs)
                    (flip index []))
               ~~ index i (map (flip (bindTerm {a = fs.Data.Model.Algebra.algebra}) (flip index []))
                             $ map (\x => Call (MkOp (Constant x)) []) xs)
                  ...(cong (index i) $ bindTermsIsMap {a = fs.Data.Model.Algebra.algebra} _ _)
               ~~ bindTerm {a = fs.Data.Model.Algebra.algebra}
                     (index i (map (\x => Call (MkOp (Constant x)) []) xs))
                           (flip index [])
                  ...(indexNaturality _ _ _)
               ~~ fs.Data.Model.Algebra.algebra.Semantics (MkOp (Constant (index i xs))) []
                  ...(cong (\t => bindTerm {a = fs.Data.Model.Algebra.algebra} t (flip index [])) $
                        indexNaturality _ _ _)
               ~~ index i (map (\i => (fs.Data.Model.Algebra.algebra.Semantics
                    (MkOp (Constant i)) Vect.Nil)) xs)
               ...(sym $ indexNaturality _ _ _))
      }
  , Var = fs.Data.Env
  }


public export
(.OverAlgebra) : {pres : Presentation} -> {a : Model pres} -> {s : Setoid} ->
  (other : Extension a s) ->
  SetoidAlgebra (EvaluationPresentation pres a.Algebra).signature
other.OverAlgebra = MkSetoidAlgebra
  { algebra = MakeAlgebra
      { U = U other.Model
      , Semantics = \case
          MkOp (Op op     ) => other.Model.Algebra.algebra.Semantics (MkOp op)
          MkOp (Constant i) => \_ => other.Embed.H.H i
      }
  , equivalence = other.Model.equivalence
  , congruence = \case
      MkOp {fst = arity} (Op op     ) => \xs,ys,prf =>
        other.Model.Algebra.congruence (MkOp op) xs ys prf
      MkOp (Constant i) => \_,_,_ => other.Model.equivalence.reflexive _
  }

export
(.OverAlgebraCoherence) : {pres : Presentation} -> {a : Model pres} -> {s : Setoid} ->
  (other : Extension a s) ->
  (env : x -> U other.Model) -> (t : Term pres.signature x) ->
    (castEval other.OverAlgebra).Sem t env
    = other.Model.Sem t env

export
OverAlgebraCoherenceAux : {pres : Presentation} -> {a : Model pres} -> {s : Setoid} ->
  (other : Extension a s) ->
  (env : x -> U other.Model) -> (ts : Vect n $ Term pres.signature x) ->
    bindTerms {a = (castEval other.OverAlgebra).algebra} ts env
    = bindTerms {a = other.Model.Algebra.algebra} ts env
OverAlgebraCoherenceAux other env [] = Refl
OverAlgebraCoherenceAux other env (t :: ts) = cong2 (::)
  (other.OverAlgebraCoherence env t)
  (OverAlgebraCoherenceAux other env ts)

other.OverAlgebraCoherence env (Done i   ) = Refl
other.OverAlgebraCoherence env (Call (MkOp op) ts) =
  cong (other.Model.Algebra.algebra.Semantics (MkOp op)) $
    OverAlgebraCoherenceAux other env ts

export
OverAlgebraNop : {pres : Presentation} -> {a : Model pres} -> {s : Setoid} ->
  (other : Extension a s) -> (xs : Vect n (U a)) -> (env : x -> U other.Model) ->
  bindTerms {a = other.OverAlgebra.algebra}
    (map (\x => Call (MkOp $ Constant x) []) xs)
    env
  === map other.Embed.H.H xs
OverAlgebraNop other xs env = vectorExtensionality _ _ $ \i => Calc $
 |~ index i (bindTerms {a = other.OverAlgebra.algebra}
               (map (\x => Call (MkOp $ Constant x) []) xs)
               env)
 ~~ index i (map (flip (bindTerm {a = other.OverAlgebra.algebra}) env)
               (map (\x => Call (MkOp $ Constant x) []) xs))
                                     ...(cong (index i) $
                                         bindTermsIsMap {a = other.OverAlgebra.algebra}
                                         _ _)
 ~~ bindTerm {a = other.OverAlgebra.algebra}
     (index i (map (\x => Call (MkOp $ Constant x) []) xs))
     env  ...(indexNaturality _ _ _)
 ~~ other.Embed.H.H (index i xs)
       ...(cong (\u => bindTerm {a = other.OverAlgebra.algebra} u env) $
           indexNaturality _ (\x => Call (MkOp $ Constant x) []) _)
 ~~ index i (map other.Embed.H.H xs) ...(sym $ indexNaturality _ _ _)

public export
(.Over) : {pres : Presentation} -> {a : Model pres} -> {s : Setoid} ->
  (other : Extension a s) ->
  (EvaluationPresentation pres a.Algebra) `ModelOver` s
other.Over = MkModelOver
  { Model = MkModel
      { Algebra = other.OverAlgebra
      , Validate = \case
          Axiom ax        => \env => CalcWith @{cast other.Model} $
            |~ other.OverAlgebra.Sem (Signature.cast @{EvalEmbed pres.signature {a = U a}}
                 (pres.axiom ax).lhs) env
            ~~ (castEval other.OverAlgebra).Sem (pres.axiom ax).lhs env
               ...(irrelevantEq $ coherence other.OverAlgebra _ _)
            ~~ other.Model.Sem (pres.axiom ax).lhs env
               ...(other.OverAlgebraCoherence _ _)
            <~ other.Model.Sem (pres.axiom ax).rhs env
               ...(other.Model.Validate ax env)
            ~~ (castEval other.OverAlgebra).Sem (pres.axiom ax).rhs env
               ...(sym $ other.OverAlgebraCoherence _ _)
            ~~ other.OverAlgebra.Sem (Signature.cast @{EvalEmbed pres.signature {a = U a}}
                 (pres.axiom ax).rhs) env
               ...(sym $ irrelevantEq $ coherence other.OverAlgebra _ _)
          Evaluation f cs => \env => CalcWith @{cast other.Model} $
            |~ other.Model.Algebra.algebra.Semantics (MkOp f)
                 (bindTerms {a = other.OverAlgebra.algebra}
                   (map (\x => Call (MkOp (Constant x)) []) cs) env)
            ~~ other.Model.Algebra.algebra.Semantics (MkOp f)
                 (map other.Embed.H.H cs)
                 ...(cong (other.Model.Algebra.algebra.Semantics (MkOp f)) $
                     OverAlgebraNop other _ _)
            <~ other.Embed.H.H (a.Sem (MkOp f) cs)
               ...(other.Model.equivalence.symmetric _ _ $
                   other.Embed.preserves (MkOp f) _)
          Assumption xyEq => \env => other.Embed.H.homomorphic _ _ xyEq
      }
  , Env   = other.Var
  }

public export
Extender : {pres : Presentation} -> {a : Model pres} -> {s : Setoid} ->
  (fs : Free.Definition.Free (EvaluationPresentation pres a.Algebra) s) ->
  Extender (freeAsExtension {a} fs)
Extender fs other =
  let h : fs.Data ~> other.Over
      h = fs.UP.Exists other.Over
  in MkExtensionMorphism
  { H = MkSetoidHomomorphism
    { H = h.H.H
    , preserves = \case
        MkOp op => \xs => h.H.preserves (MkOp $ Construction.Op op) xs
    }
  , PreserveEmbed = \i => CalcWith @{cast other.Model} $
    |~ h.H.H.H (fs.Data.Model.sem (Constant i))
    <~ other.Over.Model.sem (Constant i) ...(h.H.preserves (MkOp $ Constant i) [])
  , PreserveVar   = h.preserves
  }

public export
Uniqueness : {pres : Presentation} -> {a : Model pres} -> {s : Setoid} ->
  (fs : Free.Definition.Free (EvaluationPresentation pres a.Algebra) s) ->
  Uniqueness (freeAsExtension {a} fs)
Uniqueness fs other extend1 extend2 =
 let lemma : (extend : (freeAsExtension {a} fs) ~> other) -> fs.Data ~> other.Over
     lemma extend = MkHomomorphism
       { H = MkSetoidHomomorphism
           { H = extend.H.H
           , preserves = \case
               MkOp (Op op     ) => extend.H.preserves (MkOp op)
               MkOp (Constant i) => \ [] => extend.PreserveEmbed i
           }
       , preserves = extend.PreserveVar
       }
 in fs.UP.Unique other.Over (lemma extend1) (lemma extend2)


public export
FrexByFree : {pres : Presentation} -> {a : Model pres} -> {s : Setoid} ->
  (fs : Free.Definition.Free (EvaluationPresentation pres a.Algebra) s) ->
  Frex a s
FrexByFree fs = MkFrex
  { Data = freeAsExtension {a} fs
  , UP = IsUniversal
    { Exists = Extender {a} fs
    , Unique = Uniqueness {a} fs
    }
  }

public export
Frex : {pres : Presentation} -> (a : Model pres) -> (s : Setoid) -> Frex a s
Frex a s = FrexByFree {a}
         $ Frex.Free.Construction.Free (EvaluationPresentation pres a.Algebra) s
