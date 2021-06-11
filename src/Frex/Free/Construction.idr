||| Construct the free model over a setoid
||| Small print: the setoid's equivalence relation may not be decidable
module Frex.Free.Construction

import Data.Setoid
import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model
import Frex.Free
import Frex.Axiom

import Syntax.PreorderReasoning

%default total

infix 4 |-

record PresetoidAlgebra (Sig : Signature) where
  constructor MkPresetoidAlgebra
  algebra : Algebra Sig
  0 relation : (x, y : U algebra) -> Type

public export 0
U : PresetoidAlgebra sig -> Type
U a = U (a.algebra)

public export
data (|-)
  : {pres : Presentation} -> (a : PresetoidAlgebra pres.signature) -> 
    (x,y : U a) -> Type where

  Include : {pres : Presentation} -> {a : PresetoidAlgebra pres.signature} -> 
    {x,y : U a} -> a.relation x y ->
    (|-) {pres} a x y

  Refl : (x : U a) -> (|-) {pres} a x x
  Sym  : (|-) {pres} a x y -> (|-) {pres} a y  x
  Transitive : {x,y,z : U a} ->
    (|-) {pres} a x y -> 
    (|-) {pres} a y z -> 
    (|-) {pres} a x z

  ByAxiom : {pres : Presentation} -> {a : PresetoidAlgebra pres.signature} -> 
    (eq : Axiom pres) -> (env : (pres.axiom eq).Var -> U a) ->
    (|-) {pres} a (bindTerm {a = a.algebra} (pres.axiom eq).lhs env)
                  (bindTerm {a = a.algebra} (pres.axiom eq).rhs env)

  Congruence : {pres : Presentation} -> {a : PresetoidAlgebra pres.signature} -> 
    (t : Term pres.signature vars) -> {lhs, rhs : vars -> U a} -> 
    (eqForEq : (x : vars) -> (|-) {pres} a (lhs x) (rhs x)) ->
    (|-) {pres} a (bindTerm {a = a.algebra} t lhs)
                  (bindTerm {a = a.algebra} t rhs)
public export
QuotientModel : (pres : Presentation) -> (a : PresetoidAlgebra pres.signature) -> 
   Model pres
QuotientModel pres a =
  let quotient : Setoid
      quotient = MkSetoid (U a) $ MkEquivalence 
        { relation = (|-) {pres} a
        , reflexive = \x => Refl x
        , symmetric = \x,y,prf => Sym prf 
        , transitive = \x,y,z,prf1,prf2 => Transitive prf1 prf2
        }
  in MkModel 
  { Algebra = MkSetoidAlgebra 
    { algebra = a.algebra
    , equivalence = quotient.equivalence
    , congruence = \op, xs, ys, prf => CalcWith @{cast quotient} $
       |~ a.algebra.Sem op xs
       ~~ bindTerm {a = a.algebra} (Call op (tabulate Done)) (\i => index i xs) ...(sym $
            callEqSem _ _ _)
       <~ bindTerm {a = a.algebra} (Call op (tabulate Done)) (\i => index i ys) ...(
          Congruence (Call op (Fin.tabulate Done)) prf )
       ~~ a.algebra.Sem op ys ...(callEqSem _ _ _)
    }
  , Validate = ByAxiom 
  }

public export
data FreePresetoid
  : (sig : Signature) -> (x : Setoid) -> (u,v : Term sig (U x)) -> Type where
  Assume : x.equivalence.relation i j -> FreePresetoid sig x (Done i) (Done j)
  
public export
QuotientData : (pres : Presentation) -> (x : Setoid) -> PresetoidAlgebra pres.signature
QuotientData pres x = MkPresetoidAlgebra {Sig = pres.signature}
  { algebra = Free pres.signature (U x)
  , relation = FreePresetoid pres.signature x
  }
  
public export
F : (pres : Presentation) -> (x : Setoid) -> Model pres
F pres x = QuotientModel pres $ QuotientData pres x

public export
FreeDataEnv : (pres : Presentation) -> (x : Setoid) -> x ~> cast (F pres x)
FreeDataEnv pres x = MkSetoidHomomorphism
  { H = \i => Done {sig = pres.signature} i
  , homomorphic = \i,j,prf => Include (Assume prf)
  }

public export
FreeData : (pres : Presentation) -> (x : Setoid) -> pres `ModelOver` x
FreeData pres x = MkModelOver 
  { Model = F pres x
  , Env   = FreeDataEnv pres x
  }

public export
FreeUPExistsHHH : (pres : Presentation) -> (x : Setoid) -> ExtenderFunction (FreeData pres x)
FreeUPExistsHHH pres x other = flip (bindTerm {a = other.Model.Algebra.algebra}) (other.Env.H)

public export
FreeUPExistsHHHomomorphic : (pres : Presentation) -> (x : Setoid) -> (other : pres `ModelOver` x) -> 
  SetoidHomomorphism (cast $ F pres x) (cast {from = Model pres} $ other.Model) 
    (FreeUPExistsHHH pres x other)
FreeUPExistsHHHomomorphic pres x other (Done i) (Done j) (Include (Assume prf))  
  = other.Env.homomorphic i j prf
FreeUPExistsHHHomomorphic pres x other _ _ (Refl t ) 
  = (cast other.Model).equivalence.reflexive _
FreeUPExistsHHHomomorphic pres x other _ _ (Sym prf) 
  = (cast other.Model).equivalence.symmetric _ _ $ FreeUPExistsHHHomomorphic pres x other _ _ prf 
FreeUPExistsHHHomomorphic pres x other _ _ (Transitive prf1 prf2) 
  = (cast other.Model).equivalence.transitive _ _ _ (FreeUPExistsHHHomomorphic pres x other _ _prf1) 
                                                    (FreeUPExistsHHHomomorphic pres x other _ _prf2)
FreeUPExistsHHHomomorphic pres x other _ _ (ByAxiom eq env) 
  = CalcWith @{cast other.Model} $
  |~ bindTerm {a = other.Model.Algebra.algebra} 
        (bindTerm {a = Free _ _} 
           (pres.axiom eq).lhs env) 
        other.Env.H
  ~~ bindTerm {a = other.Model.Algebra.algebra} 
          (pres.axiom eq).lhs
          (\i => bindTerm {a = other.Model.Algebra.algebra} 
                (env i) 
                other.Env.H)                                ...(bindAssociative 
                                                                 {a = other.Model.Algebra.algebra} 
                                                                 _ _ _)
  <~ bindTerm {a = other.Model.Algebra.algebra} 
          (pres.axiom eq).rhs
          (\i => bindTerm {a = other.Model.Algebra.algebra} 
                (env i) 
                other.Env.H)                                ...(other.Model.Validate eq _)
  ~~ bindTerm {a = other.Model.Algebra.algebra} 
        (bindTerm {a = Free _ _} 
           (pres.axiom eq).rhs env) 
        other.Env.H                                         ...(sym $ 
                                                                bindAssociative 
                                                                  {a = other.Model.Algebra.algebra} 
                                                                  _ _ _)
FreeUPExistsHHHomomorphic pres x other _ _ (Congruence {vars, lhs, rhs} u eqForEq) = 
  let q = \i => FreeUPExistsHHHomomorphic pres x other _ _ (eqForEq i)
      lhs',rhs' : cast vars ~> cast other.Model
      lhs' = mate (FreeUPExistsHHH pres x other . lhs)
      rhs' = mate (FreeUPExistsHHH pres x other . rhs)
  in CalcWith @{cast other.Model} $
    |~ bindTerm {a = other.Model.Algebra.algebra}
         (bindTerm {a = Free _ _ } u lhs)
         other.Env.H
    ~~ bindTerm {a = other.Model.Algebra.algebra } u
         (\i : vars => 
           bindTerm {a = other.Model.Algebra.algebra}
             (lhs i)
             other.Env.H)                             ...(bindAssociative 
                                                            {a = other.Model.Algebra.algebra} 
                                                             _ _ _)
    <~ bindTerm {a = other.Model.Algebra.algebra } u
         (\i : vars => 
           bindTerm {a = other.Model.Algebra.algebra}
             (rhs i)
             other.Env.H)                             ...((Setoid.eval u).homomorphic lhs' rhs' q)
    ~~ bindTerm {a = other.Model.Algebra.algebra}
         (bindTerm {a = Free _ _ } u rhs)
         other.Env.H                                  ...(sym $ 
                                                          bindAssociative 
                                                            {a = other.Model.Algebra.algebra} 
                                                            _ _ _)

public export
FreeUPExistsHH : (pres : Presentation) -> (x : Setoid) -> ExtenderSetoidHomomorphism (FreeData pres x)
FreeUPExistsHH pres x other = 
  MkSetoidHomomorphism 
    { H = FreeUPExistsHHH pres x other
    , homomorphic = FreeUPExistsHHHomomorphic pres x other
    }

public export
FreeUPExists : (pres : Presentation) -> (x : Setoid) -> Extender (FreeData pres x)
FreeUPExists pres x other = 
        let homo : Term pres.signature (U x) -> U other.Model
            homo = FreeUPExistsHHH pres x other
        in MkHomomorphism 
        { H = MkSetoidHomomorphism 
            { H = FreeUPExistsHH pres x other
            , preserves = \op, xs => reflect (cast other.Model) $
                (Universality.eval {a = other.Model.Algebra.algebra}
                            other.Env.H).preserves op xs
            }
        , preserves = \x => reflect (cast other.Model) Refl
        }
        
public export
FreeUPUnique : (pres : Presentation) -> (x : Setoid) -> Uniqueness (FreeData pres x)

public export
FreeUPUniqueMap : (pres : Presentation) -> (x : Setoid) -> (other : pres `ModelOver` x) ->
  (extend1, extend2 : FreeData pres x  ~> other) ->
  forall n. (ts : Vect n (U $ F pres x)) -> 
            (VectSetoid n (cast other.Model)).equivalence.relation
               (map extend1.H.H.H ts)
               (map extend2.H.H.H ts)
FreeUPUniqueMap pres x other extend1 extend2 []          _ impossible
FreeUPUniqueMap pres x other extend1 extend2 (t :: _ )  FZ
  = FreeUPUnique pres x other extend1 extend2 t
FreeUPUniqueMap pres x other extend1 extend2 (_ :: ts) (FS i) 
  = FreeUPUniqueMap pres x other extend1 extend2 ts i

FreeUPUnique pres x other extend1 extend2 (Done j) 
  = CalcWith @{cast other.Model} $
    |~ extend1.H.H.H (Done j)
    <~ other.Env.H j          ...(extend1.preserves j)
    <~ extend2.H.H.H (Done j) ...((cast other.Model).equivalence.symmetric _ _ (extend2.preserves j))

FreeUPUnique pres x other extend1 extend2 (Call op xs) 
  = CalcWith @{cast other.Model} $
  |~  extend1.H.H.H (Call op xs)
  ~~  extend1.H.H.H ((F pres x).Sem op xs)      ...(Refl)
  <~  other.Model.Sem op (map extend1.H.H.H xs) ...(extend1.H.preserves op xs)
  <~  other.Model.Sem op (map extend2.H.H.H xs) ...(other.Model.Algebra.congruence op _ _ 
                                                   $ FreeUPUniqueMap pres x other extend1 extend2 xs)
  <~  extend2.H.H.H ((F pres x).Sem op xs)      ...((cast other.Model).equivalence.symmetric _ _ 
                                                 $ extend2.H.preserves op xs)
  ~~  extend2.H.H.H (Call op xs)                ...(Refl)
  
public export
FreeIsFree : (pres : Presentation) -> (x : Setoid) -> Freeness (FreeData pres x)
FreeIsFree pres x = IsFree 
    { Exists = FreeUPExists pres x        
    , Unique = FreeUPUnique pres x
    }

public export
Free : (pres : Presentation) -> (x : Setoid) -> Free pres x
Free pres x = MkFree 
  { Data = FreeData pres x
  , UP   = FreeIsFree pres x
  }

