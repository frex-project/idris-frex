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
F : {pres : Presentation} -> (x : Setoid) -> Model pres
F {pres} x = QuotientModel pres $ QuotientData pres x
  
public export
Free : (pres : Presentation) -> (x : Setoid) -> Free pres x
%unbound_implicits off
-- If only we had copatterns...
Free pres x = MkFree 
  { Data = MkModelOver 
      { Model = F x
      , Env   = MkSetoidHomomorphism
        { H = \i => Done {sig = pres.signature} i
        , homomorphic = \i,j,prf => Include (Assume prf)
        }
      }
  , UP   = IsFree 
    { Exists = \other => 
        let homo : Term pres.signature (U x) -> U other.Model
            homo = flip (bindTerm {a = other.Model.Algebra.algebra}) (other.Env.H)
        in MkHomomorphism 
        { H = MkSetoidHomomorphism 
            { H = MkSetoidHomomorphism
                  { H = homo
                  , homomorphic = let 
                      lemma : {t, s : Term pres.signature (U x)} -> 
                              (prf : (|-) {pres} (QuotientData pres x) t s) ->
                              (cast other.Model).equivalence.relation
                                 (homo t)
                                 (homo s)
                      lemma {t = Done i, s = Done j} (Include (Assume prf)) 
                        = other.Env.homomorphic i j prf
                      lemma (Refl t ) = (cast other.Model).equivalence.reflexive _
                      lemma (Sym prf) = (cast other.Model).equivalence.symmetric _ _ $ lemma prf
                      lemma (Transitive prf1 prf2) 
                        = (cast other.Model).equivalence.transitive _ _ _ (lemma prf1) 
                                                                          (lemma prf2)
                      lemma (ByAxiom eq env) = CalcWith @{cast other.Model} $
                        |~ bindTerm {a = other.Model.Algebra.algebra} 
                              (bindTerm {a = Free _ _} 
                                 (pres.axiom eq).lhs env) 
                              other.Env.H
                        ~~ _ {-bindTerm {a = Free pres.signature (U x)} 
                                (pres.axiom eq).lhs
                                (\i => bindTerm {a = other.Model.Algebra.algebra} 
                                      (env i) 
                                      other.Env.H)-}
                           ...(bindAssociative {a = other.Model.Algebra.algebra} _ _ _)
                        <~ _ ...(other.Model.Validate eq _)
                        ~~ bindTerm {a = other.Model.Algebra.algebra} 
                              (bindTerm {a = Free _ _} 
                                 (pres.axiom eq).rhs env) 
                              other.Env.H
                            ...(sym $ bindAssociative {a = other.Model.Algebra.algebra} _ _ _)
                      lemma (Congruence {vars, lhs, rhs} u eqForEq) = 
                         let q = \x => lemma (eqForEq x)
                             lhs',rhs' : cast vars ~> cast other.Model
                             lhs' = mate (homo . lhs)
                             rhs' = mate (homo . rhs)
                             p := (Setoid.eval {x = cast vars
                                               , sig = pres.signature} u).homomorphic  
                                  lhs' rhs' q
                         in CalcWith @{cast other.Model} $
                           |~ bindTerm {a = other.Model.Algebra.algebra}
                                (bindTerm {a = Free _ _ } u lhs)
                                other.Env.H
                           ~~ _ {-bindTerm {a = Free pres.signature vars } u
                                (\i : vars => 
                                  bindTerm {a = other.Model.Algebra.algebra}
                                    (lhs i)
                                    other.Env.H)-}
                                ...(bindAssociative {a = other.Model.Algebra.algebra} 
                                      _ _ _)
                           <~ _ ...(p)
                           ~~ bindTerm {a = other.Model.Algebra.algebra}
                                (bindTerm {a = Free _ _ } u rhs)
                                other.Env.H
                                ...(sym $ bindAssociative {a = other.Model.Algebra.algebra} _ _ _)
                    in \t,s => lemma {t} {s}
                  }
            , preserves = \op, xs => reflect (cast other.Model) $
                (Universality.eval {a = other.Model.Algebra.algebra}
                            other.Env.H).preserves op xs
            }
        , preserves = \x => reflect (cast other.Model) Refl
        }
    , Unique = \other, extend1, extend2 => 
                 let Other : Setoid
                     Other = cast {from = Model pres} other.Model
                     FX : Model pres
                     FX = F x
                     lemma : (t : U (FX)) -> (Other).equivalence.relation
                         (extend1.H.H.H t)
                         (extend2.H.H.H t)
                     lemmaMap : forall n. (ts : Vect n (U $ FX)) -> 
                       (VectSetoid n Other).equivalence.relation
                         (map extend1.H.H.H ts)
                         (map extend2.H.H.H ts)
                     lemmaMap [] _ impossible
                     lemmaMap (t :: ts) FZ     = lemma t
                     lemmaMap (t :: ts) (FS i) = lemmaMap ts i
                       
                     lemma donej@(Done j) = 
                       -- This is truly messed up. There's a bug somewhere in the typechecker.
                       -- Still true though!
                       let u : Other .equivalence.relation
                                 (extend1.H.H.H donej)
                                 (other.Env.H j)
                           u = extend1.preserves j
                           v := Other .equivalence.symmetric _ _ (extend2.preserves j)
                       in CalcWith @{cast Other} $
                       |~ extend1.H.H.H donej
                       <~ other.Env.H j          ...(u)
                       <~ extend2.H.H.H donej    ...(v)
                    
                     lemma (Call op xs) = CalcWith @{cast Other} $
                       |~  extend1.H.H.H (Call op xs)
                       ~~  extend1.H.H.H ((FX).Sem op xs) ...(Refl)
                       <~  other.Model.Sem op (map extend1.H.H.H xs) ...(extend1.H.preserves op xs)
                       <~  other.Model.Sem op (map extend2.H.H.H xs) 
                            ...(other.Model.Algebra.congruence op _ _ $ lemmaMap xs)
                       <~  extend2.H.H.H ((FX).Sem op xs)   ...((Other).equivalence.symmetric _ _ 
                                                               $ extend2.H.preserves op xs)
                       ~~  extend2.H.H.H (Call op xs)                ...(Refl)
                 in lemma
    }
  } 
%unbound_implicits on
