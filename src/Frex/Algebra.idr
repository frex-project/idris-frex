||| Algebras for a `Frex.Signature` and associated definitions
module Frex.Algebra

import Frex.Signature
import public Notation
import public Notation.Semantic

import Data.Setoid
import Data.Nat
import Data.Nat.Order

import public Data.Vect
import public Data.Vect.Elem
import public Data.Vect.Properties
import public Data.Rel

import Control.WellFounded

import Syntax.PreorderReasoning
import Decidable.Order
import Syntax.PreorderReasoning.Generic

import Data.Vect.Extra

infix 10 ^
infix 5 ~>, <~>

||| N-ary tuples
public export
(^) : Type -> Nat -> Type
(^) a n = Vect n a

||| Curry a function from n-tuples to an n-ary function
public export
curry : {n : Nat} -> (f : a ^ n -> a) -> n `ary` a
curry {n = 0  } f = f []
curry {n = S n} f = \x => curry (\xs => f (x :: xs))

||| Uncurry an n-ary function into a function from n-tuples
public export
uncurry : {n : Nat} -> (f : n `ary` a) -> a ^ n -> a
uncurry {n = 0  } f xs = f
uncurry {n = S n} f xs = Algebra.uncurry (f $ head xs) (tail xs)

||| States: each operation has an interpretation
public export
algebraOver : (sig : Signature) -> (a : Type) -> Type
sig `algebraOver` a = (f : Op sig) -> a ^ (arity f) -> a

public export
algebraOver' : (sig : Signature) -> (a : Type) -> Type
sig `algebraOver'` a = {n : Nat} -> (f : sig.OpWithArity n) -> n `ary` a


||| An algebra for a signature Sig consists of:
||| @U : A type called the carrier
||| @Sem : a semantic interpretation for each Sig-operation
||| The smart constructor `MkAlgebra` is more usable in concrete cases
public export
record Algebra (Sig : Signature) where
  constructor MakeAlgebra
  0 U   : Type
  Semantics : Sig `algebraOver` U

public export
Semantic (Algebra sig) (Op sig) where
  (.SemType) a op = (U a) ^ (arity op) -> U a
  (.Sem) a op = a.Semantics op

||| Smart constructor for an algebra for a signature Sig:
||| @U : A type called the carrier
||| @Sem : a semantic interpretation for each Sig-operation
public export
MkAlgebra : {0 Sig : Signature} -> (0 U : Type) -> (Sem : Sig `algebraOver'` U) -> Algebra Sig
MkAlgebra u sem = MakeAlgebra u \f => uncurry (sem (snd f))

||| Algebraic terms of this signature with variables in the given type
public export
data Term : (0 sig : Signature) -> Type -> Type where
  ||| A variable with the given index
  Done : {0 sig : Signature} -> a -> Term sig a
  ||| An operator, applied to a vector of sub-terms
  Call : {0 sig : Signature} -> (f : Op sig) -> Vect (arity f) (Term sig a)
         -> Term sig a

------------------ Functor, Applicative, Monad -------------------------------------------

public export total
bindTerm : {0 sig : Signature} -> {0 x : Type} -> {auto a : Algebra sig}
  -> (t : Term sig x) -> (env : x -> U a)
  -> (U a)


public export total
bindTerms : {0 sig : Signature} -> {0x : Type} -> {auto a : Algebra sig}
  -> (ts : Vect n (Term sig x)) -> (env : x -> U a)
  -> Vect n (U a)

bindTerms  [] env = []
bindTerms (t :: ts) env = bindTerm t env :: bindTerms ts env

bindTerm (Done i) env = env i
bindTerm (Call f xs) env = a.Sem f $ bindTerms  xs env


public export
Semantic (Algebra sig) (Term sig x) where
  (.SemType) a t = (env : x -> U a) -> U a
  (.Sem) a t = bindTerm t

||| Specifies `bindTerms` specialises `map bindTerm`.
export
bindTermsIsMap : {auto a : Algebra sig}
  -> (xs : Vect n (Term sig x)) -> (env : x -> U a)
  -> bindTerms {a} xs env = map (flip a.Sem env) xs
bindTermsIsMap [] env = Refl
bindTermsIsMap (y :: xs) env = cong (bindTerm y env ::) $ bindTermsIsMap xs env

||| The free `sig`-algebra over over a given type
public export
Free : (0 sig : Signature) -> (0 x : Type) -> Algebra sig
Free sig x = MakeAlgebra (Term sig x) Call

||| The corresponding  n-ary operation over the term algebra
public export
call : {n : Nat} -> sig.OpWithArity n -> n `ary` (Term sig x)
call f = curry (Call (MkOp f))

||| Smart constructor for variables
public export
X : {0 sig : Signature} -> Fin k -> Term sig (Fin k)
X = Done

public export
Functor (Term sig) where
  map h t = (Free sig _).Sem t (Done . h)

public export
Applicative (Term sig) where
  pure = Done
  (<*>) fs ts = (Free sig _).Sem fs \f =>
                (Free sig _).Sem ts \x =>
                Done (f x)

public export
Monad (Term sig) where
  (>>=) = (Free sig _).Sem

||| Free `sig`-algebra over `n`-variables.
public export
TermAlgebra : (0 sig : Signature) -> (n : Nat) -> Algebra sig
TermAlgebra sig n = Free sig (Fin n)

export total
bindTermsPureRightUnit : {0 sig : Signature} -> {0 x : Type}
    -> (ts : Vect n (Term sig x))
    -> bindTerms {a = Free _ _} ts Prelude.pure = ts

||| Monad law corresponding to right unit law of monoids
export total
bindPureRightUnit : {0 sig : Signature} -> {0 x : Type}
    -> (t : Term sig x)
    -> t >>= Prelude.pure = t
bindPureRightUnit (Done i) = Refl
bindPureRightUnit (Call f xs) = cong (Call f) $ bindTermsPureRightUnit _

bindTermsPureRightUnit [] = Refl
bindTermsPureRightUnit (t :: ts)
  = cong2 (::) (bindPureRightUnit t)
               (bindTermsPureRightUnit ts)

-- It'll be useful to also have algebras quotiented by a
-- proof-relevant relation
namespace Setoid
  ||| The equivalence relation on `a` is a congruence w.r.t. the operation `f`.
  public export 0
  CongruenceWRT : {n : Nat} -> (a : Setoid) -> (f : (U a) ^ n -> U a) -> Type
  CongruenceWRT a f = SetoidHomomorphism (VectSetoid n a) a f

  ||| Equality is always a congruence
  export
  EqualCongruence : {n : Nat} -> (f : a ^ n -> a) -> CongruenceWRT (cast a) f
  EqualCongruence f xs ys prf = cong f $ vectorExtensionality _ _ prf

  ||| A setoid algebra: an algebra over a setoid whose equivalence
  ||| relation respects all the algebraic operations
  public export
  record SetoidAlgebra (Sig : Signature) where
    constructor MkSetoidAlgebra
    ||| Underlying algebra
    algebra : Algebra Sig
    ||| Equivalence relation making the carrier a setoid
    equivalence : Equivalence (U algebra)
    ||| All algebraic operations respect the equivalence relation
    congruence : (f : Op Sig) -> (MkSetoid (U algebra) equivalence) `CongruenceWRT` (algebra.Sem f)

  public export
  Semantic (SetoidAlgebra sig) (Op sig) where
    (.SemType) a op = a.algebra.SemType op
    (.Sem) a op = a.algebra.Sem op

  public export
  Semantic (SetoidAlgebra sig) (Term sig x) where
    (.SemType) a = a.algebra.SemType
    (.Sem) a = a.algebra.Sem

  public export 0
  U : SetoidAlgebra sig -> Type
  U a = Algebra.U a.algebra

  public export
  Cast (SetoidAlgebra sig) Setoid where
    cast a = MkSetoid (U $ a.algebra) (equivalence a)

  public export total
  cast : (a : SetoidAlgebra sig) -> Preorder (U a) (a.equivalence.relation)
  cast a = cast $ Prelude.cast {to = Setoid} a

  public export
  Cast (Algebra sig) (SetoidAlgebra sig) where
    cast a = MkSetoidAlgebra
      { algebra = a
      , equivalence = EqualEquivalence (U a)
      , congruence = \f, xs, ys, ext => cong (a.Sem f) $ vectorExtensionality _ _ ext
      }
  namespace Homomorphism
    public export
    cast : {a : SetoidAlgebra sig} -> (f : Op sig) ->
      VectSetoid (arity {sig} f) (Prelude.cast a) ~> cast a
    cast f = MkSetoidHomomorphism (a.Sem f) (a.congruence f)

-------------------- Homomorphisms -------------------------------

  ||| States: the function `h : U a -> U b` preserves the `sig`-operation `f`
  public export 0
  Preserves : {sig : Signature}
           -> (a, b : SetoidAlgebra sig) -> (h : U a -> U b) -> (f : Op sig) -> Type
  Preserves {sig} a b h f
    = (xs : Vect (arity f) (U a))
      -> b.equivalence.relation (h $ a.Sem f xs) (b.Sem f (map h xs))

  ||| States: the function `h : U a -> U b` preserves all `sig`-operations
  public export 0
  Homomorphism : {sig : Signature} -> (a, b : SetoidAlgebra sig) -> (h : U a -> U b) -> Type
  Homomorphism a b h = (f : Op sig) -> Preserves a b h f

  ||| Homomorphisms between Setoid `Sig`-algebras
  ||| @H : setoid morphism between the carriers
  ||| @preserves : satisfying the homomorphism property
  public export
  record (~>) {Sig : Signature} (a, b : SetoidAlgebra Sig) where
    constructor MkSetoidHomomorphism
    ||| Underlying Setoid homomorphism
    H : cast {to = Setoid} a ~> cast b
    ||| Preservation of `Sig`-operations up to the setoid's equivalence
    preserves : Homomorphism a b (.H H)

  {- NB: We need to have a Setoid homomorphism, to allow preserving
     the operations up to the setoid equivalence.
  -}

  public export
  id : (a : SetoidAlgebra sig) -> a ~> a
  id a = MkSetoidHomomorphism (Setoid.Definition.id $ cast a)
          \f,xs => CalcWith @{cast a} $
          |~ a.Sem f xs
          ~~ a.Sem f (map id xs) ...(cong (a.Sem f) $ sym (mapId _))

  public export
  (.) : {a,b,c : SetoidAlgebra sig} -> b ~> c -> a ~> b -> a ~> c
  g . f  = MkSetoidHomomorphism (H g . H f) \op, xs => CalcWith @{cast c} $
    |~ g.H.H (f.H.H (a.Sem op xs))
    <~ g.H.H (b.Sem op (map (.H f.H) xs))        ...(g.H.homomorphic _ _ $ f.preserves op xs)
    <~ c.Sem op (map g.H.H (map f.H.H     xs))   ...(g.preserves op _)
    ~~ c.Sem op (map (\x => g.H.H (f.H.H x)) xs) ...(cong (c.Sem op)
                                                            $ mapFusion _ _ _)

-- Back to (non-setoid) Algebra

public export 0
(~>) : (a,b : Algebra sig) -> Type
a ~> b = cast {to=SetoidAlgebra sig} a ~> cast b

||| States: `(>>= f) : Free sig x -> a` is an algebra homomorphism
export
bindHom : {0 sig : Signature} -> {0 x : Type} -> {a : Algebra sig} -> (env : x -> U a)
  -> Homomorphism {sig} (cast $ Free sig x) (cast a) (flip (bindTerm {a}) env)
bindHom env f ts = cong (a.Sem f) (bindTermsIsMap _ _)

namespace Universality
  ||| Like Algebra.(>>=), but pack the `sig`-homomorphism structure
  public export
  eval : {0 sig : Signature} -> {0 x : Type} -> {auto a : Algebra sig} -> (env : x -> U a)
          -> Free sig x ~> a
  eval env = MkSetoidHomomorphism (mate $ flip bindTerm env) (bindHom env)

public export
bindAssociative : {0 sig : Signature} -> {0 x, y : Type} -> {auto a : Algebra sig}
  -> (t : Term sig x) -> (f : x -> Term sig y) -> (g : y -> U a)
  -> bindTerm (bindTerm {a = Free _ _} t f) g
     = bindTerm {a} t (\i : x => bindTerm {a} (f i) g)

public export
bindTermsAssociative : {0 sig : Signature} -> {0 x, y : Type} -> {auto a : Algebra sig}
  -> (ts : Vect n $ Term sig x) -> (f : x -> Term sig y) -> (g : y -> U a)
  -> bindTerms {a} (bindTerms {a = Free _ _} ts f) g
     = bindTerms {a} ts (\x => bindTerm {a} (f x) g)
bindTermsAssociative    []     f g = Refl
bindTermsAssociative (t :: ts) f g
  = cong2 (::) (bindAssociative      t  f g)
               (bindTermsAssociative ts f g)

bindAssociative (Done i    ) f g = Refl
bindAssociative (Call op xs) f g
  = cong (a.Sem op)
         (bindTermsAssociative xs f g)

namespace Setoid
  ||| The setoid equivalence is a congruence wrt. all algebraic terms
  export total
  bindCongruence : {0 sig : Signature} -> {0 x : Setoid} -> {a : SetoidAlgebra sig}
    -> (t : Term sig (U x)) -> SetoidHomomorphism (x ~~> cast a) (cast a)
         (\u => bindTerm {a = a.algebra} t (u.H))

  ||| Auxiliary function used in the inductive argument for `bindCongruence`
  export total
  bindTermsCongruence : {0 sig : Signature} -> {0 x : Setoid} -> {a : SetoidAlgebra sig}
    -> (ts : Vect n $ Term sig (U x)) -> SetoidHomomorphism (x ~~> cast a) (VectSetoid n $ cast a)
         (\u => bindTerms {a = a.algebra} ts (u.H))
  bindTermsCongruence (t :: _ ) f g prf FZ     = bindCongruence t f g prf
  bindTermsCongruence (_ :: ts) f g prf (FS i) = bindTermsCongruence ts f g prf i

  bindCongruence (Done v   ) f g prf = prf _
  bindCongruence {a} (Call op xs) f g prf
    = a.congruence op (bindTerms {a = a.algebra} xs f.H)
                      (bindTerms {a = a.algebra} xs g.H)
                      (\i => bindTermsCongruence xs f g prf i)

  ||| Evaluation of algebraic terms in a SetoidAlgebra is a setoid homomorphism
  public export
  eval : {0 sig : Signature} -> {0 x : Setoid} -> {a : SetoidAlgebra sig}
    -> (t : Term sig (U x)) -> (x ~~> cast a) ~> (cast a)
  eval t = MkSetoidHomomorphism (\env => bindTerm {a = a.algebra} t env.H) (bindCongruence t)

  {- NB: even once we define the power of `a` by `x`, `eval t : (x ~~>  a) ~> a` may not
         be a homomorphism of `SetoidAlgebra`. Eg:

         For example (an instance of the Eckmann-Hilton argument):

         Take `a` to be a non-commutative monoid, with u,v
         non-commuting, for example, strings with concatenation:

           t : Term Monoid Bool
           t = True * False
           f True  = a.Sem 1 []
           f False = u
           g True  = v
           g False = a.sem 1 []

           and then:

           eval t (f * g) = eval t \case {True => 1 * v; False => u * 1}
                          = (v * u)

           while:

           (eval t f) * (eval t g) = (1 * u) * (v * 1) = u * v

           and these are different.
  -}

namespace Term
  ||| Every term over x induces an `x`-ary operation.
  ||| States: `h` preserves the this operation.
  public export 0
  Preserves : (a,b : SetoidAlgebra sig) -> (h : U a -> U b) -> (t : Term sig x) -> Type
  Preserves a b h t = (env : x -> U a) ->
  b.equivalence.relation
    (h (bindTerm {a = a.algebra} t env))
    (bindTerm {a = b.algebra} t (h . env))

  ||| Homomorphism preserve all algebraic operations
  public export
  homoPreservesSem : {a,b : SetoidAlgebra sig} -> (h : a ~> b) -> (t : Term sig x) ->
    Preserves a b h.H.H t

  ||| Auxiliary generalisation to prove `homoPreservesSem`.
  public export
  homoPreservesSemMap : {a,b : SetoidAlgebra sig} -> (h : a ~> b) -> (ts : Vect n $ Term sig x) ->
    (env : x -> U a) ->
    (VectSetoid n $ cast b).equivalence.relation
      (map h.H.H (bindTerms {a = a.algebra} ts env))
      (bindTerms {a = b.algebra} ts (h.H.H . env))
  homoPreservesSemMap h (t :: ts) env  FZ    = homoPreservesSem h t env
  homoPreservesSemMap h (t :: ts) env (FS i) = homoPreservesSemMap h ts env i

  homoPreservesSem h (Done v    ) env = b.equivalence.reflexive _
  homoPreservesSem h (Call op ts) env = CalcWith @{cast b} $
    |~ h.H.H (a.Sem op (bindTerms {a = a.algebra} ts env))
    <~ b.Sem op (map h.H.H $ bindTerms {a = a.algebra} ts env) ...(h.preserves op _)
    <~ b.Sem op (bindTerms {a = b.algebra} ts (h.H.H . env))   ...(b.congruence op _ _
                                                                          $ homoPreservesSemMap {a,b}
                                                                              h ts env)
public export
record (<~>) {0 sig : Signature} (a, b : SetoidAlgebra sig) where
  constructor MkIsomorphism
  Iso : cast {to = Setoid} a <~> cast b
  FwdHomo : Homomorphism a b (Iso).Fwd.H

public export
BwdHomo : {0 sig : Signature} -> (a, b : SetoidAlgebra sig) ->
  (iso : a <~> b) -> Homomorphism b a (iso.Iso).Bwd.H
BwdHomo a b iso f xs = CalcWith @{cast a} $
  let id' : cast b ~> cast b
      id' = (iso.Iso.Fwd) . (iso.Iso.Bwd)
  in
  |~ iso.Iso.Bwd.H (b.Sem f xs)
  <~ iso.Iso.Bwd.H (b.Sem f (map iso.Iso.Fwd.H (map iso.Iso.Bwd.H xs)))
          ...((iso.Iso.Bwd . cast f).homomorphic _ _
             $ CalcWith @{cast $ VectSetoid _ $ cast b}
             $ |~ xs
               <~ map (id b).H.H xs ...(\i => reflect (cast b) $ sym $ indexNaturality _ id _)
               <~ map (iso.Iso.Fwd.H . iso.Iso.Bwd.H) xs
                    ...(let id_eq_id' = (cast b ~~> cast b).equivalence.symmetric
                              id' (id b).H
                              (iso.Iso.Iso.FwdBwdId)
                        in (VectMap).homomorphic (id b).H id' id_eq_id' xs)
               ~~ map iso.Iso.Fwd.H (map iso.Iso.Bwd.H xs)
                    ...(sym $ mapFusion _ _ _))
  <~ iso.Iso.Bwd.H (iso.Iso.Fwd.H (a.Sem f (map iso.Iso.Bwd.H xs)))
                                            ...(iso.Iso.Bwd.homomorphic _ _
                                               $ b.equivalence.symmetric _ _
                                               $ iso.FwdHomo f _)
  <~ a.Sem f (map iso.Iso.Bwd.H xs) ...(iso.Iso.Iso.BwdFwdId _)

||| Reverse an isomorphism
public export
sym : {a, b : SetoidAlgebra sig} -> a <~> b -> b <~> a
sym iso = MkIsomorphism (sym iso.Iso) (BwdHomo _ _ iso)


public export
{a : SetoidAlgebra sig} -> {b : SetoidAlgebra sig} -> Cast (a <~> b) (a ~> b) where
  cast iso = MkSetoidHomomorphism iso.Iso.Fwd iso.FwdHomo

||| The setoid of homomorphisms between algebras with pointwise equivalence.
public export
(~~>) : (a, b : SetoidAlgebra sig) -> Setoid
%unbound_implicits off
(~~>) a b = Quotient (a ~> b)
                      {b = (cast {to = Setoid} a) ~~> cast b}
                     (\h => h.H)
%unbound_implicits on

||| nary interpretation of an operator in an algebra
public export
(.sem) : {n : Nat} -> (a : SetoidAlgebra sig) -> (op : sig.OpWithArity n) -> n `ary` (U a)
(.sem) {n} a op = Algebra.curry $ a.Sem (MkOp op)

||| Each operation in the signature is an algebraic operation
public export
callEqSem : {sig : Signature} -> (a : Algebra sig) -> (op : Op sig)
  -> (xs : Vect (arity op) (U a)) ->
     (bindTerm {a} (Call op (tabulate Done)) (\i => index i xs))
     =
     (a.Sem op xs)
callEqSem a op xs = Calc $
  |~ bindTerm (Call op (tabulate Done)) (\i => index i xs)
  ~~ a.Sem op (map (flip bindTerm (\i => index i xs)) (tabulate Done))
       ...((Universality.eval {a} (\i => index i xs)).preserves op (tabulate Done))
  ~~ a.Sem op (tabulate (\i => index i xs))
       ...(cong (a.Sem op) $ sym $ mapTabulate _ _)
  ~~ a.Sem op xs ...(cong (a.Sem op) $ vectorExtensionality _ _ $ indexTabulate _)
