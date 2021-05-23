||| Algebras for a `Frex.Signature` and associated definitions
module Frex.Algebra

import Frex.Signature
import Notation

import Data.Setoid
import Data.Nat
import Data.Nat.Order

import public Data.Vect
import public Data.Vect.Elem
import Data.Vect.Properties
import Data.Rel

import Control.WellFounded

import Syntax.PreorderReasoning
import Decidable.Order
import Syntax.PreorderReasoning.Generic

import Data.Vect.Extra

infix 10 ^
infix 5 ~>

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
sig `algebraOver` a = (f : sig.Op) -> a ^ (sig.arity f) -> a

||| An algebra for a signature Sig consists of:
||| @U : A type called the carrier
||| @Sem : a semantic interpretation for each Sig-operation
public export
record Algebra (Sig : Signature) where
  constructor MkAlgebra
  0 U   : Type
  Sem : Sig `algebraOver` U
  
||| States: the function `h : U a -> U b` preserves the `sig`-operation `f`
public export 0
Preserves : {sig : Signature}
         -> (a, b : Algebra sig) -> (h : U a -> U b) -> (f : sig.Op) -> Type
Preserves {sig} a b h f
  = (xs : Vect (sig.arity f) (U a)) 
    -> h (a.Sem f xs) = b.Sem f (map h xs)

||| States: the function `h : U a -> U b` preserves all `sig`-operations
public export 0
Homomorphism : {sig : Signature} -> (a, b : Algebra sig) -> (h : U a -> U b) -> Type
Homomorphism a b h = (f : Op sig) -> Preserves a b h f

||| Homomorphisms between `Sig`-algebras
||| @H : function between the carriers
||| @preserves : satisfying the homomorphism property
public export
record (~>) {Sig : Signature} (a, b : Algebra Sig) where
  constructor MkHomomorphism
  H : U a -> U b
  preserves : Homomorphism a b H

||| Algebraic terms of this signature with variables in the given type
public export
data Term : (0 sig : Signature) -> Type -> Type where
  ||| A variable with the given index
  Done : {0 sig : Signature} -> a -> Term sig a
  ||| An operator, applied to a vector of sub-terms
  Call : {0 sig : Signature} -> (f : Op sig) -> Vect (sig.arity f) (Term sig a)
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


||| Specifies `bindTerms` specialises `map bindTerm`.
export
bindTermsIsMap : {auto a : Algebra sig} 
  -> (xs : Vect n (Term sig x)) -> (env : x -> U a)
  -> bindTerms {a} xs env = map (flip (bindTerm {a}) env) xs
bindTermsIsMap [] env = Refl
bindTermsIsMap (y :: xs) env = cong (bindTerm y env ::) $ bindTermsIsMap xs env

||| The free `sig`-algebra over over a given type
public export
Free : (0 sig : Signature) -> (0 x : Type) -> Algebra sig
Free sig x = MkAlgebra (Term sig x) Call

public export
Functor (Term sig) where
  map h t = bindTerm {a = Free _ _} t (Done . h)

public export
Applicative (Term sig) where
  pure = Done
  (<*>) fs ts = bindTerm {a = Free sig _} fs \f => 
                bindTerm {a = Free sig b} ts \x => 
                Done (f x)

public export
Monad (Term sig) where
  (>>=) {b} = bindTerm {a = Free sig b}

||| Extends the semantic interpration of the algebra from operators to terms homomorphically
||| @ env : environment/valuation, with the i-th element holding the
|||         algebra value to substitute for the i-th variable
public export
Sem : {0 sig : Signature} -> (a : Algebra sig)
  -> Term sig (Fin n) -> (env : Vect n (U a))
  -> U a
Sem a t env = bindTerm t (\i => index i env)

||| Free `sig`-algebra over `n`-variables.
public export
TermAlgebra : (0 sig : Signature) -> (n : Nat) -> Algebra sig
TermAlgebra sig n = Free sig (Fin n)

||| States: `(>>= f) : Free sig x -> a` is an algebra homomorphism
export
bindHom : {0 sig : Signature} -> {0 x : Type} -> {a : Algebra sig} -> (env : x -> U a)
  -> Homomorphism (Free sig x) a (flip (bindTerm {a}) env)
bindHom env f ts = cong (a.Sem f) (bindTermsIsMap _ _)

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

namespace Universality
  ||| Like Algebra.(>>=), but pack the `sig`-homomorphism structure
  public export
  eval : {0 sig : Signature} -> {0 x : Type} -> {auto a : Algebra sig} -> (env : x -> U a)
          -> Free sig x ~> a 
  eval env = MkHomomorphism (flip bindTerm env) (bindHom env)

export  
bindAssociative : {0 sig : Signature} -> {0 x, y : Type} -> {auto a : Algebra sig}
  -> (t : Term sig x) -> (f : x -> Term sig y) -> (g : y -> U a) 
  -> bindTerm (bindTerm {a = Free _ _} t f) g 
     = bindTerm {a} t (\x => bindTerm {a} (f x) g)

export  
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
  Cast (SetoidAlgebra sig) Setoid where
    cast a = MkSetoid (U $ a.algebra) (equivalence a)
  
  public export
  Cast (Algebra sig) (SetoidAlgebra sig) where
    cast a = MkSetoidAlgebra 
      { algebra = a
      , equivalence = EqualEquivalence (U a)
      , congruence = \f, xs, ys, ext => cong (a.Sem f) $ vectorExtensionality _ _ ext
      }

  ||| Setoid homomorphisms between `SetoidAlgebra`s
  public export
  record (~>) {Sig : Signature} (A, B : SetoidAlgebra Sig) where
    constructor MkSetoidAlgebraHomomorphism
    ||| Ordinary algebra homomorphism
    H : algebra A ~> algebra B
    ||| Respecting the equivalence relation
    congruence : SetoidHomomorphism (cast A) (cast B) (.H H)

  {a : SetoidAlgebra sig} -> {b : SetoidAlgebra sig} -> 
    Cast (a ~> b) ((the Setoid) (cast a) ~> cast b) where
      cast h = MkSetoidHomomorphism h.H.H h.congruence
      
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
