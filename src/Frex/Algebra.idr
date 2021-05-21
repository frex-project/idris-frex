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
import Data.Vect.Extra
import Data.Rel

import Control.WellFounded

import Syntax.PreorderReasoning
import Decidable.Order
import Syntax.PreorderReasoning.Generic

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

public export total
sizeOfTerms : Vect n (Term sig x) -> Vect n Nat  

public export total
sizeOfTerm  :        (Term sig x) -> Nat  
sizeOfTerm (Done _) = 0 
sizeOfTerm (Call f xs) = 1 + sum (sizeOfTerms xs)

sizeOfTerms [] = []
sizeOfTerms (t :: ts) = sizeOfTerm t :: sizeOfTerms ts

sizeOfTermsIsMap : (xs : Vect n (Term sig x)) -> sizeOfTerms xs = map Algebra.sizeOfTerm xs  
sizeOfTermsIsMap [] = Refl
sizeOfTermsIsMap (y :: xs) = cong (sizeOfTerm y ::) $ sizeOfTermsIsMap xs

sumIsGTEtoParts : {x : Nat} -> (xs : Vect n Nat) -> (x `Elem` xs) -> sum xs `GTE` x
sumIsGTEtoParts (x :: xs) Here 
  = rewrite (foldrVectHomomorphism {f = plus} {e = 0}).cons x xs in
  CalcWith $
  |~ x
  ~~ x + 0 ...(sym $ plusZeroRightNeutral _)
  <~ _     ...(plusLteMonotoneLeft x 0 _ LTEZero)
sumIsGTEtoParts {x} (y :: xs) (There later) 
  = rewrite (foldrVectHomomorphism {f = plus} {e = 0}).cons y xs in 
    CalcWith $ 
    |~ x
    <~ sum xs       ...(sumIsGTEtoParts {x} xs later)
    ~~ 0 + sum xs   ...(Refl)
    <~ y + (sum xs) ...(plusLteMonotoneRight (sum xs) 0 y LTEZero)

public export total
Sized (Term sig x) where
  size t = sizeOfTerm t

sumMonotone : {n : Nat} -> (xs, ys : Vect n Nat) 
  -> (prf : (i : Fin n) -> index i xs `LTE` index i ys)
  -> (sum xs `LTE` sum ys)
sumMonotone [] [] prf = LTEZero
sumMonotone (x :: xs) (y :: ys) prf = 
  let prf' = sumMonotone xs ys (\i => prf (FS i)) 
  in CalcWith $
  |~ sum (x :: xs)
  ~~ x + sum xs    ...((foldrVectHomomorphism {f = plus} {e = 0}).cons x xs)
  <~ y + sum ys    ...(plusLteMonotone  (prf 0) prf')
  ~~ sum (y :: ys) ...(sym $ (foldrVectHomomorphism {f = plus} {e = 0}).cons y ys)

export
enoughFuel : {fuel : Nat} -> {t : Term sig x} -> (xs : Vect (sig.arity f) (Term sig x)) -> (pos : t `Elem` xs)
  -> (fuel `GTE` sum (sizeOfTerms xs))
  -> (fuel `GTE` size t)
enoughFuel {fuel} xs pos enough = CalcWith $
    |~ sizeOfTerm t
    <~ sum (map sizeOfTerm xs) ...(sumIsGTEtoParts _ $ mapElem pos)
    ~~ sum (sizeOfTerms xs)    ...(cong sum $ sym $ sizeOfTermsIsMap xs)
    <~ fuel                    ...(enough) 

public export
mapTerm : (f : x -> y) -> (t : Term sig x) 
  -> (0 fuel : Nat) -> (0 enough: fuel `GTE` size t)
  -> Term sig y
mapTerm h (Done w) _ _ = Done (h w)
mapTerm h (Call f xs) (S fuel) (LTESucc enough) 
  = Call f $ mapWithElem xs \t,pos => mapTerm h t fuel (enoughFuel xs pos enough)

public export
Functor (Term sig) where
  map h t = mapTerm h t (size t) (LTEIsReflexive _)

bindFueled : {0 sig : Signature} -> {0x : Type} -> {a : Algebra sig}
  -> (t : Term sig x) -> (env : x -> U a) 
  -> (0 fuel : Nat) -> (0 enough : fuel `GTE` size t)
  -> (U a) 
bindFueled (Done   v ) env _ _ = env v
bindFueled (Call f xs) env (S fuel) (LTESucc enough) = 
  a.Sem f $ mapWithElem xs \t,pos => bindFueled t env fuel (enoughFuel xs pos enough)

depCong : {0 p : a -> Type} -> (f : (x : a) -> p x) -> (0 prf : x = y) -> f x = f y
depCong f Refl = Refl

export total
bindFueledIndependent : {0 sig : Signature} -> {0 x : Type} -> {a : Algebra sig}
  -> (t : Term sig x) -> (env : x -> U a) 
  -> (0 fuel1 : Nat) -> (0 enough1 : fuel1 `GTE` size t)
  -> (0 fuel2 : Nat) -> (0 enough2 : fuel2 `GTE` size t)
  -> bindFueled {a} t env fuel1 enough1 = bindFueled {a} t env fuel2 enough2
bindFueledIndependent (Done y) env fuel1 enough1 fuel2 enough2 = Refl
bindFueledIndependent (Call f xs) env (S fuel1) (LTESucc enough1) (S fuel2) (LTESucc enough2) = Calc $
  |~ a.Sem f (mapWithElem xs (\t, pos => bindFueled t env fuel1 (enoughFuel xs pos enough1)))
  ~~ a.Sem f (mapWithElem xs (\t, pos => bindFueled t env fuel2 (enoughFuel xs pos enough2)))
    ...(cong (a.Sem f) $ mapWithElemExtensional xs _ _ \t,pos =>
                         bindFueledIndependent t env _ _ _ _)

-- Idris thinks this is covering for some reason...
--bindFueledIndependent (Call _ _) _ _ LTEZero (S _) (LTESucc _) = ?h



infixl 1 >>==

||| The Kleisli extension operator associated with each algebra
public export
(>>==) : {0 sig : Signature} -> {0 x : Type} -> {a : Algebra sig}
  -> (t : Term sig x) -> (env : x -> U a) -> (U a)
(>>==) t env = bindFueled t env (size t) (LTEIsReflexive _)

||| The free `sig`-algebra over over a given type
public export
Free : (0 sig : Signature) -> (0 x : Type) -> Algebra sig
Free sig x = MkAlgebra (Term sig x) Call

public export
Applicative (Term sig) where
  pure x = Done x
  (<*>) fs ts = (>>==) {a = Free sig _} fs \f => 
                (>>==) {a = Free sig b} ts \x => 
                Done (f x)

public export
Monad (Term sig) where
  (>>=) {b} = (>>==) {a = Free sig b}

||| Extends the semantic interpration of the algebra from operators to terms homomorphically
||| @ env : environment/valuation, with the i-th element holding the
|||         algebra value to substitute for the i-th variable
public export
Sem : {0 sig : Signature} -> (a : Algebra sig)
  -> Term sig (Fin n) -> (env : Vect n (U a))
  -> U a
Sem a t env = t >>== (\i => index i env)

||| Free `sig`-algebra over `n`-variables.
public export
TermAlgebra : (0 sig : Signature) -> (n : Nat) -> Algebra sig
TermAlgebra sig n = Free sig (Fin n)

||| States: `(>>= f) : Free sig x -> a` is an algebra homomorphism
export
bindHom : {sig : Signature} -> {0 x : Type} -> {a : Algebra sig} -> (env : x -> U a)
  -> Homomorphism (Free sig x) a (flip ((>>==) {a}) env)
bindHom env f ts = ?efl

||| Monad law corresponding to right unit law of monoids
export total
bindPureRightUnit : {0 sig : Signature} -> {0 x : Type} 
    -> (t : Term sig x) 
    -> (t >>= Prelude.pure) = t
bindPureRightUnit (Done v) = Refl
bindPureRightUnit (Call f xs) = ?h1 {-cong (Call f) $ Calc $
  |~ map (>>= pure) xs
  ~~ map id xs  ...(assert_total (mapExtensional _ _ bindPureRightUnit _))
  ~~ xs         ...(mapId _) -}

{-
export 
bindAssociative : {0 sig : Signature} -> {0 x, y : Type} -> {a : Algebra sig}
  -> (t : Term sig x) -> (f : x -> Term sig y) -> (g : y -> U a) 
  -> ((t >>= f) >>= g) = with Algebra (t >>= (\x => f x >>= g))
-}
namespace Universality
  ||| Like Algebra.(>>=), but pack the `sig`-homomorphism structure
  public export
  (>>=) : {sig : Signature} -> {0 x : Type} -> {a : Algebra sig} -> (env : x -> U a)
          -> Free sig x ~> a 
  (>>=) env = MkHomomorphism (\t => t >>== env) (bindHom env)
  
  


namespace Setoid
  public export 0
  CongruenceWRT : {n : Nat} -> (a : Setoid) -> (f : (U a) ^ n -> U a) -> Type
  CongruenceWRT a f = SetoidHomomorphism (VectSetoid n a) a f
  
  export
  EqualCongruence : {n : Nat} -> (f : a ^ n -> a) -> CongruenceWRT (cast a) f
  EqualCongruence f x y prf = ?EqualCongruence_rhs -- Vector extensionality
  
  public export
  record SetoidAlgebra (Sig : Signature) where
    constructor MkSetoidAlgebra
    algebra : Algebra Sig
    equivalence : Equivalence (U algebra)
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

  public export
  record (~>) {Sig : Signature} (A, B : SetoidAlgebra Sig) where
    constructor MkSetoidAlgebraHomomorphism
    H : algebra A ~> algebra B
    congruence : SetoidHomomorphism (cast A) (cast B) (.H H)

  {a : SetoidAlgebra sig} -> {b : SetoidAlgebra sig} -> 
    Cast (a ~> b) ((the Setoid) (cast a) ~> cast b) where
      cast h = MkSetoidHomomorphism h.H.H h.congruence

