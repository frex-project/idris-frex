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

{- ------------------ Functor, Applicative, Monad ------------------------------------------- 

  To define the Functor, Applicative, and Monad implementations, we
  need to inductively call `map` etc., and that confuses the
  termination checker.
  
  We use a crude solution: define the size terms, and use this size as
  fuel.
-}

||| A specialisation of `map sizeOfTerm` that helps the termination
||| checker see something is decreasing.
public export total
sizeOfTerms : Vect n (Term sig x) -> Vect n Nat  

||| The size of a term gives an upper bound on its depth.
||| 
||| It would be more natural to use `max` rather than `sum`, but
||| `contrib`'s support for order is not great at the moment.
public export total
sizeOfTerm  :        (Term sig x) -> Nat  
sizeOfTerm (Done _) = 0 
sizeOfTerm (Call f xs) = 1 + sum (sizeOfTerms xs)

sizeOfTerms [] = []
sizeOfTerms (t :: ts) = sizeOfTerm t :: sizeOfTerms ts

||| Specifies `sizeOfTerms` specialises `map sizeOfTerm`.
export
sizeOfTermsIsMap : (xs : Vect n (Term sig x)) -> sizeOfTerms xs = map Algebra.sizeOfTerm xs  
sizeOfTermsIsMap [] = Refl
sizeOfTermsIsMap (y :: xs) = cong (sizeOfTerm y ::) $ sizeOfTermsIsMap xs


public export total
Sized (Term sig x) where
  size t = sizeOfTerm t

export
enoughFuel : {fuel : Nat} -> {t : Term sig x} -> (xs : Vect n (Term sig x)) -> (pos : t `Elem` xs)
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
  = Call f $ Data.Vect.Extra.mapWithElem xs \t,pos => mapTerm h t fuel (enoughFuel xs pos enough)

public export
Functor (Term sig) where
  map h t = mapTerm h t (size t) (LTEIsReflexive _)

||| Kleisli extension operator for a `sig`-algebra, with fuel for termination
public export
bindFuelled : {0 sig : Signature} -> {0x : Type} -> {a : Algebra sig}
  -> (t : Term sig x) -> (env : x -> U a) 
  -> (0 fuel : Nat) -> (0 enough : fuel `GTE` size t)
  -> (U a) 
bindFuelled (Done   v ) env _ _ = env v
bindFuelled (Call f xs) env (S fuel) (LTESucc enough) = 
  a.Sem f $ mapWithElem xs \t,pos => bindFuelled t env fuel (enoughFuel xs pos enough)

||| the argument to `bindFuelled`'s `mapWithElem`, needed for proofs
bindarg : {0 sig : Signature} -> {0 x : Type} -> {a : Algebra sig} -> {xs : Vect n (Term sig x)}
  -> (fuel : Nat) -> (enough : fuel `GTE` sum (sizeOfTerms xs))
  -> (f : x -> U a) 
  -> (t : Term sig x) -> (0 pos : t `Elem` xs) -> U a
bindarg {a} {xs} fuel enough f t pos = bindFuelled {a} t f fuel (enoughFuel xs pos enough)

export total
bindFuelledIndependentExtensional : {0 sig : Signature} -> {0 x : Type} -> {a : Algebra sig}
  -> (t1 : Term sig x) -> (env1 : x -> U a) 
  -> (t2 : Term sig x) -> (env2 : x -> U a)  
  -> (t1 = t2) -> ((i : x) -> env1 i = env2 i)
  -> (0 fuel1 : Nat) -> (0 enough1 : fuel1 `GTE` size t1)
  -> (0 fuel2 : Nat) -> (0 enough2 : fuel2 `GTE` size t2)
  -> bindFuelled {a} t1 env1 fuel1 enough1 = bindFuelled {a} t2 env2 fuel2 enough2
bindFuelledIndependentExtensional (Done i) env _ _ Refl prf fuel1 enough1 fuel2 enough2 = prf i
bindFuelledIndependentExtensional (Call f xs) env1 _ env2 Refl prf (S fuel1) (LTESucc enough1) (S fuel2) (LTESucc enough2) 
  = Calc $
  |~ a.Sem f (mapWithElem xs (\t, pos => bindFuelled t env1 fuel1 (enoughFuel xs pos enough1)))
  ~~ a.Sem f (mapWithElem xs (\t, pos => bindFuelled t env2 fuel2 (enoughFuel xs pos enough2)))
    ...(cong (a.Sem f) $ mapWithElemExtensional xs _ _ \t,pos =>
                         bindFuelledIndependentExtensional t env1 t env2 Refl prf _ _ _ _)

-- Idris thinks this is covering for some reason...
--bindFuelledIndependent (Call _ _) _ _ LTEZero (S _) (LTESucc _) = ?h



infixl 1 >>==

||| The Kleisli extension operator associated with each algebra
public export
(>>==) : {0 sig : Signature} -> {0 x : Type} -> {a : Algebra sig}
  -> (t : Term sig x) -> (env : x -> U a) -> (U a)
(>>==) t env = bindFuelled t env (size t) (LTEIsReflexive _)

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

||| Monad law corresponding to right unit law of monoids, fueled version
total
bindFuelledPureRightUnit : {0 sig : Signature} -> {0 x : Type} 
    -> (t : Term sig x) 
    -> (fuel : Nat) -> (enough : fuel `GTE` size t)
    -> (bindFuelled {a = Free _ _} t Prelude.pure fuel enough) = t
bindFuelledPureRightUnit (Done v) _ _ = Refl
bindFuelledPureRightUnit (Call f xs) (S fuel) (LTESucc enough) 
  = cong (Call f) $ vectorExtensionality _ _ \i => 
  let maparg : (t : Term sig x) -> (0 pos : t `Elem` xs) -> Term sig x
      maparg t pos = bindFuelled {a = Free _ _} t pure fuel (enoughFuel xs pos enough)
  in Calc $ 
  |~ index i (mapWithElem xs (bindarg {a = Free _ _} fuel enough pure))
  ~~ maparg (index i xs) (finToElem xs i)
    ...(let u = indexNaturalityWithElem i xs (bindarg {a = Free _ _} fuel enough pure) in u)
  ~~ index i xs ...(bindFuelledPureRightUnit _ _ _)

||| Monad law corresponding to right unit law of monoids
export total
bindPureRightUnit : {0 sig : Signature} -> {0 x : Type} 
    -> (t : Term sig x) 
    -> t >>= Prelude.pure = t
bindPureRightUnit t = bindFuelledPureRightUnit t (size t) (LTEIsReflexive _)


namespace Universality
  ||| Like Algebra.(>>=), but pack the `sig`-homomorphism structure
  public export
  (>>=) : {sig : Signature} -> {0 x : Type} -> {a : Algebra sig} -> (env : x -> U a)
          -> Free sig x ~> a 
  (>>=) env = MkHomomorphism (\t => t >>== env) (bindHom env)
  
depCong : {p : a -> Type} -> (f : (x : a) -> p x) -> x = y -> f x = f y
depCong _ Refl = Refl
  
bindFuelledAssociative : {0 sig : Signature} -> {0 x, y : Type} -> {a : Algebra sig}
  -> (t : Term sig x) -> (f : x -> Term sig y) -> (g : y -> U a) 
  -> (fuel : Nat) -> (enough : fuel `GTE` size t) -- luckily, one set of fuel is enough
  -> (>>==) {a} (bindFuelled {a = Free _ _} t f fuel enough) g 
     = bindFuelled {a} t (\x => (>>==) {a} (f x) g) fuel enough
bindFuelledAssociative (Done v    ) f g fuel enough = Refl 
bindFuelledAssociative (Call op xs) f g (S fuel) (LTESucc enough) 
  {sig,x,y}
  = let ys : Vect (sig.arity op) (Term sig y)
        ys = mapWithElem xs \t, pos => 
                             bindarg {a = Free _ _} fuel enough f t pos
  in cong (a.Sem op) $ vectorExtensionality _  _ \i => Calc $ 
  |~ index i (mapWithElem ys
                          \t, pos => bindarg {a} _ (LTEIsReflexive _) g t pos)
  ~~ bindarg {a} _ (LTEIsReflexive _) g 
        (index i $ 
          mapWithElem xs \t, pos => 
                         bindarg {a = Free _ _} fuel enough f t pos)
          (finToElem ys i) ...(indexNaturalityWithElem _ _ _)
  ~~ bindarg {a} (sum (sizeOfTerms ys)) (LTEIsReflexive _) g
       (bindarg {a = Free _ _} fuel enough f (index i xs) (finToElem xs i))
       ?h -- Ah, not a cong, but a depCong, since the final argument depends on the previous one
  
       {-bindarg {a} ?h (LTEIsReflexive _) g  
       (bindarg {a = Free _ _} fuel enough f (index i xs) (finToElem xs i))
       ?h2-} ...(--cong (\u => bindarg {a} (sum (sizeOfTerms ys)) (LTEIsReflexive _) g u ?)
                ?h1) --bindFuelledIndependentExtensional ? ? ? ? ?h1 ?h2 ? ? ? ?)
  ~~ index i (mapWithElem xs \t, pos => bindarg fuel enough (\x => (>>==) {a} (f x) g) t pos)
  ...(?help) --Need to first show (>>==) is a homomorphism mapWithElemExtensional xs _ _ \t,pos => ?help


export 
bindAssociative : {0 sig : Signature} -> {0 x, y : Type} -> {a : Algebra sig}
  -> (t : Term sig x) -> (f : x -> Term sig y) -> (g : y -> U a) 
  -> (>>==) {a} (t >>= f) g = (>>==) {a} t (\x => (>>==) {a} (f x) g)
bindAssociative t f g = bindFuelledAssociative t f g (size t) (LTEIsReflexive _)



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


