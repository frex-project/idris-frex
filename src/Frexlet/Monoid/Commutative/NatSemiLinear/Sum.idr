||| Properties to do with sums
module Frexlet.Monoid.Commutative.NatSemiLinear.Sum

import Frex

import Frexlet.Monoid.Commutative.Theory
import Frexlet.Monoid.Commutative.Notation.Core
import Data.Vect.Properties

import Frex.Free
import Frex.Free.Construction

%default total

public export
sumHomomorphism : (a : CommutativeMonoid) ->
  SetoidHomomorphism (VectSetoid n (cast a)) (cast a) a.sum
sumHomomorphism a [] [] prf = (cast a).equivalence.reflexive _
sumHomomorphism a (x :: xs) (y :: ys) prf = a.cong 2 (Dyn 0 :+: Dyn 1) [_,_] [_,_]
  [ prf 0
  , sumHomomorphism a xs ys (\i => prf (FS i))
  ]

public export
(.sum) : (a : CommutativeMonoid) -> VectSetoid n (cast a) ~> cast a
a.sum = MkSetoidHomomorphism
  { H = a.sum
  , homomorphic = sumHomomorphism a
  }

public export
sumTabulateExtensional : {n : Nat} -> (a : CommutativeMonoid) -> (f, g : Fin n -> U a) ->
  (cast {to=Setoid} (Fin n) ~~> cast a).equivalence.relation (mate f) (mate g)  ->
  a.rel (a.sum $ tabulate f)
        (a.sum $ tabulate g)
sumTabulateExtensional {n = 0  } a f g prf = a.equivalence.reflexive _
sumTabulateExtensional {n = S n} a f g prf = a.cong 2 (Dyn 0 .+. Dyn 1) [_,_] [_,_]
  [ prf 0
  , sumTabulateExtensional a (f . FS) (g . FS) (\i => prf (FS i))
  ]

public export
sumZeroZero : (a : CommutativeMonoid) -> (n : Nat) ->
  let %hint notation : Action1 Nat (U a)
      notation = NatAction1 a in
  (cast a).equivalence.relation
    (a.sum (replicate n O1))
    O1
sumZeroZero a 0 = reflect (cast a) Refl
sumZeroZero a (S n) =
  let %hint
      notation : Action1 Nat (U a)
      notation = NatAction1 a
  in CalcWith (cast a) $
  |~ a.sum (replicate (S n) O1)
  ~~ O1 .+. a.sum (replicate n O1) ...(Refl)
  :~ O1 .+. O1                     ...(a.cong 1 (O2 :+: Dyn 0) [_] [_]
                                         [sumZeroZero a n])
  :~ O1                            ...(a.Validate (Mon LftNeutrality) (const _))

public export
sumDegenerate : {n : Nat} -> (a : CommutativeMonoid) ->
  let %hint
      notation : Action1 Nat (U a)
      notation = NatAction1 a
  in
  (xs : Vect n (U a)) -> (i : Fin n) ->
  ((j : Fin n) -> (i = j) `Either` ((cast a).equivalence.relation (index j xs) O1)) ->
  (cast a).equivalence.relation
    (a.sum xs)
    (index i xs)
sumDegenerate a [] _ f impossible
sumDegenerate {n = S n} a (x :: xs) FZ prf =
  let %hint
      notation : Action1 Nat (U a)
      notation = NatAction1 a
      prf' : (j : Fin _) -> (cast a).equivalence.relation (index j xs) O1
      prf'  j with (prf $ FS j)
       prf' _ | Left _ impossible
       prf' j | Right prf = prf
      xsZero : (cast a).equivalence.relation
                 (a.sum xs)
                 (a.sum $ replicate n O1)
      xsZero = (a.sum).homomorphic _ _ $ \i => CalcWith (cast a) $
        |~ index i xs
        :~ O1                       ...(prf' i)
        ~~ index i (replicate n O1) ...(sym $ indexReplicate _ _)
  in CalcWith (cast a) $
  |~ a.sum (x :: xs)
  ~~ x .+. a.sum xs               ...(Refl)
  :~ x .+. a.sum (replicate n O1) ...(a.cong 1 (Sta x :+: Dyn 0) [_] [_]
                                        [xsZero])
  :~ x .+. O1                     ...(a.cong 1 (Sta x :+: Dyn 0) [_] [_]
                                        [sumZeroZero a n])
  :~ x                            ...(a.Validate (Mon RgtNeutrality) $ const x)
sumDegenerate  a (x :: xs) (FS i) prf with (prf 0)
 sumDegenerate a (x :: xs) (FS i) prf | Left  Refl impossible
 sumDegenerate a (x :: xs) (FS i) prf | Right xZero =
   let %hint
       notation : Action1 Nat (U a)
       notation = NatAction1 a
       prf' : (j : Fin _) -> (i === j) `Either` (a.rel (index j xs) O1)
       prf'  j with (prf $ FS j)
        prf' _ | Left Refl = Left Refl
        prf' j | Right res = Right res

   in CalcWith (cast a) $
   |~ a.sum (x :: xs)
   ~~ x  .+. (a.sum xs) ...(Refl)
   :~ O1 .+. index i xs ...(a.cong 2 (Dyn 0 .+. Dyn 1) [_,_] [_,_]
                             [xZero, sumDegenerate a xs i prf'])
   :~        index i xs ...(a.Validate (Mon LftNeutrality) (const _))

-- Silly idea: Make all the notation extraction machinery a hint, but
-- require it to auto-search for a token it doesn't use. Then all we
-- need is a let-bound token marking which interface to take :D.

public export
interchange : (a : CommutativeMonoid) -> (x,y,z,w : U a) ->
  let %hint
      notation : Action1 Nat (U a)
      notation = NatAction1 a
  in a.rel ((x .+. y) .+. (z .+. w))
           ((x .+. z) .+. (y .+. w))
interchange a x y z w =
  let %hint
      notation : Action1 Nat (U a)
      notation = NatAction1 a
      lemma : (x,y,z,w : U a) ->
        a.rel ((x .+. y) .+. (z .+. w))
              (x .+.((y  .+.  z).+. w))
      lemma x y z w = CalcWith (cast a) $
        |~ (x .+. y) .+. (z .+. w)
        ~:  x .+.(y  .+. (z .+. w)) ...(a.Validate (Mon Associativity) (flip index [x, y, z .+. w]))
        :~  x .+.((y .+. z) .+. w)  ...(a.cong 1 (Sta x :+: Dyn 0) [_] [_]
                                       [a.Validate (Mon Associativity) (flip index [y, z, w])])
  in CalcWith (cast a) $
  |~ (x .+. y) .+. (z .+. w)
  :~  x .+.((y .+. z) .+. w) ...(lemma x y z w)
  :~  x .+.((z .+. y) .+. w) ...(a.cong 1 (Sta x .+. (Dyn 0 .+. Sta w)) [_] [_]
                                [a.Validate Commutativity (flip index [_, _])])
  ~: (x .+. z) .+. (y .+. w) ...(lemma x z y w)

public export
sumCommutative : {n : Nat} -> (a : CommutativeMonoid) -> (f,g : Fin n -> U a) ->
  let %hint
      notation : Action1 Nat (U a)
      notation = NatAction1 a
  in a.rel (a.sum $ tabulate $ \i => f i .+. g i)
           (a.sum (tabulate f) .+. a.sum (tabulate g))
sumCommutative {n = 0} a f g =
  let %hint
      notation : Action1 Nat (U a)
      notation = NatAction1 a
  in CalcWith (cast a) $
  |~ O1
  ~: O1 .+. O1 ...(a.Validate (Mon LftNeutrality) (const O1))
sumCommutative {n = S n} a f g =
  let %hint
      notation : Action1 Nat (U a)
      notation = NatAction1 a
  in CalcWith (cast a) $
  |~ a.sum (tabulate $ \i => f i .+. g i)
  ~~ (f 0 .+. g 0) .+. a.sum (tabulate $ \i => (f . FS) i .+. (g . FS) i)
              ...(Refl)
  :~ (f 0 .+. g 0) .+. (a.sum (tabulate $ f . FS) .+. a.sum (tabulate $ g . FS))
              ...(a.cong 1 (Sta (f 0 .+. g 0) :+: Dyn 0) [_] [_]
                                               [sumCommutative a _ _])
  :~ (f 0 .+. (a.sum $ tabulate $ f . FS)) .+. (g 0 .+. (a.sum $ tabulate $ g . FS))
              ...(interchange a _ _ _ _)
  ~~ a.sum (tabulate f) .+. a.sum (tabulate g)
              ...(Refl)


||| NB: a,b are explicit since we can't recover them from the
||| homomorphism between them as algebras alone.
public export
sumPreservation  : (a, b : CommutativeMonoid) ->
  let %hint
      notationA : Action1 Nat (U a)
      notationA = NatAction1 a
      %hint
      notationB : Action1 Nat (U b)
      notationB = NatAction1 b
  in (h : a ~> b) -> {0 n : Nat} -> (xs : Vect n (U a)) ->
  b.rel (h.H.H (a.sum xs))
        (b.sum (map h.H.H xs))
sumPreservation a b h    []     = h.preserves Zero []
sumPreservation a b h (x :: xs) =
  let %hint
      notationA : Action1 Nat (U a)
      notationA = NatAction1 a
      %hint
      notationB : Action1 Nat (U b)
      notationB = NatAction1 b
  in CalcWith (cast b) $
  |~ h.H.H (a.sum (x :: xs))
  ~~ h.H.H (x .+. a.sum xs)           ...(Refl)
  :~ h.H.H x .+. h.H.H (a.sum xs)     ...(h.preserves Plus [_,_])
  :~ h.H.H x .+. b.sum (map h.H.H xs) ...(b.cong 1 (Sta _ .+. Dyn 0) [_] [_]
                                          [sumPreservation _ _ _ _])
  ~~ b.sum (map h.H.H (x :: xs))      ...(Refl)
