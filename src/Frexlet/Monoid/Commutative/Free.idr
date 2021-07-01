||| An inductive construction of the free commutative monoid over a
||| finite set.
module Frexlet.Monoid.Commutative.Free

import Frex

import Notation
import Notation.Action

import Frexlet.Monoid.Commutative.Theory
import Frexlet.Monoid.Commutative.Notation.Core
import Data.Vect.Properties

import Syntax.PreorderReasoning.Generic
import Syntax.PreorderReasoning

import Frexlet.Monoid.Commutative.NatSemiLinear

import public Frexlet.Monoid.Commutative.Nat

import Decidable.Equality
import Data.Bool.Decidable
import Data.Nat
import public Data.Vect.Extra
import Data.Vect.Extra1

%default total

public export
Model : (n : Nat) -> CommutativeMonoid
Model n = (Commutative.Nat.Additive ^ n).Data.Model

||| Monadic unit
public export
unit : (n : Nat) -> Fin n -> U (Model n)
unit n i = Fin.tabulate \j => dirac i j

public export
FreeCommutativeMonoidOver : (n : Nat) -> CommutativeMonoidTheory `ModelOver` (cast $ Fin n)
FreeCommutativeMonoidOver n =
  MkModelOver
  { Model = Model n
  , Env   = mate (\i => unit n i)
  }

export
FreeModelZeroRepresentation : (n : Nat) -> (Model n).sem Neutral = replicate n 0
FreeModelZeroRepresentation  n = vectorExtensionality _ _ \i => Calc $
  |~ index i (map (uncurry 0) (replicate n Vect.Nil))
  ~~ uncurry 0 (index i $ replicate n Vect.Nil) ...(indexNaturality _ _ _)
  ~~ 0                                          ...(Refl)
  ~~ index i (replicate n 0)                    ...(sym $ indexReplicate _ _)

export
pointwiseSum : (n : Nat) -> (xss : Vect m (U $ Model n)) -> (i : Fin n) ->
  index i ((Model n).sum xss) = (Nat.Additive).sum (map (index i) xss)
pointwiseSum n xss i = sumPreservation (Model n) (Nat.Additive) (Fin.eval i) xss

export
pointwiseMult : (n : Nat) -> (m : Nat) -> (xs : (U $ Model n)) -> (i : Fin n) ->
  let %hint
      notation : Action1 Nat (U $ Model n)
      notation = NatAction1 (Model n)
  in
  index i (m *. xs) = m * (index i xs)
pointwiseMult n m xs i =
  let %hint
      notation : Action1 Nat (U $ Model n)
      notation = NatAction1 (Model n)
      %hint
      notation' : Action1 Nat (U $ Commutative.Nat.Additive)
      notation' = NatAction1 (Nat.Additive)
  in Calc $
  |~ index i (m *. xs)
  ~~ m *. (index i xs) ...(multPreservation (Model n) (Nat.Additive) (Fin.eval i) m xs)
  ~~ m * (index i xs) ...(multActionNat _ _)

export
diracPointMass : (i, j : Fin n) ->
           (i = j, index j (unit n i) = 1)
  `Either` (index j (unit n i) = 0)
diracPointMass  i j with (decEq i j)
 diracPointMass i i | Yes Refl = Left (Refl, Calc $
   |~ index i (unit n i)
   ~~ dirac i i ...(indexTabulate (dirac i) i)
   ~~ 1         ...(diracOnDiagonal _))
 diracPointMass i j | No i_neq_j = Right $ Calc $
   |~ index j (unit n i)
   ~~ dirac i j ...(indexTabulate (dirac i) j)
   ~~ 0         ...(diracOffDiagonal i j i_neq_j)

lemma1 : (n : Nat) -> (i,j : Fin n) -> (xs : Vect n Nat) ->
  let %hint
      notation : Action1 Nat (U $ Model n)
      notation = NatAction1 (Model n)
      %hint
      notation' : Action1 Nat (U $ Commutative.Nat.Additive)
      notation' = NatAction1 Additive
  in index i ((index j xs) *. (unit n j)) = (dirac i j) *. (index j xs)
lemma1 n i j xs =
  let %hint
      notation : Action1 Nat (U $ Model n)
      notation = NatAction1 (Model n)
      %hint
      notation' : Action1 Nat (U $ Commutative.Nat.Additive)
      notation' = NatAction1 Additive
  in Calc $
  |~ index i ((index j xs) *. (unit n j))
  ~~ (index j xs) *  (index i $ unit n j) ...(pointwiseMult n (index j xs) (unit n j) i)
  ~~ (index j xs) *. (index i $ unit n j) ...(sym $ multActionNat _ _)
  ~~ (index j xs) *. (dirac j i)          ...(cong ((index j xs) *.) $ indexTabulate (dirac j) i)
  ~~ (index j xs) *. (dirac i j)          ...(cong (index j xs *.) $ diracSym _ _)
  ~~ (dirac i j ) *. (index j xs)         ...(actionNatCommutative _ _)

lemma2 : (n : Nat) -> (i : Fin n) -> (xs : Vect n Nat) ->
  let %hint
      notation : Action1 Nat (U $ Model n)
      notation = NatAction1 (Model n)
      %hint
      notation' : Action1 Nat (U $ Commutative.Nat.Additive)
      notation' = NatAction1 Additive
  in map (index i) (tabulate \j => (index j xs) *. (unit n j))
  =  tabulate (\j => (dirac i j) *. (index j xs))
lemma2 n i xs =
  let %hint
      notation : Action1 Nat (U $ Model n)
      notation = NatAction1 (Model n)
      %hint
      notation' : Action1 Nat (U $ Commutative.Nat.Additive)
      notation' = NatAction1 Additive
  in Calc $
        |~ map (index i) (tabulate \j => (index j xs) *. (unit n j))
        ~~ tabulate (\j => (index i $ (index j xs) *. (unit n j))) ...(sym $ mapTabulate (index i)
                                                                      \j => (index j xs) *. (unit n j))
        ~~ tabulate (\j => (dirac i j) *. (index j xs)) ...(tabulateExtensional _ _
                                                           $ \j => lemma1 n i j xs)


export
normalForm : (n : Nat) -> (xs : U (Model n)) ->
  let %hint
      notation : Action1 Nat (U $ Model n)
      notation = NatAction1 (Model n)
  in (Model n).sum (tabulate \i => (index i xs) *. (unit n i)) = xs
normalForm n xs = vectorExtensionality _ _ $ \i =>
  let %hint
      notation : Action1 Nat (U $ Model n)
      notation = NatAction1 (Model n)
      %hint
      notation' : Action1 Nat (U $ Commutative.Nat.Additive)
      notation' = NatAction1 Additive
  in Calc $
  |~ index i ((Model n).sum (tabulate \i => (index i xs) *. (unit n i)))
  ~~ (Additive).sum (map (index i) (tabulate \i => (index i xs) *. (unit n i)))
                                                                 ...(pointwiseSum n _ _)
  ~~ (Additive).sum (tabulate \j => (dirac i j) *. (index j xs)) ...(cong (Additive).sum $
                                                                    lemma2 n i xs)
  ~~ index i xs                                                  ...(convolveDirac Additive _ _)

public export
FreeExtenderFunction : ExtenderFunction (FreeCommutativeMonoidOver n)
FreeExtenderFunction other =
  let %hint
      notation : Action1 Nat (U $ other.Model)
      notation = NatAction1 (other.Model)
  in
  other.Model.sum . (mapWithPos (\i,k => k *. other.Env.H i))

public export
FreeExtenderSetoidHomomorphism : ExtenderSetoidHomomorphism (FreeCommutativeMonoidOver n)
FreeExtenderSetoidHomomorphism other = MkSetoidHomomorphism
  { H = FreeExtenderFunction other
  , homomorphic = \xs,ys,prf => Data.Setoid.Definition.reflect (cast other.Model)
                              $ cong (FreeExtenderFunction other)
                              $ vectorExtensionality xs ys prf
  }

public export
extenderPreservesZero : {n : Nat} -> (other : CommutativeMonoidTheory `ModelOver` (cast $ Fin n)) ->
  Preserves (Model n).Algebra other.Model.Algebra (FreeExtenderFunction other) Zero
extenderPreservesZero other [] =
  let %hint
      notation : Action1 Nat (U other.Model)
      notation = NatAction1 other.Model
      %hint
      notation' : Action1 Nat (U (Model n))
      notation' = NatAction1 (Model n)
  in CalcWith @{cast other.Model} $
  |~ FreeExtenderFunction other O1
  ~~ other.Model.sum
    (mapWithPos (\i : Fin n,k : Nat => k *. other.Env.H i)
                (replicate n 0)) ...(cong (FreeExtenderFunction other) $
                                     FreeModelZeroRepresentation n)
  ~~ other.Model.sum
      (tabulate (\i => Z *. other.Env.H i)) ...(cong other.Model.sum $ mapWithPosTabulate _ Z)
  ~~ other.Model.sum
      (Fin.tabulate (\i => O1))             ...(Refl)
  ~~ other.Model.sum
      (replicate n O1)                      ...(cong other.Model.sum $ tabulateConstantly O1)
  <~ O1                                     ...(sumZeroZero other.Model n)

public export
extenderPreservesPlus : {n : Nat} -> (other : CommutativeMonoidTheory `ModelOver` (cast $ Fin n)) ->
  Preserves (Model n).Algebra other.Model.Algebra (FreeExtenderFunction other) Plus
extenderPreservesPlus other [xs,ys] =
  let %hint
      notation : Action1 Nat (U other.Model)
      notation = NatAction1 other.Model
      %hint
      notation' : Action1 Nat (U (Model n))
      notation' = NatAction1 (Model n)
      h : U (Model n) -> U other.Model
      h = FreeExtenderFunction other

      lemma2 : (j : Fin n) ->
        other.Model.rel (index j $ tabulate \i => (index i $ xs .+. ys) *. other.Env.H i)
                        (index j $ tabulate \i => (index i xs) *. other.Env.H i
                                              .+. (index i ys) *. other.Env.H i)
      lemma2 j = CalcWith @{cast other.Model} $
        |~ index j (tabulate \i => (index i $ xs .+. ys) *. other.Env.H i)
        ~~ index j (xs .+. ys) *. other.Env.H j           ...(indexTabulate _ _)
        ~~ ((index j xs) + (index j ys)) *. other.Env.H j
            ...(cong (\u : Nat => u *. (other.Env.H j)) $
                     (Fin.eval {a = (Commutative.Nat.Additive).Algebra}
                        j).preserves Plus [xs,ys])
        <~  (index j xs) *. other.Env.H j  .+.  (index j ys) *. other.Env.H j
            ...(multDistributesOverPlusLeft other.Model _ _ _)
        ~~ index j (tabulate \i => (index i xs) *. other.Env.H i
                                              .+. (index i ys) *. other.Env.H i)
            ...(sym $ indexTabulate _ _)
  in CalcWith @{cast other.Model} $
  |~ h (xs .+. ys)
  ~~ other.Model.sum (mapWithPos (\i, k => k *. other.Env.H i) (xs .+. ys)) ...(Refl)
  ~~ other.Model.sum (tabulate \i => (index i $ xs .+. ys) *. other.Env.H i)
      ...(cong other.Model.sum $ mapWithPosAsTabulate _ _)
  <~ other.Model.sum (tabulate \i =>  (index i xs) *. other.Env.H i
                                  .+. (index i ys) *. other.Env.H i)
                   ...(other.Model.sum.homomorphic _ _ (\i => lemma2 i))
  <~ other.Model.sum (tabulate \i => (index i xs) *. other.Env.H i) .+.
     other.Model.sum (tabulate \i => (index i ys) *. other.Env.H i)
                   ...(sumCommutative other.Model _ _)
  <~ h xs .+. h ys ...(other.Model.cong 2 (Dyn 0 .+. Dyn 1) [_,_] [_,_]
                       [ Data.Setoid.Definition.reflect (cast other.Model) $ sym $
                         cong other.Model.sum $ mapWithPosAsTabulate _ _
                       , Data.Setoid.Definition.reflect (cast other.Model) $ sym $
                         cong other.Model.sum $ mapWithPosAsTabulate _ _
                       ])

public export
FreeExtenderHomomorphism : {n : Nat} -> ExtenderAlgebraHomomorphism (FreeCommutativeMonoidOver n)
FreeExtenderHomomorphism other = MkSetoidHomomorphism
  { H = FreeExtenderSetoidHomomorphism other
  , preserves = \case
      MkOp Neutral => extenderPreservesZero other
      MkOp Product => extenderPreservesPlus other
  }

public export
extenderIsMorphism : {n : Nat} -> (other : CommutativeMonoidTheory `ModelOver` (cast $ Fin n)) ->
  PreservesEnv (FreeCommutativeMonoidOver n) other (FreeExtenderSetoidHomomorphism other)
extenderIsMorphism {n} other i =
  let %hint
      notation : Action1 Nat (U other.Model)
      notation = NatAction1 other.Model
      %hint
      notation' : Action1 Nat (U (Model n))
      notation' = NatAction1 (Model n)
      h : U (Model n) -> U other.Model
      h = FreeExtenderFunction other
  in CalcWith @{cast other.Model} $
  |~ h (unit n i)
  ~~ other.Model.sum (mapWithPos (\j,k => k *. other.Env.H j) (unit n i)) ...(Refl)
  ~~ other.Model.sum (tabulate \j => (index j (unit n i)) *. other.Env.H j)
    ...(cong other.Model.sum $ mapWithPosAsTabulate _ _)
  ~~ other.Model.sum (tabulate \j => (dirac i j) *. other.Env.H j)
    ...(cong other.Model.sum $ tabulateExtensional _ _ \j => cong (\u : Nat => u *. other.Env.H j)
       $indexTabulate (dirac i) j)
  <~ other.Env.H i ...(convolveDirac other.Model _ _)

public export
Extender : {n : Nat} -> Extender (FreeCommutativeMonoidOver n)
Extender other = MkHomomorphism
  { H = FreeExtenderHomomorphism other
  , preserves = extenderIsMorphism other
  }

public export
uniqueExtender : {n : Nat} -> (other : CommutativeMonoidTheory `ModelOver` (cast $ Fin n)) ->
   (extend : FreeCommutativeMonoidOver n ~> other) -> (xs : U (Model n)) ->
   other.Model.rel (extend.H.H.H xs)
                   (FreeExtenderFunction other xs)
uniqueExtender other extend xs =
  let %hint
      notation : Action1 Nat (U other.Model)
      notation = NatAction1 other.Model
      %hint
      notation' : Action1 Nat (U (Model n))
      notation' = NatAction1 (Model n)
  in CalcWith @{cast other.Model} $
  |~ extend.H.H.H xs
  ~~ extend.H.H.H ((Model n).sum (tabulate \i => (index i xs) *. unit n i))
        ...(cong extend.H.H.H $ sym $ normalForm n xs)
  <~ other.Model.sum (map extend.H.H.H $ (tabulate \i => (index i xs) *. unit n i))
        ...(sumPreservation (Model n) other.Model extend.H _)
  ~~ other.Model.sum (tabulate \i => extend.H.H.H ((index i xs) *. unit n i))
        ...(cong other.Model.sum $ sym $ mapTabulate _ _)
  <~ other.Model.sum (tabulate \i => (index i xs) *. extend.H.H.H (unit n i))
        ...(sumTabulateExtensional other.Model _ _ \i =>
            multPreservation (Model n) other.Model extend.H (index i xs) (unit n i))
  <~ other.Model.sum (tabulate \i => (index i xs) *. other.Env.H i)
        ...(sumTabulateExtensional other.Model _ _ \i =>
            multIsHomomorphism other.Model _ _ _ $
            extend.preserves i)
  ~~ FreeExtenderFunction other xs ...(cong other.Model.sum $ sym $
      mapWithPosAsTabulate _ _)

public export
Uniqueness : {n : Nat} -> Uniqueness (FreeCommutativeMonoidOver n)
Uniqueness other extend1 extend2 xs =
  let %hint
      notation : Action1 Nat (U other.Model)
      notation = NatAction1 other.Model
      %hint
      notation' : Action1 Nat (U (Model n))
      notation' = NatAction1 (Model n)
  in CalcWith @{cast other.Model} $
  |~ extend1.H.H.H xs
  <~ FreeExtenderFunction other xs ...(uniqueExtender other extend1 xs)
  <~ extend2.H.H.H xs              ...(other.Model.equivalence.symmetric _ _ $
                                       uniqueExtender other extend2 xs)
public export
Free : {n : Nat} -> Free CommutativeMonoidTheory (cast $ Fin n)
Free = MkFree
  { Data = FreeCommutativeMonoidOver n
  , UP   = IsFree
    { Exists = Extender
    , Unique = Uniqueness
    }
  }
