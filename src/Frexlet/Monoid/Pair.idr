||| Monoid structures over pairs
module Frexlet.Monoid.Pair

import Frex
import Frex.Signature
import Frex.Algebra
import Frex.Presentation

import Frex.Model
import Frexlet.Monoid.Theory
import Frexlet.Monoid.Frex.Properties
import Data.Setoid
import Data.Setoid.Pair

%default total

public export
Unit : Setoid
Unit = MkSetoid Builtin.Unit (EqualEquivalence Builtin.Unit)

public export
leftNeut : {a : Setoid} -> Pair Unit a <~> a
leftNeut = MkIsomorphism fwd bwd
             (IsIsomorphism (\((), x) => MkAnd Refl (a.equivalence.reflexive x))
                            a.equivalence.reflexive)
   where fwd : Pair Unit a ~> a
         fwd = MkSetoidHomomorphism snd (\_, _, prf => prf.snd)
         bwd : a ~> Pair Unit a
         bwd = MkSetoidHomomorphism (\x => ((), x)) (\_, _, prf => MkAnd Refl prf)

public export
rightNeut : {a : Setoid} -> Pair a Unit <~> a
rightNeut = MkIsomorphism fwd bwd
             (IsIsomorphism (\(x, ()) => MkAnd (a.equivalence.reflexive x) Refl)
                            a.equivalence.reflexive)
   where fwd : Pair a Unit ~> a
         fwd = MkSetoidHomomorphism fst (\_, _, prf => prf.fst)
         bwd : a ~> Pair a Unit
         bwd = MkSetoidHomomorphism (\x => (x, ())) (\_, _, prf => MkAnd prf Refl)

public export
assoc : {a,b,c : Setoid} -> Pair a (Pair b c) <~> Pair (Pair a b) c
assoc = MkIsomorphism fwd bwd
         (IsIsomorphism (\(x,(y,z)) => (Pair a (Pair b c)).equivalence.reflexive (x,(y,z)))
                        (\((x,y),z) => (Pair (Pair a b) c).equivalence.reflexive ((x,y),z)))
   where fwd : Pair a (Pair b c) ~> Pair (Pair a b) c
         fwd = MkSetoidHomomorphism (\abc => ((fst abc,fst (snd abc)), snd (snd abc)))
                  (\_, _, (MkAnd ap (MkAnd bp cp)) => MkAnd (MkAnd ap bp) cp)
         bwd : Pair (Pair a b) c ~> Pair a (Pair b c)
         bwd = MkSetoidHomomorphism (\abc => (fst (fst abc), (snd (fst abc), snd abc)))
                  (\_, _, (MkAnd (MkAnd ap bp) cp) => (MkAnd ap (MkAnd bp cp)))

public export
MonoidPair : Monoid
MonoidPair = MkModel
  { Algebra = MkSetoidAlgebra
      { algebra = MkAlgebra
        { U = Setoid
        , Sem = \case
           Neutral => Unit
           Product => Pair }
      , equivalence = IsoEquivalence
      , congruence = \case
          MkOp Neutral => \_,_,_ => refl
          MkOp Product => \[x1,x2], [y1,y2], idx => (pairIso (idx FZ) (idx (FS FZ))) }
  , Validate = \case
      LftNeutrality => \env => leftNeut
      RgtNeutrality => \env => rightNeut
      Associativity => \env => assoc }
