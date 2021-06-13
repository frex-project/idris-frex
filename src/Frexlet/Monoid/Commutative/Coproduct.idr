||| The coproduct of two commutative monoids is their cartesian product
module Frexlet.Monoid.Commutative.Coproduct

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
import Data.Nat
import public Data.Vect.Extra
import Data.Vect.Extra1

%default total

public export
CoprodAlgebraStructure : (a, b : CommutativeMonoid) -> Algebra Signature
CoprodAlgebraStructure a b = 
  let %hint aNotation : Action1 Nat (U a)
      aNotation = NatAction1 (a)
      %hint bNotation : Action1 Nat (U b)
      bNotation = NatAction1 (b)
  in MkAlgebra 
  { U = (U a, U b)
  , Sem = \case 
    Neutral => (O1, O1)
    Product => \xy1,xy2 => (fst xy1 .+. fst xy2, snd xy1 .+. snd xy2)
  }

public export
CoprodSetoidEquivalence : (a, b : CommutativeMonoid) -> Equivalence (U a, U b)
CoprodSetoidEquivalence a b = 
  let %hint aNotation : Action1 Nat (U a)
      aNotation = NatAction1 (a)
      %hint bNotation : Action1 Nat (U b)
      bNotation = NatAction1 (b)
      0 Rel : (xy1, xy2 : (U a, U b)) -> Type
      Rel xy1 xy2 = ( a.rel (fst xy1) (fst xy2)
                    , b.rel (snd xy1) (snd xy2))
  in MkEquivalence 
  { relation = Rel
  , reflexive = \x => ( a.equivalence.reflexive (fst x)
                      , b.equivalence.reflexive (snd x))
  , symmetric = \x,y,prf => ( a.equivalence.symmetric (fst x) (fst y) (fst prf)
                            , b.equivalence.symmetric (snd x) (snd y) (snd prf))
  , transitive = \x,y,z,prf1,prf2 => 
     ( a.equivalence.transitive (fst x) (fst y) (fst z) (fst prf1) (fst prf2)
     , b.equivalence.transitive (snd x) (snd y) (snd z) (snd prf1) (snd prf2))
  }
  
public export
CoprodSetoid : (a, b : CommutativeMonoid) -> Setoid
CoprodSetoid a b = MkSetoid
  { U = (U a, U b)
  , equivalence = CoprodSetoidEquivalence a b
  }
  
public export
CoprodAlgebraCongruence : (a, b : CommutativeMonoid) -> (op : Op Signature) -> 
  CongruenceWRT (CoprodSetoid a b) ((CoprodAlgebraStructure a b).Sem op)
CoprodAlgebraCongruence a b (0 ** Neutral)      xy1       xy2       prf 
   = ( a.Algebra.congruence (0 ** Neutral) [] [] (\i => case i of {})
     , b.Algebra.congruence (0 ** Neutral) [] [] (\i => case i of {}))
CoprodAlgebraCongruence a b op@(2 ** Product) [xy1,xy2] [uv1,uv2] prf 
   = ( a.Algebra.congruence Plus [fst xy1, fst xy2] [fst uv1, fst uv2] 
         \case {0 => fst (prf 0); 1 => fst (prf 1)}
     , b.Algebra.congruence Plus [snd xy1, snd xy2] [snd uv1, snd uv2] 
         \case {0 => snd (prf 0); 1 => snd (prf 1)})

public export
CoprodAlgebra : (a, b : CommutativeMonoid) -> MonoidStructure
CoprodAlgebra a b = MkSetoidAlgebra
  { algebra = CoprodAlgebraStructure a b
  , equivalence = CoprodSetoidEquivalence a b
  , congruence = CoprodAlgebraCongruence a b
  }

public export
CoprodValidate : (a, b : CommutativeMonoid) -> 
  Validates CommutativeMonoidTheory (CoprodAlgebra a b)
CoprodValidate a b (Mon LftNeutrality) env 
    = ( a.Validate (Mon LftNeutrality) (fst . env) 
      , b.Validate (Mon LftNeutrality) (snd . env))
CoprodValidate a b (Mon RgtNeutrality) env 
    = ( a.Validate (Mon RgtNeutrality) (fst . env) 
      , b.Validate (Mon RgtNeutrality) (snd . env))
CoprodValidate a b (Mon Associativity) env 
    = ( a.Validate (Mon Associativity) (fst . env) 
      , b.Validate (Mon Associativity) (snd . env))
CoprodValidate a b Commutativity env 
    = ( a.Validate Commutativity (fst . env) 
      , b.Validate Commutativity (snd . env))

public export
Coprod : (a, b : CommutativeMonoid)  -> CommutativeMonoid
Coprod a b = MkModel 
  { Algebra = CoprodAlgebra a b
  , Validate = CoprodValidate a b
  } 

public export
CoprodLftFunction : (a, b : CommutativeMonoid)  -> U a -> U (Coprod a b)
CoprodLftFunction a b x = 
  let %hint bNotation : Action1 Nat (U b)
      bNotation = NatAction1 (b)
  in (x, O1)

public export
CoprodLftSetoidHomomorphism : (a, b : CommutativeMonoid)  -> 
  SetoidHomomorphism (cast a) (cast $ Coprod a b) (CoprodLftFunction a b)
CoprodLftSetoidHomomorphism a b x y prf = (prf, b.equivalence.reflexive _)

public export
CoprodLftHomomorphism : (a, b : CommutativeMonoid)  -> 
  Homomorphism a.Algebra (Coprod a b).Algebra (CoprodLftFunction a b)
CoprodLftHomomorphism a b (0 ** Neutral) [] 
  = let %hint aNotation : Action1 Nat (U a)
        aNotation = NatAction1 (a)
        %hint bNotation : Action1 Nat (U b)
        bNotation = NatAction1 (b)
  in (Coprod a b).equivalence.reflexive (O1, O1)
CoprodLftHomomorphism a b (2 ** Product) [x1,x2] = 
  let %hint aNotation : Action1 Nat (U a)
      aNotation = NatAction1 (a)
      %hint bNotation : Action1 Nat (U b)
      bNotation = NatAction1 (b)
  in ( a.equivalence.reflexive (x1 .+. x2)
     , b.equivalence.symmetric _ _ 
     $ b.validate (Mon LftNeutrality) [O1])
     
-- The Rgt case is analogous to the Lft case     
     
public export
CoprodRgtFunction : (a, b : CommutativeMonoid)  -> U b -> U (Coprod a b)
CoprodRgtFunction a b y = 
  let %hint aNotation : Action1 Nat (U a)
      aNotation = NatAction1 (a)
  in (O1, y)

public export
CoprodRgtSetoidHomomorphism : (a, b : CommutativeMonoid)  -> 
  SetoidHomomorphism (cast b) (cast $ Coprod a b) (CoprodRgtFunction a b)
CoprodRgtSetoidHomomorphism a b x y prf = (a.equivalence.reflexive _, prf)

public export
CoprodRgtHomomorphism : (a, b : CommutativeMonoid)  -> 
  Homomorphism b.Algebra (Coprod a b).Algebra (CoprodRgtFunction a b)
CoprodRgtHomomorphism a b (0 ** Neutral) [] 
  = let %hint aNotation : Action1 Nat (U a)
        aNotation = NatAction1 (a)
        %hint bNotation : Action1 Nat (U b)
        bNotation = NatAction1 (b)
  in (Coprod a b).equivalence.reflexive (O1, O1)
CoprodRgtHomomorphism a b (2 ** Product) [y1,y2] = 
  let %hint aNotation : Action1 Nat (U a)
      aNotation = NatAction1 (a)
      %hint bNotation : Action1 Nat (U b)
      bNotation = NatAction1 (b)
  in ( a.equivalence.symmetric _ _ 
     $ a.validate (Mon LftNeutrality) [O1]
     , b.equivalence.reflexive (y1 .+. y2))
     
public export
Coproduct : (a, b : CommutativeMonoid) -> (a <~.~> b)
Coproduct a b = MkCospan 
  { Sink = Coprod a b
  , Lft = MkSetoidHomomorphism
          { H = MkSetoidHomomorphism
            { H = CoprodLftFunction a b
            , homomorphic = CoprodLftSetoidHomomorphism a b
            }
          , preserves = CoprodLftHomomorphism a b
          }
  , Rgt = MkSetoidHomomorphism
          { H = MkSetoidHomomorphism
            { H = CoprodRgtFunction a b
            , homomorphic = CoprodRgtSetoidHomomorphism a b
            }
          , preserves = CoprodRgtHomomorphism a b
          }
  }

public export
ExtenderFunction : (a,b : CommutativeMonoid) -> ExtenderFunction (Coproduct a b)
ExtenderFunction a b other xy
  = let %hint otherNotation : Action1 Nat (U other.Sink)
        otherNotation = NatAction1 (other.Sink)
    in other.Lft.H.H (fst xy) .+. other.Rgt.H.H (snd xy)

public export
ExtenderSetoidHomomorphism : (a, b : CommutativeMonoid) -> ExtenderSetoidHomomorphism (Coproduct a b)
ExtenderSetoidHomomorphism a b other 
  = let %hint otherNotation : Action1 Nat (U other.Sink)
        otherNotation = NatAction1 (other.Sink)
    in MkSetoidHomomorphism
    { H = ExtenderFunction a b other
    , homomorphic = \xy, uv, prf => other.Sink.cong 2 (Dyn 0 .+. Dyn 1) [_,_] [_,_]
      [ other.Lft.H.homomorphic (fst xy) (fst uv) (fst prf) 
      , other.Rgt.H.homomorphic (snd xy) (snd uv) (snd prf) 
      ]
    }

public export
ExtenderIsHomomorphism : (a, b : CommutativeMonoid) -> (other : a <~.~> b) ->
  Homomorphism (Coprod a b).Algebra other.Sink.Algebra (ExtenderFunction a b other)
ExtenderIsHomomorphism a b other (0 ** Neutral) [] 
  = let %hint otherNotation : Action1 Nat (U other.Sink)
        otherNotation = NatAction1 (other.Sink)
        %hint aNotation : Action1 Nat (U a)
        aNotation = NatAction1 (a)
        %hint bNotation : Action1 Nat (U b)
        bNotation = NatAction1 (b)
        h : (U $ Coprod a b) -> U other.Sink
        h = ExtenderFunction a b other
    in CalcWith @{cast other.Sink} $
    |~ h (O1, O1)
    ~~ (other.Lft.H.H O1) .+. (other.Rgt.H.H O1)   ...(Refl)
    <~ O1 .+. O1 ...(other.Sink.cong 2 (Dyn 0 .+. Dyn 1) [_,_] [_,_]
                    [other.Lft.preserves Zero []
                    ,other.Rgt.preserves Zero []])
    <~ O1 ...(other.Sink.validate (Mon LftNeutrality) [O1])
ExtenderIsHomomorphism a b other (2 ** Product) [(x1,y1),(x2,y2)] 
  = let %hint otherNotation : Action1 Nat (U other.Sink)
        otherNotation = NatAction1 (other.Sink)
        %hint aNotation : Action1 Nat (U a)
        aNotation = NatAction1 (a)
        %hint bNotation : Action1 Nat (U b)
        bNotation = NatAction1 (b)
        %hint abNotation : Action1 Nat (U $ Coprod a b)
        abNotation = NatAction1 (Coprod a b)
        h : (U $ Coprod a b) -> U other.Sink
        h = ExtenderFunction a b other
    in CalcWith @{cast other.Sink} $
    |~ h ((x1, y1) .+. (x2, y2))
    ~~ other.Lft.H.H (x1 .+. x2) .+. other.Rgt.H.H (y1 .+. y2) 
                                ...(Refl)
    <~ (other.Lft.H.H x1 .+. other.Lft.H.H x2) .+. (other.Rgt.H.H y1 .+. other.Rgt.H.H y2) 
                                ...(other.Sink.cong 2 (Dyn 0 .+. Dyn 1) [_,_] [_,_]
                                                               [ other.Lft.preserves Plus [x1, x2]
                                                               , other.Rgt.preserves Plus [y1, y2]])
    <~ (other.Lft.H.H x1 .+. other.Rgt.H.H y1) .+. (other.Lft.H.H x2 .+. other.Rgt.H.H y2) 
                                ...(interchange other.Sink _ _ _ _)
    ~~ h (x1, y1) .+. h(x2, y2) ...(Refl)

public export
Extender : (a, b : CommutativeMonoid) -> Extender (Coproduct a b)
Extender a b other 
  = let %hint otherNotation : Action1 Nat (U other.Sink)
        otherNotation = NatAction1 (other.Sink)
        %hint aNotation : Action1 Nat (U a)
        aNotation = NatAction1 (a)
        %hint bNotation : Action1 Nat (U b)
        bNotation = NatAction1 (b)
        h : (U $ Coprod a b) -> U other.Sink
        h = ExtenderFunction a b other
    in MkCospanMorphism
    { H = MkSetoidHomomorphism 
          { H = ExtenderSetoidHomomorphism a b other
          , preserves = ExtenderIsHomomorphism a b other
          }
    , preserve = IsPreserving
       { Lft = \x => CalcWith @{cast other.Sink} $
           |~ h (x, O1)
           ~~ other.Lft.H.H x .+. other.Rgt.H.H O1 ...(Refl)
           <~ other.Lft.H.H x .+. O1 ...(other.Sink.cong 1 (Sta (other.Lft.H.H x) .+. Dyn 0) [_] [_]
                                        [other.Rgt.preserves Zero []])
           <~ other.Lft.H.H x        ...(other.Sink.validate (Mon RgtNeutrality) [_])
       , Rgt = \y => CalcWith @{cast other.Sink} $
           |~ h (O1, y)
           ~~ other.Lft.H.H O1 .+. other.Rgt.H.H y  ...(Refl)
           <~               O1 .+. other.Rgt.H.H y ...(other.Sink.cong 1 
                                                      (Dyn 0 .+. Sta (other.Rgt.H.H y) ) [_] [_]
                                                      [other.Lft.preserves Zero []])
           <~ other.Rgt.H.H y        ...(other.Sink.validate (Mon LftNeutrality) [_])
       }
    }

public export
normalForm : (a, b : CommutativeMonoid) -> (xy : U (Coprod a b)) ->
  let %hint abNotation : Action1 Nat (U $ Coprod a b)
      abNotation = NatAction1 (Coprod a b)
      %hint aNotation : Action1 Nat (U a)
      aNotation = NatAction1 (a)
      %hint bNotation : Action1 Nat (U b)
      bNotation = NatAction1 (b)
  in (Coprod a b).rel 
       ((fst xy, O1) .+. (O1, snd xy))
       xy
normalForm a b (x, y) = 
  ( a.validate (Mon RgtNeutrality) [_]
  , b.validate (Mon LftNeutrality) [_])

public export
extenderUniqueness : (a, b : CommutativeMonoid) -> 
  (other : a <~.~> b) -> (extend : (Coproduct a b) ~> other) ->
  (xy : U (Coprod a b)) -> 
  other.Sink.rel 
    (extend.H.H.H xy)
    ((Extender a b other).H.H.H xy)
extenderUniqueness a b other extend (x,y) = 
  let %hint abNotation : Action1 Nat (U $ Coprod a b)
      abNotation = NatAction1 (Coprod a b)
      %hint aNotation : Action1 Nat (U a)
      aNotation = NatAction1 (a)
      %hint bNotation : Action1 Nat (U b)
      bNotation = NatAction1 (b)
      %hint otherNotation : Action1 Nat (U $ other.Sink)
      otherNotation = NatAction1 (other.Sink)
      h : U (Coprod a b) -> U other.Sink
      h = ExtenderFunction a b other
  in CalcWith @{cast other.Sink} $
  |~ extend.H.H.H (x,y)
  <~ extend.H.H.H ((x, O1) .+. (O1, y))            ...(other.Sink.equivalence.symmetric _ _ $
                                                       extend.H.H.homomorphic _ _ $
                                                       normalForm a b (x,y))
  <~ extend.H.H.H (x, O1) .+. extend.H.H.H (O1, y) ...(extend.H.preserves Plus [_,_])
  <~ other.Lft.H.H x .+. other.Rgt.H.H y           ...(other.Sink.cong 2 (Dyn 0 .+. Dyn 1) [_,_] [_,_]
                                                      [ extend.preserve.Lft _
                                                      , extend.preserve.Rgt _ ])
  ~~ h (x,y)  ...(Refl)

public export
Uniqueness : (a, b : CommutativeMonoid) -> Uniqueness (Coproduct a b)
Uniqueness a b other extend1 extend2 xy = CalcWith @{cast other.Sink} $
  |~ extend1.H.H.H xy
  <~ ExtenderFunction a b other xy ...(extenderUniqueness a b other extend1 xy)
  <~ extend2.H.H.H xy              ...(other.Sink.equivalence.symmetric _ _ $
                                       extenderUniqueness a b other extend2 xy)

public export
CoproductCospan : (a,b : CommutativeMonoid) -> Coproduct a b
CoproductCospan a b = MkCoproduct
  { Data = Coproduct a b
  , UP   = IsUniversal
    { Exists = Extender a b
    , Unique = Uniqueness a b
    }
  }
