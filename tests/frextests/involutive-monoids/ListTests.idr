module ListTests

import Frex
import Frexlet.Monoid.Involutive
import Frexlet.Monoid.Involutive.Notation
import Frexlet.Monoid.Notation.Multiplicative

inv : Term (Frexlet.Monoid.Involutive.Theory.Signature) a -> Term (Frexlet.Monoid.Involutive.Theory.Signature) a
inv x = Call (MkOp Involution) [x]

test : {A : Setoid} -> {x,y : List (U A)} -> A .ListEquality (reverse (reverse y ++ ([] ++ reverse x)))
                                                             (x ++ y)
test = frexify (Frexlet.Monoid.Involutive.Frex.Frex List _) [x,y]
         { prf = ConsUlt (A .ListEqualityReflexive _) (MkAnd Refl Refl) $
                 ConsUlt (A .ListEqualityReflexive _) (MkAnd Refl Refl) $ Ultimate (A .ListEqualityReflexive _) }
         $ (((Dyn 1) .inv .*. (I1 .*. (Dyn 0) .inv)) .inv)
            =-=
           (Dyn 0 .*. Dyn 1)

PropListMonoid : {A:Type} -> Monoid
PropListMonoid = MkModel
  { Algebra = cast {from = Algebra Frexlet.Monoid.Theory.Signature} $ MkAlgebra
        { U = List A
        , Sem = \case
            Neutral => []
            Product => (++) }
  , Validate = \case
      LftNeutrality => \env => Refl
      RgtNeutrality => \env => appendNilRightNeutral _
      Associativity => \env => appendAssociative _ _ _ }

PropListInvolutiveMonoid : {A: Type} -> InvolutiveMonoid
PropListInvolutiveMonoid = MkModel (MkInvolutiveMonoidStructure ((PropListMonoid {A=A}) .Algebra)
  (MkSetoidHomomorphism Data.List.reverse (\_,_,Refl => Refl)))
  $ \case
     (Mon LftNeutrality) => PropListMonoid .Validate LftNeutrality
     (Mon RgtNeutrality) => PropListMonoid .Validate RgtNeutrality
     (Mon Associativity) => PropListMonoid .Validate Associativity
     Involutivity        => \env => reverseInvolutive _
     Antidistributivity  => \env => sym (revAppend _ _)

testProp : {A : Type} -> {x,y : List A} -> reverse (reverse y ++ ([] ++ reverse x)) = x ++ y
testProp = solve 2 (Frex PropListInvolutiveMonoid _)
         $ ((Dyn 1) .inv .*. (I1 .*. (Dyn 0) .inv)) .inv =-= Dyn 0 .*. Dyn 1
