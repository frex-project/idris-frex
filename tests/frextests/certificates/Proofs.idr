import Data.Setoid

import Frex
import Frexlet.Monoid
import Frexlet.Monoid.Notation.Additive

import Notation.Hints

%hide Frex.Axiom.lftNeutrality
%hide Frex.Axiom.rgtNeutrality

parameters (m : Model MonoidTheory)

  export infix 0 =~=
  0 (=~=) : (x, y : U m) -> Type
  x =~= y = (cast m).equivalence.relation x y

  %hint
  notation1 : NotationHint m Additive1
  notation1 = m.notationHint Additive1
            (Prelude.cast $ Additive.Model.cast m)

  %hint
  notation2 : Additive2 (Term Signature (Maybe (U m)))
  notation2 = notationAdd2

  Val : U m -> Term Signature (Maybe (U m))
  Val v = Done (Just v)

  (.asContext) :
    (Term Signature (Maybe (U m)) -> Term Signature (Maybe (U m))) ->
    U m -> U m
  f .asContext x = m .Sem (cast $ f (Done Nothing))
                 $ either id (\ k => index k [x])

  Cong : (f : Term Signature (Maybe (U m)) -> Term Signature (Maybe (U m))) ->
         {x, y : U m} -> x =~= y ->
         f .asContext x =~= f .asContext y
  Cong f {x, y} eq = m.cong 1 (cast $ f (Done Nothing)) [x] [y] [eq]

  lftNeutrality : (x : U m) -> O1 .+. x =~= x
  lftNeutrality x = m.Validate LftNeutrality (\ k => index k [x])

  rgtNeutrality : (x : U m) -> x .+. O1 =~= x
  rgtNeutrality x = m.Validate RgtNeutrality (\ k => index k [x])

  associativity : (x, y, z : U m) -> x .+. (y .+. z) =~= x .+. y .+. z
  associativity x y z = m.Validate Associativity (\ k => index k [x, y, z])

  trivial : (x : U m) -> x =~= x
  trivial x = CalcWith (cast m) $
    |~ x

  trivial2 : (x, y : U m) -> x .+. y =~= x .+. y
  trivial2 x y = CalcWith (cast m) $
    |~ x .+. y

  assoc : (x, y, z : U m) -> x .+. (y .+. z) =~= x .+. y .+. z
  assoc x y z = CalcWith (cast m) $
    |~ x .+. (y .+. z)
    ~~ x .+. (y .+. (O1 .+. z))
      ..<( Cong (\ focus => Val x :+: (Val y :+: focus)) $ lftNeutrality z )
    ~~ x .+. (y .+. (O1 .+. z .+. O1))
      ..<( Cong (\ focus => Val x :+: (Val y :+: focus)) $ rgtNeutrality (O1 .+. z) )
    ~~ x .+. (O1 .+. y .+. (O1 .+. z .+. O1))
      ..<( Cong (\ focus => Val x :+: (focus :+: (O2 :+: Val z :+: O2))) $ lftNeutrality y )
    ~~ x .+. (O1 .+. y .+. O1 .+. (O1 .+. z .+. O1))
      ..<( Cong (\ focus => Val x :+: (focus :+: (O2 :+: Val z :+: O2))) $ rgtNeutrality (O1 .+. y) )
    ~~ O1 .+. x .+. (O1 .+. y .+. O1 .+. (O1 .+. z .+. O1))
      ..<( Cong (\ focus => focus :+: (O2 :+: Val y :+: O2 :+: (O2 :+: Val z :+: O2))) $ lftNeutrality x )
    ~~ O1 .+. x .+. (O1 .+. y .+. O1) .+. (O1 .+. z .+. O1)
      ...( associativity (O1 .+. x) (O1 .+. y .+. O1) (O1 .+. z .+. O1) )
    ~~ x .+. (O1 .+. y .+. O1) .+. (O1 .+. z .+. O1)
      ...( Cong (\ focus => focus :+: (O2 :+: Val y :+: O2) :+: (O2 :+: Val z :+: O2)) $ lftNeutrality x )
    ~~ x .+. (O1 .+. y) .+. (O1 .+. z .+. O1)
      ...( Cong (\ focus => Val x :+: focus :+: (O2 :+: Val z :+: O2)) $ rgtNeutrality (O1 .+. y) )
    ~~ x .+. y .+. (O1 .+. z .+. O1)
      ...( Cong (\ focus => Val x :+: focus :+: (O2 :+: Val z :+: O2)) $ lftNeutrality y )
    ~~ x .+. y .+. (O1 .+. z)
      ...( Cong (\ focus => Val x :+: Val y :+: focus) $ rgtNeutrality (O1 .+. z) )
    ~~ x .+. y .+. z
      ...( Cong (\ focus => Val x :+: Val y :+: focus) $ lftNeutrality z )

  units : (x : U m) -> O1 .+. (x .+. O1) .+. O1 =~= x
  units x = CalcWith (cast m) $
    |~ O1 .+. (x .+. O1) .+. O1
    ~~ O1 .+. (O1 .+. x .+. O1) .+. O1
      ..<( Cong (\ focus => O2 :+: (focus :+: O2) :+: O2) $ lftNeutrality x )
    ~~ O1 .+. (O1 .+. (x .+. O1)) .+. O1
      ..<( Cong (\ focus => O2 :+: focus :+: O2) $ associativity O1 x O1 )
    ~~ O1 .+. O1 .+. (x .+. O1) .+. O1
      ...( Cong (\ focus => focus :+: O2) $ associativity O1 O1 (x .+. O1) )
    ~~ O1 .+. O1 .+. x .+. O1 .+. O1
      ...( Cong (\ focus => focus :+: O2) $ associativity (O1 .+. O1) x O1 )
    ~~ O1 .+. x .+. O1 .+. O1
      ...( Cong (\ focus => focus :+: Val x :+: O2 :+: O2) $ lftNeutrality O1 )
    ~~ O1 .+. x .+. (O1 .+. O1)
      ..<( associativity (O1 .+. x) O1 O1 )
    ~~ O1 .+. x .+. O1
      ...( Cong (\ focus => O2 :+: Val x :+: focus) $ lftNeutrality O1 )
    ~~ O1 .+. x
      ...( rgtNeutrality (O1 .+. x) )
    ~~ x
      ...( lftNeutrality x )
