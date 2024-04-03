import Frex
import Frexlet.Monoid

------------------------------------------------------------------------
-- Hiding definitions conflicting with axiom names

%hide Axiom.lftNeutrality
%hide Axiom.rgtNeutrality
%hide Axiom.associativity

%unbound_implicits off

parameters (m : Model MonoidTheory)

------------------------------------------------------------------------
-- Boilerplate: equivalence & congruence combinator

  export infix 0 =~=
  0 (=~=) : U m -> U m -> Type
  x =~= y = (cast m).equivalence.relation x y

  Sig : Signature
  Sig = MonoidTheory .signature

  Val : U m -> Term Sig (Maybe (U m))
  Val v = Done (Just v)

  0 Context : Type
  Context = Term Sig (Maybe (U m)) -> Term Sig (Maybe (U m))

  (.asContext) : Context -> (U m -> U m)
  f .asContext x = m .Sem (cast $ f (Done Nothing))
                 $ either id (\ k => index k [x])

  Cong : (f : Context) -> {x, y : U m} ->
         x =~= y -> f .asContext x =~= f .asContext y
  Cong f {x, y} eq = m.cong 1 (cast $ f (Done Nothing)) [x] [y] [eq]

------------------------------------------------------------------------
-- Term combinators

  zero : U m
  zero = m .Algebra .algebra .Semantics (MkOp  Neutral) []

  export infixl 8 <>
  (<>) : U m -> U m -> U m
  x <> y = m .Algebra .algebra .Semantics (MkOp  Product) [x, y]

------------------------------------------------------------------------
-- Context combinators

  zero' : Term Sig (Maybe (U m))
  zero' = Call (MkOp  Neutral) []

  export infixl 8 :<>
  (:<>) : Term Sig (Maybe (U m)) -> Term Sig (Maybe (U m)) -> Term Sig (Maybe (U m))
  x :<> y = Call (MkOp  Product) [x, y]

------------------------------------------------------------------------
-- Proofs the axioms hold in the model

  lftNeutrality : (x : U m) -> zero <> x =~= x
  lftNeutrality x = m.Validate LftNeutrality (\ k => index k [x])

  rgtNeutrality : (x : U m) -> x <> zero =~= x
  rgtNeutrality x = m.Validate RgtNeutrality (\ k => index k [x])

  associativity : (x, y, z : U m) -> x <> (y <> z) =~= x <> y <> z
  associativity x y z = m.Validate Associativity (\ k => index k [x, y, z])

------------------------------------------------------------------------
-- Lemmas

  trivial : (x : U m) -> x =~= x
  trivial x = CalcWith (cast m) $
    |~ x

  trivial2 : (x, y : U m) -> x <> y =~= x <> y
  trivial2 x y = CalcWith (cast m) $
    |~ x <> y

  assoc : (x, y, z : U m) -> x <> (y <> z) =~= x <> y <> z
  assoc x y z = CalcWith (cast m) $
    |~ x <> (y <> z)
    ~~ x <> (y <> (zero <> z))
      ..<( Cong (\ focus => Val x :<> (Val y :<> focus)) $ lftNeutrality z )
    ~~ x <> (y <> (zero <> z <> zero))
      ..<( Cong (\ focus => Val x :<> (Val y :<> focus)) $ rgtNeutrality (zero <> z) )
    ~~ x <> (zero <> y <> (zero <> z <> zero))
      ..<( Cong (\ focus => Val x :<> (focus :<> (zero' :<> Val z :<> zero'))) $ lftNeutrality y )
    ~~ x <> (zero <> y <> zero <> (zero <> z <> zero))
      ..<( Cong (\ focus => Val x :<> (focus :<> (zero' :<> Val z :<> zero'))) $ rgtNeutrality (zero <> y) )
    ~~ zero <> x <> (zero <> y <> zero <> (zero <> z <> zero))
      ..<( Cong (\ focus => focus :<> (zero' :<> Val y :<> zero' :<> (zero' :<> Val z :<> zero'))) $ lftNeutrality x )
    ~~ zero <> x <> (zero <> y <> zero) <> (zero <> z <> zero)
      ...( associativity (zero <> x) (zero <> y <> zero) (zero <> z <> zero) )
    ~~ x <> (zero <> y <> zero) <> (zero <> z <> zero)
      ...( Cong (\ focus => focus :<> (zero' :<> Val y :<> zero') :<> (zero' :<> Val z :<> zero')) $ lftNeutrality x )
    ~~ x <> (zero <> y) <> (zero <> z <> zero)
      ...( Cong (\ focus => Val x :<> focus :<> (zero' :<> Val z :<> zero')) $ rgtNeutrality (zero <> y) )
    ~~ x <> y <> (zero <> z <> zero)
      ...( Cong (\ focus => Val x :<> focus :<> (zero' :<> Val z :<> zero')) $ lftNeutrality y )
    ~~ x <> y <> (zero <> z)
      ...( Cong (\ focus => Val x :<> Val y :<> focus) $ rgtNeutrality (zero <> z) )
    ~~ x <> y <> z
      ...( Cong (\ focus => Val x :<> Val y :<> focus) $ lftNeutrality z )

  units : (x : U m) -> zero <> (x <> zero) <> zero =~= x
  units x = CalcWith (cast m) $
    |~ zero <> (x <> zero) <> zero
    ~~ zero <> (zero <> x <> zero) <> zero
      ..<( Cong (\ focus => zero' :<> (focus :<> zero') :<> zero') $ lftNeutrality x )
    ~~ zero <> (zero <> (x <> zero)) <> zero
      ..<( Cong (\ focus => zero' :<> focus :<> zero') $ associativity zero x zero )
    ~~ zero <> zero <> (x <> zero) <> zero
      ...( Cong (\ focus => focus :<> zero') $ associativity zero zero (x <> zero) )
    ~~ zero <> zero <> x <> zero <> zero
      ...( Cong (\ focus => focus :<> zero') $ associativity (zero <> zero) x zero )
    ~~ zero <> x <> zero <> zero
      ...( Cong (\ focus => focus :<> Val x :<> zero' :<> zero') $ lftNeutrality zero )
    ~~ zero <> x <> (zero <> zero)
      ..<( associativity (zero <> x) zero zero )
    ~~ zero <> x <> zero
      ...( Cong (\ focus => zero' :<> Val x :<> focus) $ lftNeutrality zero )
    ~~ zero <> x
      ...( rgtNeutrality (zero <> x) )
    ~~ x
      ...( lftNeutrality x )