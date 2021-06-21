||| The syntax and axioms for involutive monoids
module Frexlet.Monoid.Involutive.Theory

import Frex

import public Frexlet.Monoid

public export
data Operation : Nat -> Type where
  Mono : Monoid.Theory.Operation n -> Operation n
  Involution : Operation 1

public export
Signature : Signature
Signature = MkSignature Involutive.Theory.Operation

%hint
public export
castOp : Monoid.Theory.Signature ~> Involutive.Theory.Signature
castOp = OpTranslation Mono

namespace Axiom
  public export
  data Axiom 
    = Mon Monoid.Theory.Axiom
    | Involutivity
    | Antidistributivity

public export
InvolutiveMonoidTheory : Presentation
InvolutiveMonoidTheory = MkPresentation Involutive.Theory.Signature Involutive.Theory.Axiom.Axiom 
  \case
    Mon ax => cast ((MonoidTheory).axiom ax)
    Involutivity       => involutivity       Involution
    Antidistributivity => antidistributivity Involution (Mono Product)

public export
InvolutiveMonoidStructure, InvolutiveMonoid : Type
InvolutiveMonoidStructure = SetoidAlgebra (InvolutiveMonoidTheory).signature
InvolutiveMonoid          = Model          InvolutiveMonoidTheory

||| Smart constructor for involutive monoid structures
public export
MkInvolutiveMonoidStructure : (monoid : MonoidStructure) -> 
    (involution : cast monoid ~> cast monoid) ->
    InvolutiveMonoidStructure
MkInvolutiveMonoidStructure monoid involution = MkSetoidAlgebra
  { algebra = MakeAlgebra 
      { U   = U monoid
      , Semantics = \case
          (MkOp (Mono op )) => monoid.algebra.Semantics (MkOp op)
          (MkOp Involution) => involution.H . head
          {-Mono op    => monoid.Semantics op
          Involution => involution.H-}
      }
  , equivalence = monoid.equivalence
  , congruence = \case 
      MkOp (Mono op)  => monoid.congruence (MkOp op)
      MkOp Involution => \ [x],[y],prf => involution.homomorphic x y (prf 0)
  }

||| Smart constructor for involutive monoids
public export
MkInvolutiveMonoid 
  : (monoid : Monoid) -> 
    (involution : cast monoid ~> cast monoid) ->
    let invMonoid = (MkInvolutiveMonoidStructure monoid.Algebra involution) in
    (involutivity        : ValidatesEquation
       (Axiom.involutivity {sig = Involutive.Theory.Signature} Involution)
       invMonoid) ->
    (antidistributivity  : ValidatesEquation
       (Axiom.antidistributivity {sig = Involutive.Theory.Signature} Involution (Mono Product))
       invMonoid) ->
    InvolutiveMonoid

public export
Cast InvolutiveMonoid Monoid where
  cast invMonoid = MkModel 
    { Algebra  = MkSetoidAlgebra 
      { algebra = MakeAlgebra
          { U = U invMonoid
          , Semantics = \f => invMonoid.Algebra.algebra.Semantics (MkOp $ Mono f.snd) 
          }
      , equivalence = invMonoid.Algebra.equivalence
      , congruence  = \(MkOp op),xs,ys,prf => invMonoid.Algebra.congruence (MkOp (Mono op)) xs ys prf
      }
    , Validate = \case
        LftNeutrality => invMonoid.Validate (Mon LftNeutrality)
        RgtNeutrality => invMonoid.Validate (Mon RgtNeutrality)
        Associativity => invMonoid.Validate (Mon Associativity)
    }

public export
Mon : Op (MonoidTheory).signature -> Op (InvolutiveMonoidTheory).signature
Mon op = MkOp (Mono op.snd)

public export
Involute : Op (InvolutiveMonoidTheory).signature
Involute = MkOp Involution
