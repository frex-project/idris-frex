module Frexlet.Group.Theory

import Frex

import public Frexlet.Monoid

%default total


public export
data Operation : Nat -> Type where
  Mono    : Monoid.Theory.Operation n -> Operation n
  Inverse : Operation 1

public export
Signature : Signature
Signature = MkSignature Group.Theory.Operation


%hint
public export
castOp : Monoid.Theory.Signature ~> Group.Theory.Signature
castOp = OpTranslation Mono

public export
data Axiom
  = Mon Monoid.Theory.Axiom
  | LftInverse
  | RgtInverse


public export
GroupTheory : Presentation
GroupTheory = MkPresentation Group.Theory.Signature
                             Group.Theory.Axiom $
  \case
    Mon ax => cast ((MonoidTheory).axiom ax)
    LftInverse => lftInverse (Mono Neutral) Inverse (Mono Product)
    RgtInverse => rgtInverse (Mono Neutral) Inverse (Mono Product)

public export
Group,GroupStructure : Type
Group = Model GroupTheory
GroupStructure = SetoidAlgebra (GroupTheory).signature

public export
MkGroupStructure : (monoid : MonoidStructure) ->
  (inverse : cast {to = Setoid} monoid ~> cast monoid) ->
  GroupStructure
MkGroupStructure monoid inverse = MkSetoidAlgebra
  { algebra = MakeAlgebra
      { U = U monoid
      , Semantics = \case
          (MkOp (Mono op)) => monoid.algebra.Semantics (MkOp op)
          (MkOp Inverse)   => inverse.H . head
      }
  , equivalence = monoid.equivalence
  , congruence  = \case
      (MkOp (Mono op)) => monoid.congruence (MkOp op)
      (MkOp Inverse)   => \[x],[y],prf => inverse.homomorphic x y (prf 0)
  }

||| Smart constructor for groups
public export
MkGroup
  : (monoid : Monoid) ->
    (inverse : cast {to = Setoid} monoid ~> cast monoid) ->
    (lftInversion : ValidatesEquation
                       ((GroupTheory).axiom LftInverse)
                       (MkGroupStructure monoid.Algebra inverse)) ->
    (rgtInversion : ValidatesEquation
                       ((GroupTheory).axiom RgtInverse)
                       (MkGroupStructure monoid.Algebra inverse)) ->
    Group
MkGroup monoid inverse lft rgt = MkModel
  { Algebra = MkGroupStructure monoid.Algebra inverse
  , Validate = \case
      -- silly, but hey
      Mon ax@LftNeutrality => monoid.Validate ax
      Mon ax@RgtNeutrality => monoid.Validate ax
      Mon ax@Associativity => monoid.Validate ax
      LftInverse => lft
      RgtInverse => rgt
  }

public export
Cast GroupStructure MonoidStructure where
  cast group = MkSetoidAlgebra
    { algebra = MakeAlgebra
        { U = U group
        , Semantics = \op =>
            group.algebra.Semantics (MkOp $ Mono op.snd)
        }
    , equivalence = group.equivalence
    , congruence  = \op,env,prf => group.congruence (MkOp $ Mono op.snd) env prf
    }

public export
Cast Group Monoid where
  cast group = MkModel
    { Algebra  = cast group.Algebra
    , Validate = \case
        ax@LftNeutrality => group.Validate (Mon ax)
        ax@RgtNeutrality => group.Validate (Mon ax)
        ax@Associativity => group.Validate (Mon ax)
    }

public export
Unit : Op (GroupTheory).signature
Unit = MkOp $ Mono Neutral

public export
Mult : Op (GroupTheory).signature
Mult = MkOp $ Mono Product

public export
Invert : Op (GroupTheory).signature
Invert = MkOp Inverse

export
[Raw] Show Group.Theory.Axiom where
  show = \case
    Mon ax => show @{Raw} ax
    LftInverse => "LftInverse"
    RgtInverse => "RgtInverse"

export
[Words] Show Group.Theory.Axiom where
  show = \case
    Mon ax => show @{Words} ax
    LftInverse => "LftInverse"
    RgtInverse => "RgtInverse"

export
Finite Group.Theory.Axiom where
  enumerate = map Mon enumerate ++ [LftInverse, RgtInverse]

export
withRaw : Printer (GroupTheory).signature a -> Printer GroupTheory a
withRaw = MkPrinter "GroupTheory" Raw

export
withWords : Printer (GroupTheory).signature a -> Printer GroupTheory a
withWords = MkPrinter "GroupTheory" Words
