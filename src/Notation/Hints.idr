module Notation.Hints

import Frex

namespace Algebra
  public export 0
  NotationHint : (a : Algebra sig) -> (notation : Type -> Type) -> Type
  NotationHint a notation = {0 b : Type} -> (0 ford : b = U a) => notation b

  public export
  (.notationHint) : (0 a : Algebra sig) -> (0 notation : Type -> Type) ->
    (implem : notation (U a)) -> NotationHint a notation
  a.notationHint notation implem @{Refl} = implem

namespace Model
  public export 0
  NotationHint : (a : Model pres) -> (notation : Type -> Type) -> Type
  NotationHint a notation = {0 b : Type} -> (0 ford : b = U a) => notation b

  public export
  (.notationHint) : (0 a : Model pres) -> (0 notation : Type -> Type) ->
    (implem : notation (U a)) -> NotationHint a notation
  a.notationHint notation implem @{Refl} = implem
