||| Constructing the frex of a monoid by a setoid
module Frexlet.Monoid.Frex.Construction

import Frex

import Frexlet.Monoid.Theory
import Frexlet.Monoid.Notation
import Frexlet.Monoid.Frex.Structure
import Frexlet.Monoid.Frex.Properties

import Notation.Multiplicative
import Notation.Action

import Data.List
import Data.List.Elem

import Data.Setoid.Pair

import Syntax.PreorderReasoning.Generic

%default total

public export
reify : (a : Monoid) -> (s : Setoid) -> FrexCarrier a s -> Term Signature (U a `Either` U s)
reify a s (Ultimate i    ) = Done (Left i)
reify a s (ConsUlt i x is) =
  let %hint
      notation : Multiplicative1 (Term Signature (U a `Either` U s))
      notation = notationSyntax
  in Done (Left i) .*. Done (Right x) .*. reify a s is

public export
normalForm : (a : Monoid) -> (s : Setoid) -> (is : FrexCarrier a s) ->
  (FrexMonoid a s).rel
    ((FrexMonoid a s).Sem (reify a s is) (either a.sta a.dyn))
    is
normalForm a s (Ultimate i) = (FrexSetoid a s).equivalence.reflexive _
normalForm a s (ConsUlt i x is) =
  let %hint
      notation : Multiplicative1 (Term Signature (U a `Either` U s))
      notation = notationSyntax
      %hint
      notation' : MAction1 (U a) (FrexCarrier a s)
      notation' = cast $ MonAction a s
      %hint
      notation'' : Multiplicative1 (U a)
      notation'' = a.Multiplicative1
      env : U a `Either` U s -> FrexCarrier a s
      env = either a.sta a.dyn
  in CalcWith @{cast $ FrexMonoid a s} $
  |~ a.sta i .*. a.dyn x .*. (FrexMonoid a s).Sem (reify a s is) env
  ~~ (i .*. I1 , x) :: the (U a) I1 *. ((FrexMonoid a s).Sem (reify a s is) env)
                  ...(Refl)
  <~ (i , x) :: (FrexMonoid a s).Sem (reify a s is) env
                  ...(( a.validate RgtNeutrality [_] , s.equivalence.reflexive _)
                     :: multUnitNeutral a s _)
  <~ (i, x) :: is ...(((cast a).equivalence.reflexive _
                      ,s.equivalence.reflexive _
                      ) :: normalForm a s is)

public export
staIsHomo : (a : Monoid) -> (s : Setoid) -> Homomorphism a.Algebra (FrexStructure a s) (a.sta)
staIsHomo a s (MkOp Neutral) []    = (FrexSetoid a s).equivalence.reflexive _
staIsHomo a s (MkOp Product) [i,j] = (FrexSetoid a s).equivalence.reflexive _

public export
staHomo : (a : Monoid) -> (s : Setoid) -> (a ~> FrexMonoid a s)
staHomo a s = MkSetoidHomomorphism
  { H = MkSetoidHomomorphism
    { H           = a.sta
    , homomorphic = \i,j,prf => Ultimate prf
    }
  , preserves = staIsHomo a s
  }

public export
dynHomo : (a : Monoid) -> (s : Setoid) -> (s ~> FrexSetoid a s)
dynHomo a s = MkSetoidHomomorphism
  { H = a.dyn
  , homomorphic = \x,y,prf => (a.equivalence.reflexive _ , prf)
                              :: (FrexSetoid a s).equivalence.reflexive _
  }


public export
Extension : (a : Monoid) -> (s : Setoid) -> Extension a s
Extension a s = MkExtension
  { Model = FrexMonoid a s
  , Embed = staHomo a s
  , Var   = dynHomo a s
  }

public export
ExtenderFunction : (a : Monoid) -> (s : Setoid) -> Frex.ExtenderFunction (Extension a s)
ExtenderFunction a s other (Ultimate i    ) = other.Embed.H.H i
ExtenderFunction a s other (ConsUlt i x is) =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
  in other.Embed.H.H i .*.
     other.Var.H     x .*.
     ExtenderFunction a s other is

public export
ExtenderPreservesMult : (a : Monoid) -> (s : Setoid) ->
  (other : Extension a s) ->
  (i : U a) -> (is : FrexCarrier a s) ->
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
      %hint
      notation' : MAction1 (U a) (FrexCarrier a s)
      notation' = cast $ MonAction a s
  in other.Model.rel
    (ExtenderFunction a s other (i *. is))
    (other.Embed.H.H i .*. ExtenderFunction a s other is)
ExtenderPreservesMult a s other i (Ultimate j) =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
      %hint
      notation' : MAction1 (U a) (FrexCarrier a s)
      notation' = cast $ MonAction a s
      %hint
      notation'' : Multiplicative1 (U a)
      notation'' = a.Multiplicative1
  in CalcWith @{cast other.Model} $
  |~ other.Embed.H.H (i .*. j)
  <~ other.Embed.H.H i .*. other.Embed.H.H j
    ...(other.Embed.preserves Prod [i, j])

ExtenderPreservesMult a s other i (ConsUlt j y js) =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
      %hint
      notation' : MAction1 (U a) (FrexCarrier a s)
      notation' = cast $ MonAction a s
      %hint
      notation'' : Multiplicative1 (U a)
      notation'' = a.Multiplicative1
      h : U (FrexMonoid a s) -> U other.Model
      h = ExtenderFunction a s other
  in CalcWith @{cast other.Model} $
  |~ h ((i .*. j , y) :: js)
  ~~ other.Embed.H.H (i .*. j) .*. other.Var.H y .*. h js
          ...(Refl)
  <~ other.Embed.H.H i .*. other.Embed.H.H j .*. other.Var.H y .*. h js
          ...(other.Model.cong 1 (Dyn 0 .*. Sta (other.Var.H y) .*. Sta (h js)) [_] [_]
             [other.Embed.preserves Prod [i,j]])
  <~ (other.Embed.H.H i .*. other.Embed.H.H j) .*. (other.Var.H y .*. h js)
          ...(other.Model.equivalence.symmetric _ _ $
              other.Model.validate Associativity [_,_,_])
  <~ other.Embed.H.H i .*. (other.Embed.H.H j .*. (other.Var.H y .*. h js))
          ...(other.Model.equivalence.symmetric _ _ $
              other.Model.validate Associativity [_,_,_])
  <~ other.Embed.H.H i .*. (other.Embed.H.H j .*. other.Var.H y .*. h js)
          ...(other.Model.cong 1 (Sta (other.Embed.H.H i) .*. Dyn 0) [_] [_]
              [other.Model.validate Associativity [_,_,_]])
  ~~ other.Embed.H.H i .*. h ((j , y) :: js) ...(Refl)

-- Need to do this as a separate function so that the termination
-- checker can easily see the arguments decreasing.
public export
ExtenderPreservesProd : (a : Monoid) -> (s : Setoid) ->
  (other : Extension a s) ->
  (is,js : FrexCarrier a s) ->
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
      %hint
      notation' : MAction1 (U a) (FrexCarrier a s)
      notation' = cast $ MonAction a s
      %hint
      notation'' : Multiplicative1 (U a)
      notation'' = a.Multiplicative1
      h : U (FrexMonoid a s) -> U other.Model
      h = ExtenderFunction a s other
  in other.Model.rel
    (h (is .*. js) )
    (h is .*. h js)
ExtenderPreservesProd a s other (Ultimate i) js =
  ExtenderPreservesMult a s other i js
ExtenderPreservesProd a s other (ConsUlt i x is) js =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
      %hint
      notation' : MAction1 (U a) (FrexCarrier a s)
      notation' = cast $ MonAction a s
      %hint
      notation'' : Multiplicative1 (U a)
      notation'' = a.Multiplicative1
      h : U (FrexMonoid a s) -> U other.Model
      h = ExtenderFunction a s other
  in CalcWith @{cast other.Model} $
  |~ h ((i, x) :: is .*. js)
  ~~ other.Embed.H.H i .*. other.Var.H x .*. h(is .*. js) ...(Refl)
  <~ other.Embed.H.H i .*. other.Var.H x .*.(h is .*. h js)
    ...(other.Model.cong 1 (Sta (other.Embed.H.H i .*. other.Var.H x) .*. Dyn 0) [_] [_]
        [ExtenderPreservesProd a s other is js])
  <~ (other.Embed.H.H i .*. other.Var.H x .*. h is) .*. h js
    ...(other.Model.validate Associativity [_,_,_])
  ~~ h ((i, x) :: is) .*. h js ...(Refl)


public export
ExtenderIsHomomorphism : (a : Monoid) -> (s : Setoid) ->
  ExtenderIsHomomorphism (Extension a s) (ExtenderFunction a s)
ExtenderIsHomomorphism a s other (MkOp Neutral) []      =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
      %hint
      notation' : MAction1 (U a) (FrexCarrier a s)
      notation' = cast $ MonAction a s
      %hint
      notation'' : Multiplicative1 (U a)
      notation'' = a.Multiplicative1
  in CalcWith @{cast other.Model} $
  |~ other.Embed.H.H I1
  <~ I1 ...(other.Embed.preserves Unit []
  )

ExtenderIsHomomorphism a s other (MkOp Product) [is,js] =
  ExtenderPreservesProd a s other is js

public export
ExtenderIsSetoidHomomorphism : (a : Monoid) -> (s : Setoid) -> (other : Extension a s) ->
  (is,js : FrexCarrier a s) ->
  (prf : (FrexMonoid a s).rel is js) ->
  other.Model.rel
    (ExtenderFunction a s other is)
    (ExtenderFunction a s other js)
ExtenderIsSetoidHomomorphism a s other (Ultimate i) (Ultimate j)
  (Ultimate i_eq_j) = other.Embed.H.homomorphic i j i_eq_j
ExtenderIsSetoidHomomorphism a s other (ConsUlt i x is) (ConsUlt j y js)
  (ConsUlt i_eq_j x_eq_y is_eq_js) =
  other.Model.cong 3 (Dyn 0 .*. Dyn 1 .*. Dyn 2) [_,_,_] [_,_,_]
    [ other.Embed.H.homomorphic              i  j   i_eq_j
    , other.Var.homomorphic                  x  y   x_eq_y
    , ExtenderIsSetoidHomomorphism a s other is js is_eq_js
    ]

public export
ExtenderHomomorphism : (a : Monoid) -> (s : Setoid) -> Frex.Frex.ExtenderHomomorphism (Extension a s)
ExtenderHomomorphism a s other = MkSetoidHomomorphism
  { H = MkSetoidHomomorphism
      { H = ExtenderFunction a s other
      , homomorphic = ExtenderIsSetoidHomomorphism a s other
      }
  , preserves = ExtenderIsHomomorphism a s other
  }

public export
ExtenderPreservesEmbedding : (a : Monoid) -> (s : Setoid) ->
  ExtenderPreservesEmbedding (Extension a s) (ExtenderHomomorphism a s)
ExtenderPreservesEmbedding a s other i = other.Model.equivalence.reflexive _

public export
ExtenderPreservesVars : (a : Monoid) -> (s : Setoid) ->
  ExtenderPreservesVars (Extension a s) (ExtenderHomomorphism a s)
ExtenderPreservesVars a s other x =
  let %hint
      notation : Multiplicative1 (U other.Model)
      notation = other.Model.Multiplicative1
      %hint
      notation' : MAction1 (U a) (FrexCarrier a s)
      notation' = cast $ MonAction a s
      %hint
      notation'' : Multiplicative1 (U a)
      notation'' = a.Multiplicative1
      frex : Extension a s
      frex = Extension a s
      h : FrexMonoid a s ~> other.Model
      h = ExtenderHomomorphism a s other
  in CalcWith @{cast other.Model} $
  |~ h.H.H (frex.Var.H x)
  ~~ h.H.H ((I1, x) :: a.sta I1) ...(Refl)
  ~~ other.Embed.H.H I1 .*. other.Var.H x .*. other.Embed.H.H I1 ...(Refl)
  <~ I1 .*. other.Var.H x .*. I1 ...(other.Model.cong 1
         (Dyn 0 .*. Sta (other.Var.H x) .*. Dyn 0) [_] [_]
         [other.Embed.preserves Unit []])
  <~ I1 .*. other.Var.H x ...(other.Model.validate RgtNeutrality [_])
  <~        other.Var.H x ...(other.Model.validate LftNeutrality [_])

public export
Extender : (a : Monoid) -> (s : Setoid) -> Extender (Extension a s)
Extender a s other = MkExtensionMorphism
  { H             = ExtenderHomomorphism       a s other
  , PreserveEmbed = ExtenderPreservesEmbedding a s other
  , PreserveVar   = ExtenderPreservesVars      a s other
  }

public export
Uniqueness : (a : Monoid) -> (s : Setoid) -> Uniqueness (Extension a s)
Uniqueness a s other extend1 extend2 is =
  let frex : Extension a s
      frex = Extension a s
      lemma1 : (extend : frex ~> other) -> (is : U frex.Model) ->
        other.Model.rel
          (extend.H.H.H is)
          (other.Model.Sem (reify a s is) (extend.H.H.H . (either a.sta a.dyn)))
      lemma1 extend is = CalcWith @{cast other.Model} $
        |~ extend.H.H.H is
        <~ extend.H.H.H (frex.Sem (reify a s is) (either a.sta a.dyn))
             ...( other.Model.equivalence.symmetric _ _
                $ extend.H.H.homomorphic _ _
                $ normalForm a s is)
        <~ other.Model.Sem (reify a s is) (extend.H.H.H . (either a.sta a.dyn))
             ...(homoPreservesSem extend.H _ _)
      lemma2 : ((cast a `Either` s) ~~> cast other.Model).equivalence.relation
                  (extend1.H.H . (either frex.Embed.H frex.Var))
                  (extend2.H.H . (either frex.Embed.H frex.Var))
      lemma2 (Left  i) = CalcWith @{cast other.Model} $
        |~ extend1.H.H.H (either frex.Embed.H.H frex.Var.H (Left i))
        ~~ extend1.H.H.H (frex.Embed.H.H i)  ...(Refl)
        <~ other.Embed.H.H i                 ...(extend1.PreserveEmbed i)
        <~ extend2.H.H.H (frex.Embed.H.H i)  ...(other.Model.equivalence.symmetric _ _ $
                                                 extend2.PreserveEmbed i)
        ~~ extend2.H.H.H (either frex.Embed.H.H frex.Var.H (Left i))
                                             ...(Refl)
      lemma2 (Right x) = CalcWith @{cast other.Model} $
        |~ extend1.H.H.H (either frex.Embed.H.H frex.Var.H (Right x))
        ~~ extend1.H.H.H (frex.Var.H x) ...(Refl)
        <~ other.Var.H x                ...(extend1.PreserveVar x)
        <~ extend2.H.H.H (frex.Var.H x) ...(other.Model.equivalence.symmetric _ _ $
                                            extend2.PreserveVar x)
        ~~ extend2.H.H.H (either frex.Embed.H.H frex.Var.H (Right x))
                                        ...(Refl)
  in CalcWith @{cast other.Model} $
  |~ extend1.H.H.H is
  <~ other.Model.Sem (reify a s is) (extend1.H.H.H . (either a.sta a.dyn))
       ...(lemma1 extend1 is)
  <~ other.Model.Sem (reify a s is) (extend2.H.H.H . (either a.sta a.dyn))
       ...((eval (reify a s is)).homomorphic
             (extend1.H.H . (either frex.Embed.H frex.Var))
             (extend2.H.H . (either frex.Embed.H frex.Var))
             $ lemma2)
  <~ extend2.H.H.H is ...(other.Model.equivalence.symmetric _ _ $ lemma1 extend2 is)

public export
MonoidFrex : (a : Monoid) -> (s : Setoid) -> Frex a s
MonoidFrex a s = MkFrex
  { Data = Extension a s
  , UP   = IsUniversal
     { Exists = Extender a s
     , Unique = Uniqueness a s
     }
  }

public export
MonoidFrexlet : Frexlet {pres = MonoidTheory}
MonoidFrexlet a {n} = MonoidFrex a (cast $ Fin n)
