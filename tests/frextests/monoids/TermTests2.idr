module TermTests2

import Data.Unit

import Frex
import Frex.Free.Construction
import Frex.Free.Construction.Combinators

import Frexlet.Monoid
import Frexlet.Monoid.Free
import Frexlet.Monoid.Notation.Additive

import Syntax.PreorderReasoning

var : {n : Nat} -> Fin n -> U (Construction.Free MonoidTheory $ cast $ Fin n).Data.Model
var = (Construction.Free MonoidTheory $ cast $ Fin n).Data.Env.H

infix 0 ~~
0 (~~) : Rel (U (Construction.Free MonoidTheory $ cast $ Fin n).Data.Model)
(~~) = (Free MonoidTheory $ cast $ Fin n).Data.Model.rel

%hint
notation: {n : Nat} -> Additive1 (U (Construction.Free MonoidTheory $ cast $ Fin n).Data.Model)
notation = (Construction.Free MonoidTheory $ cast $ Fin n).Data.Model.Additive1

trivial : (var {n = 1} 0) ~~ var 0
trivial = prove (FreeMonoidOver $ cast $ Fin _)
               (Done 0 =-= Done 0)
trivial2 : var {n = 2} 0 .+. var 1 ~~ var 0 .+. var 1
trivial2 = prove (FreeMonoidOver $ cast $ Fin _)
         (Done 0 .+. Done 1 =-= Done 0 .+. Done 1)
assoc :
   (var {n = 3} 0 .+. (var 1 .+. var 2)) ~~ (var 0 .+. var 1) .+. var 2
assoc = prove (FreeMonoidOver $ cast $ Fin _) $
         Done 0 .+. (Done 1 .+. Done 2)
    =-= (Done 0 .+. Done 1) .+. Done 2

rassoc :
  let a := var {n = 3} 0
      b := var {n = 3} 1
      c := var {n = 3} 2
  in (a .+. b) .+. c ~~ a .+. (b .+. c)
rassoc = prove (FreeMonoidOver $ cast $ Fin _)
       $ (Done 0 .+. Done 1) .+. Done 2
       =-= Done 0 .+. (Done 1 .+. Done 2)
units :
  (O1 .+. (var {n = 1} 0 .+. O1)) .+. O1 ~~ var 0
units = prove (FreeMonoidOver $ cast $ Fin _)
      $ (O1 .+. (Done 0 .+. O1)) .+. O1 =-= Done 0
