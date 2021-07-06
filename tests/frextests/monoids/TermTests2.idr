module TermTests2

import Data.Unit

import Frex
import Frex.Free.Construction
import Frex.Free.Construction.Combinators

import Frexlet.Monoid
import Frexlet.Monoid.Free
import Frexlet.Monoid.Notation.Additive

var : {n : Nat} -> Fin n -> U (FreeMonoid n)
var = (FreeFrex n).Data.Var.H

infix 0 ~~
0 (~~) : Rel (U (SyntacticMonoid n))
(~~) = (SyntacticMonoid n).rel

%hint
notation: Additive1 (U (SyntacticMonoid 10))
notation = (SyntacticMonoid 10).Additive1

trivial :
  let x := (SyntacticExtension 10).Embed.H.H (var 0)
  in x ~~ x
trivial = prove 0 (MonoidFrex (FreeMonoid 10) _)
            (Sta (var 0) =-= Sta (var 0))

trivial2 :
  let a := (SyntacticExtension 10).Embed.H.H (var 0)
      b := (SyntacticExtension 10).Embed.H.H (var 1)
  in a .+. b ~~ a .+. b
trivial2 = prove 0 (MonoidFrex (FreeMonoid 10) _)
         $ Sta (var 0) .+. Sta (var 1) =-= Sta (var 0) .+. Sta (var 1)

assoc :
  let a := (SyntacticExtension 10).Embed.H.H (var 0)
      b := (SyntacticExtension 10).Embed.H.H (var 1)
      c := (SyntacticExtension 10).Embed.H.H (var 2)
  in a .+. (b .+. c) ~~ (a .+. b) .+. c
assoc = prove 0 (MonoidFrex (FreeMonoid 10) _)
      $ Sta (var 0) .+. (Sta (var 1) .+. Sta (var 2))
       =-= (Sta (var 0) .+. Sta (var 1)) .+. Sta (var 2)

rassoc :
  let a := (SyntacticExtension 10).Embed.H.H (var 0)
      b := (SyntacticExtension 10).Embed.H.H (var 1)
      c := (SyntacticExtension 10).Embed.H.H (var 2)
  in (a .+. b) .+. c ~~ a .+. (b .+. c)
rassoc = prove 0 (MonoidFrex (FreeMonoid 10) _)
       $ (Sta (var 0) .+. Sta (var 1)) .+. Sta (var 2)
       =-= Sta (var 0) .+. (Sta (var 1) .+. Sta (var 2))

units :
  let a := (SyntacticExtension 10).Embed.H.H (var 0)
  in (O1 .+. (a .+. O1)) .+. O1 ~~ a
units = prove 0 (MonoidFrex (FreeMonoid 10) _)
      $ (O1 .+. (Sta (var 0) .+. O1)) .+. O1 =-= Sta (var 0)
