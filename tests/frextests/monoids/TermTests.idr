module TermTests

import Frex
import Frex.Free.Construction.Combinators

import Frexlet.Monoid
import Frexlet.Monoid.Free
import Frexlet.Monoid.Notation.Additive

%hint
notationAdd2 : Additive2 (Term Signature a)
notationAdd2= MkAdditive2
              (call {sig = Signature} Neutral)
              (call {sig = Signature} Product)


infix 0 ~~
(~~) : {x : Type} -> (lhs, rhs : Term Signature x) -> Type
(~~) = (|-) {pres = MonoidTheory} (QuotientData MonoidTheory (cast x))

trivial : {x : Type} -> {a : Term Signature x} -> a ~~ a
trivial = solve 1 (MonoidFrex (Syntactic x) _) (Dyn 0 =-= Dyn 0)

trivial2 : {x : Type} -> {a, b : Term Signature x} ->
           a :+: b ~~ a :+: b
trivial2 = solve 2 (MonoidFrex (Syntactic x) _)
         $ Dyn 0 .+. Dyn 1 =-= Dyn 0 .+. Dyn 1

assoc : {x : Type} -> {a, b, c : Term Signature x} ->
        a :+: (b :+: c) ~~ (a :+: b) :+: c
assoc = solve 3 (MonoidFrex (Syntactic _) _)
      $ Dyn 0 .+. (Dyn 1 .+. Dyn 2) =-= (Dyn 0 .+. Dyn 1) .+. Dyn 2

rassoc : {x : Type} -> {a, b, c : Term Signature x} ->
         (a :+: b) :+: c ~~ a :+: (b :+: c)
rassoc = solve 3 (MonoidFrex (Syntactic _) _)
       $ (Dyn 0 .+. Dyn 1) .+. Dyn 2 =-= Dyn 0 .+. (Dyn 1 .+. Dyn 2)

units : {x : Type} -> {a : Term Signature x} ->
        (O2 :+: (a :+: O2)) :+: O2 ~~ a
units = solve 1 (MonoidFrex (Syntactic _) _)
        -- wtf
        {prf = ConsUlt (byAxiom MonoidTheory LftNeutrality) Refl
             $ Ultimate
             $ Sym $ Transitive (Sym $ byAxiom MonoidTheory LftNeutrality)
             $ Sym $ byAxiom MonoidTheory RgtNeutrality
        }
      $ (O1 .+. (Dyn 0 .+. O1)) .+. O1 =-= Dyn 0
