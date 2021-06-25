||| The free extension of a monoid a by a setoid x
module Frexlet.Monoid.Frex

import public Frexlet.Monoid.Frex.Structure
import public Frexlet.Monoid.Frex.Properties
import public Frexlet.Monoid.Frex.Construction


myProof : (|-) {pres = MonoidTheory} (QuotientData MonoidTheory (irrelevantCast a)) ?c ?d
myProof = ?goal
