||| Cartesian closed structure of setoids
module Data.Setoid.Fun

import Data.Setoid
import Data.Setoid.Pair

public export
mateFunc : {a,b,c : Setoid} -> (a `Pair` b) ~> c -> a ~> (b ~~> c)
mateFunc f = MkSetoidHomomorphism
  { H = \x => MkSetoidHomomorphism
        { H = curry f.H x
        , homomorphic = \y1,y2,prf => f.homomorphic (_,_) (_,_)
                        $ MkAnd (a.equivalence.reflexive _) prf
        }
  , homomorphic = \x1,x2,prf,y => f.homomorphic (_,_) (_,_)
                        $ MkAnd prf (b.equivalence.reflexive _)
  }

public export
mateHomo : {a,b,c : Setoid} -> ((a `Pair` b) ~~> c) ~> (a ~~> (b ~~> c))
mateHomo = MkSetoidHomomorphism
  { H = mateFunc
  , homomorphic = \f,g,prf,x,y => prf _
  }

public export
mateInverseFunc : {a,b,c : Setoid} -> a ~> (b ~~> c) -> (a `Pair` b) ~> c
mateInverseFunc f = MkSetoidHomomorphism
  { H = \(x,y) => (f.H x).H y
  , homomorphic = \(x1,y1),(x2,y2),prf => CalcWith c $
      |~ (f.H x1).H y1
      ~~ (f.H x1).H y2 ...((f.H _).homomorphic _ _ prf.snd)
      ~~ (f.H x2).H y2 ...(f.homomorphic _ _ prf.fst y2)
  }

public export
mateInverseHomo : {a,b,c : Setoid} -> (a ~~> (b ~~> c)) ~> ((a `Pair` b) ~~> c)
mateInverseHomo = MkSetoidHomomorphism
  { H = mateInverseFunc
  , homomorphic = \f,g,prf,(x,y) => prf x y
  }

public export
mate : {a,b,c : Setoid} -> ((a `Pair` b) ~~> c) <~> (a ~~> (b ~~> c))
mate = MkIsomorphism
  { Fwd = mateHomo
  , Bwd = mateInverseHomo
  , Iso = IsIsomorphism
     { BwdFwdId = \f,(x,y) => c.equivalence.reflexive _
     , FwdBwdId = \f, x,y  => c.equivalence.reflexive _
     }
  }
