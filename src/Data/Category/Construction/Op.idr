module Data.Category.Construction.Op

import Data.Category.Core

public export
(.op) : Category -> Category
cat.op =
  let Arr' : cat.Obj -> cat.Obj -> Setoid
      Arr' a b = cat.HomSet b a
      compose : {a,b,c : cat.Obj} -> (U $ Arr' b c, U $ Arr' a b) -> U $ Arr' a c
      compose (f,g) = g . f
  in MkCategory
  { Obj = cat.Obj
  , structure = MkStructure
    { Arr = Arr'
    , idArr = Id
    , compArr = MkSetoidHomomorphism
        { H = compose
        , homomorphic = \(f1,g1),(f2,g2),prf =>
            cat.cong (_,_) (_,_) (MkAnd prf.snd prf.fst)
        }
    }
  , laws = Check
    { idLftNeutral = \f => MkHomEq $ cat.laws.idRgtNeutral _
    , idRgtNeutral = \f => MkHomEq $ cat.laws.idLftNeutral _
    , associativity = \f,g,h => MkHomEq $
         (cat.HomSet _ _).equivalence.symmetric _ _ $
         cat.laws.associativity (U h) (U g) (U f)
    }
  }
