||| The product of two categories
module Data.Category.Construction.Pair

import Data.Category.Core

parameters (Cat1, Cat2 : Category)
  public export
  Pair : Category
  Pair = MkCategory
    { Obj       = (Cat1 .Obj, Cat2 .Obj)
    , structure = MkStructure
        { Arr = \a,b => (Cat1 .HomSet (fst a) (fst b)) `Pair` (Cat2 .HomSet (snd a) (snd b))
        , idArr = (Id, Id)
        , compArr = MkSetoidHomomorphism
            { H = \ uv => ( (fst $ fst uv) . (fst $ snd uv)
                          , (snd $ fst uv) . (snd $ snd uv))
            , homomorphic = \((u11, u12),(v11, v12)),((u21, u22),(v21, v22)),prf =>
                MkAnd
                (Cat1 .cong (_,_) (_,_) $ MkAnd prf.fst.fst prf.snd.fst)
                (Cat2 .cong (_,_) (_,_) $ MkAnd prf.fst.snd prf.snd.snd)
            }
        }
    , laws = Check
        { idLftNeutral = \f => MkHomEq $ MkAnd
            (Cat1 .laws.idLftNeutral _)
            (Cat2 .laws.idLftNeutral _)
        , idRgtNeutral = \f => MkHomEq $ MkAnd
            (Cat1 .laws.idRgtNeutral _)
            (Cat2 .laws.idRgtNeutral _)
        , associativity = \f,g,h => MkHomEq $ MkAnd
            (Cat1 .laws.associativity _ _ _)
            (Cat2 .laws.associativity _ _ _)
        }
    }

  -- and one can construct the other structure: projection functors,
  -- tupling functor etc.
