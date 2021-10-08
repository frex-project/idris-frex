module Data.Category.Construction.Op

import Data.Category.Core

public export
(.op) : Category -> Category
cat.op = MkCategory
  { Obj = cat.Obj
  , structure = MkStructure
    { Arr = \a, b => cat.structure.Arr b a
    , idArr = U Id
    , compArr = MkSetoidHomomorphism
        { H = \fg => cat.structure.compArr.H (snd fg, fst fg)
        , homomorphic = \(f1,g1),(f2,g2),prf =>
            cat.structure.compArr.homomorphic _ _ (MkAnd prf.snd prf.fst)
        }
    }
  , laws = Check
    { idLftNeutral = \f => MkHomEq $ (cat.laws.idRgtNeutral (MkHom $ U f)).runEq
    , idRgtNeutral = \f => MkHomEq $ (cat.laws.idLftNeutral (MkHom $ U f)).runEq
    , associativity = \f,g,h => MkHomEq $
         ((cat.HomSet _ _).equivalence.symmetric _ _ $
         (cat.laws.associativity (MkHom $ U h) (MkHom $ U g) (MkHom $ U f))).runEq
    }
  }
