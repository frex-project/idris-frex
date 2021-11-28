||| The product of two categories
module Data.Category.Construction.Pair

import Data.Category.Core

parameters (Cat1, Cat2 : Category)
  public export
  Pair : Category
  Pair = MkCategory
    { Obj       = (Cat1 .Obj, Cat2 .Obj)
    , structure = MkStructure
        { Arr = \a,b => (Cat1 .structure.Arr (fst a) (fst b)) `Pair` (Cat2 .structure.Arr (snd a) (snd b))
        , idArr = (U Id, U Id)
        , compArr = MkSetoidHomomorphism
            { H = \ uv => ( U $ (MkHom $ fst $ fst uv) . (MkHom $ fst $ snd uv)
                          , U $ (MkHom $ snd $ fst uv) . (MkHom $ snd $ snd uv))
            , homomorphic =
                -- Not sure why type-checking this takes so long
                \((u11, u12),(v11, v12)),((u21, u22),(v21, v22)),prf =>
                MkAnd
                (Cat1 .structure.compArr.homomorphic (_,_) (_,_)
                $ MkAnd prf.fst.fst prf.snd.fst)
                (Cat2 .structure.compArr.homomorphic (_,_) (_,_)
                $ MkAnd prf.fst.snd prf.snd.snd)
            }
        }
    , laws = Check
        { idLftNeutral = \f => MkHomEq $ MkAnd
            (Cat1 .laws.idLftNeutral $ MkHom $ fst $ U f).runEq
            (Cat2 .laws.idLftNeutral $ MkHom $ snd $ U f).runEq
        , idRgtNeutral = \f => MkHomEq $ MkAnd
            (Cat1 .laws.idRgtNeutral $ MkHom $ fst $ U f).runEq
            (Cat2 .laws.idRgtNeutral $ MkHom $ snd $ U f).runEq
        , associativity = \f,g,h => MkHomEq $ MkAnd
            (Cat1 .laws.associativity (MkHom $ fst $ U f)
                                      (MkHom $ fst $ U g)
                                      (MkHom $ fst $ U h)).runEq
            (Cat2 .laws.associativity (MkHom $ snd $ U f)
                                      (MkHom $ snd $ U g)
                                      (MkHom $ snd $ U h)).runEq
        }
    }

  -- and one can construct the other structure: projection functors,
  -- tupling functor etc. We'll define this one (even if it's not the
  -- most economical way to go about it)

public export
pair : {c1, c2, d1, d2 : Category} -> (f : c1 ~> c2) -> (g : d1 ~> d2) ->
  (c1 `Pair` d1) ~> (c2 `Pair` d2)
pair f1 f2 = MkFunctor
  { structure = MkStructure           -- build eta into the def
      { mapObj = \uv => bimap (f1 !!) (f2 !!) (fst uv, snd uv)
      , mapHom = MkHomHomo {c = c2 `Pair` d2}
               . (bimap (UHomo  . f1.mapSetoid . MkHomHomo)
                        (UHomo  . f2.mapSetoid . MkHomHomo))
               . (UHomo {c = c1 `Pair` d1})
      }
  , functoriality = Check
      { id = \ab => MkHomEq $ MkAnd (f1.functoriality.id $ fst ab).runEq
                                    (f2.functoriality.id $ snd ab).runEq
      , comp = \uv1,uv2 => MkHomEq $ MkAnd
          (f1.functoriality.comp (MkHom $ fst $ U uv1) (MkHom $ fst $ U uv2)).runEq
          (f2.functoriality.comp (MkHom $ snd $ U uv1) (MkHom $ snd $ U uv2)).runEq
      }
  }
