module Data.Category.Setoid

import Data.Category.Core
import Data.Category.Construction.Pair
import Data.Category.Construction.Op

import Data.Setoid.Fun

public export
Setoid : Category
Setoid =
  let homo : {a,b,c : Setoid} ->
        SetoidHomomorphism ((b ~~> c) `Pair` (a ~~> b)) (a ~~> c) (uncurry (.))
      homo (f1,g1) (f2,g2) prf x = CalcWith c $
        |~ f1.H (g1.H x)
        ~~ f1.H (g2.H x) ...(f1.homomorphic _ _ $
                             prf.snd _)
        ~~ f2.H (g2.H x) ...(prf.fst _)
  in MkCategory
  { Obj = Setoid
  , structure = MkStructure
    { Arr = (~~>)
    , idArr = id _
    , compArr =
      MkSetoidHomomorphism
      { H = uncurry (.)
      , homomorphic = homo
      }
    }
  , laws = Check
    { idLftNeutral = \(MkHom f) => MkHomEq $ (Setoid.Definition.(~~>) _ _).equivalence.reflexive _
    , idRgtNeutral = \(MkHom f) => MkHomEq $ (Setoid.Definition.(~~>) _ _).equivalence.reflexive _
    , associativity = \(MkHom f),(MkHom g),(MkHom h) =>
        MkHomEq $ \x => _.equivalence.reflexive
                $ (f.H $ g.H $ h.H x)
    }
  }

public export
homAction : {cat : Category} -> {a,a',b,b' : cat.Obj} ->
  (((cat.HomSet a' a) `Pair` (cat.HomSet b b')) `Pair` (cat.HomSet a b)) ~>
  (cat.HomSet a' b')
homAction = MkSetoidHomomorphism
  { H = \gfu => snd (fst gfu) . snd gfu . fst (fst gfu)
  , homomorphic = \ ((g1,f1),u1), ((g2, f2), u2), prf =>
      CalcWith (cat.HomSet _ _) $
      |~ f1 . u1 . g1
      ~~ f2 . u2 . g2 ...((prf.fst.snd) .:. ((prf.snd) .:. (prf.fst.fst)))
  }

public export
Hom : {c : Category} -> (c.op `Pair` c) ~> Setoid
Hom =
  MkFunctor
  { structure = MkStructure
    { mapObj = \ab =>  c.HomSet (fst ab) (snd ab)
    , mapHom =
      let u : {a,a',b,b' : c.Obj} ->
              ((c.HomSet a' a) `Pair` (c.HomSet b b')) ~>
              ((c.HomSet a b) ~~> (c.HomSet a' b'))
          u = ((mate {a = (c.HomSet _ _) `Pair` (c.HomSet _ _)
             , b = c.HomSet _ _
             , c = c.HomSet _ _}).Fwd.H (homAction {cat = c}))
      in MkSetoidHomomorphism
        { H = \ (MkHom (MkHom f, MkHom g)) => MkHom $ MkSetoidHomomorphism
                 { H = \(MkHom q) => MkHom $ (u.H (?h199, ?h200)).H (MkHom q)
                 , homomorphic = ?h11
                 }
        , homomorphic = ?h1
        }
    }
  , functoriality = Check
    { id = ?h3
    , comp = ?h4
    }
  }
