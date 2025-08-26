module Data.Category.Setoid

import Data.Category.Core
import Data.Category.Construction.Pair
import Data.Category.Construction.Op

import Data.Setoid.Fun

public export
uncurry' : (a -> b -> c) -> (a, b) -> c
uncurry' f ab = f (fst ab) (snd ab)


public export
Setoid : Category
Setoid =
  let homo : {a,b,c : Setoid} ->
        SetoidHomomorphism ((b ~~> c) `Pair` (a ~~> b)) (a ~~> c) (uncurry' (.))
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
      { H = uncurry' (.)
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
  (((cat.structure.Arr a' a) `Pair` (cat.structure.Arr b b')) `Pair` (cat.structure.Arr a b)) ~>
  (cat.structure.Arr a' b')
homAction = MkSetoidHomomorphism
  { H = \gfu => U $ (MkHom $ snd (fst gfu)) . (MkHom $ snd gfu) . (MkHom $ fst (fst gfu))
  , homomorphic = \ ((g1,f1),u1), ((g2, f2), u2), prf =>
      (.runEq) $ CalcWith (cat.HomSet _ _) $
      |~ MkHom f1 . MkHom u1 . MkHom g1
      ~~ MkHom f2 . MkHom u2 . MkHom g2 ...(let q = MkHomEq { f = MkHom f1
                                                            , g = MkHom f2}
                                                            prf.fst.snd
                                                v = MkHomEq { f = MkHom u1
                                                            , g = MkHom u2}
                                                            prf.snd
                                                w = MkHomEq { f = MkHom g1
                                                            , g = MkHom g2}
                                                            prf.fst.fst
                                            in q .:. v .:. w)
  }

public export
Hom : {c : Category} -> (c.op `Pair` c) ~> Setoid
Hom =
  MkFunctor
  { structure = MkStructure
    { mapObj = \ab =>  c.HomSet (fst ab) (snd ab)
    , mapHom =
      let u : {a,a',b,b' : c.Obj} ->
              ((c.structure.Arr a' a) `Pair` (c.structure.Arr b b')) ~>
              ((c.structure.Arr a b) ~~> (c.structure.Arr a' b'))
          u = ((mate {a = (c.structure.Arr _ _) `Pair` (c.structure.Arr _ _)
             , b = c.structure.Arr _ _
             , c = c.structure.Arr _ _}).Fwd.H (homAction {cat = c}))
      in MkSetoidHomomorphism
        { H = \ fg => MkHom $ MkSetoidHomomorphism
                 { H = \q => MkHom $ (u.H (U fg)).H (U q)
                 , homomorphic = \u1,u2,prf => MkHomEq $
                   (u.H (U fg)).homomorphic (U u1) (U u2) prf.runEq
                 }
        , homomorphic = \fg1, fg2, prf  => MkHomEq $ \q => MkHomEq $
            u.homomorphic (U fg1) (U fg2) prf.runEq (U q)
        }
    }
  , functoriality = Check
    { id = \ab => MkHomEq $ \u =>
        CalcWith (c.HomSet _ _) $
        |~ Id . u . Id
        ~~ Id . u ...(Id . c.laws.idRgtNeutral _)
        ~~ u      ...(     c.laws.idLftNeutral _)
    , comp = \fg1, fg2 => MkHomEq $ \u =>
        -- This is ridiculous
        let f1 : ?
            f1 = MkHom $ fst $ U fg1
            f2 : ?
            f2 = MkHom $ fst $ U fg2
            g1 : ?
            g1 = MkHom $ snd $ U fg1
            g2 : ?
            g2 = MkHom $ snd $ U fg2
        in CalcWith (c.HomSet _ _) $
        |~ (g1 . g2) . u . (f2 . f1)
        ~~ g1 . (g2 . u . (f2 . f1))   ..<(c.laws.associativity g1 g2 (u . (f2 . f1)))
        ~~ g1 . (g2 . ((u . f2) . f1)) ...(g1 . (g2 . (c.laws.associativity u f2 f1)))
        ~~ g1 . (g2 . u . f2) . f1     ...(g1 . (c.laws.associativity g2 (u . f2) f1))
    }
  }
