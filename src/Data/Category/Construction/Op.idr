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

namespace Functor
  public export
  (.op) : {c,d : Category} -> (f : c ~> d) -> c.op ~> d.op
  f.op = MkFunctor
    { structure = MkStructure
        { mapObj = (f !!)
        , mapHom = MkSetoidHomomorphism
            { H = \u => MkHom (U $ f.map (MkHom (U u)))
            , homomorphic = \u,v,prf =>
                MkHomEq (f.mapSetoid.homomorphic (MkHom $ U u) (MkHom $ U v) $
                MkHomEq prf.runEq).runEq
            }
        }
    , functoriality = Check
        { id   = \a => MkHomEq (f.functoriality.id a).runEq
        , comp = \u,v =>
          MkHomEq (f.functoriality.comp (MkHom $ U v) (MkHom $ U u)).runEq
        }
    }

  public export
  (.opMap) : {c,d : Category} -> {f,g : c ~> d} ->
    (alpha : g ~> f) -> f.op ~> g.op
  alpha.opMap = MkNatTrans
    { transformation = \a => MkHom $ U $ alpha ^ a
    , naturality = \u =>
      let v : ?
          v = MkHom $ U u
      in MkHomEq
      (CalcWith (d.HomSet _ _) $
        |~ (f.map v) . (alpha ^ _)
        ~~ ((alpha ^ _) . (g.map v)) ..<(alpha.naturality $ MkHom $ U u)
      ).runEq
    }

  public export
  OpMapHomo : {c,d : Category} -> {f,g : c ~> d} ->
    SetoidHomomorphism (g ~~> f) (f.op ~~> g.op) ((.opMap) {f,g})
  OpMapHomo alpha beta prf a = MkHomEq (prf a).runEq

  public export
  opFunctor : {c,d : Category} -> (Functor c d).op ~> (Functor c.op d.op)
  opFunctor = MkFunctor
    { structure = MkStructure
        { mapObj = (.op)
        , mapHom =
            MkSetoidHomomorphism
            { H = \alpha => MkHom (U alpha).opMap
            , homomorphic = \alpha,beta,prf =>
                MkHomEq $ \a =>
                MkHomEq (OpMapHomo (U alpha) (U beta) (prf.runEq) a).runEq
            }
        }
    , functoriality = Check
        { id = \f => MkHomEq $ \a => (d.op.HomSet _ _).equivalence.reflexive _
        , comp = \alpha,beta => MkHomEq $ \a =>
                   (d.op.HomSet _ _).equivalence.reflexive _
        }
    }
