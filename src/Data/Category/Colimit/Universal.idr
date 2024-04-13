module Data.Category.Colimit.Universal

import Data.Category
import public Data.Category.Colimit.Initial

%default total

namespace Structure
  public export
  record Arrow {C, D : Category} (X : D .Obj) (F : C ~> D) where
    constructor MkArrow
    Cod : C .Obj
    Arr : D .Hom X (F !! Cod)

  public export
  record (~>) {C, D : Category} {X : D .Obj} {F : C ~> D}
    (u,v : X `Arrow` F)
    where
    constructor MkHomo
    H : C .Hom u.Cod v.Cod
    preserves : (D .HomSet X (F !! v.Cod)).equivalence.relation
      (F .map H . u.Arr)
      (v.Arr)

namespace Setoid
  public export
  (~~>) : {C, D : Category} -> {X : D .Obj} -> {F : C ~> D} ->
    (u,v : X `Arrow` F) -> Setoid
  u ~~> v = MkSetoid
    { U = u ~> v
    , equivalence = MkEquivalence
        { relation = \f,g =>
            (C .HomSet u.Cod v.Cod).equivalence.relation f.H g.H
        , reflexive  = \f     => (C .HomSet _ _).equivalence.reflexive _
        , symmetric  = \f,g   => (C .HomSet _ _).equivalence.symmetric _ _
        , transitive = \f,g,h => (C .HomSet _ _).equivalence.transitive _ _ _
        }
    }

public export
(~~>) : {c,d : Category} -> (x : d.Obj) -> (f : c ~> d) -> Category
x ~~> f = MkCategory
  { Obj = x `Arrow` f
  , structure = MkStructure
      { Arr = \u,v => u ~~> v
      , idArr = MkHomo
          { H = Id
          , preserves = CalcWith (d.HomSet x (f !! _.Cod)) $
            |~ (f.map Id . _.Arr)
            ~~ (      Id . _.Arr) ...(f.functoriality.id _ . _.Arr)
            ~~             _.Arr  ...(d.laws.idLftNeutral _)
          }
      , compArr = MkSetoidHomomorphism
          { H = \pq => MkHomo
              { H = (fst pq).H . (snd pq).H
              {-       Arr1
                      -----------> Cod1
                     / f.map q.H /   |
                    / (pres.1)  v    |
                   x------> Cod2  =  | f.map (p.H . q.H)
                    \  f.map p.H\    |
                     \ (pres.2)  --v v
                      -----------> Cod3
              -}
              , preserves =
                let p : ?
                    p = fst pq
                    q : ?
                    q = snd pq
                in CalcWith (d.HomSet _ _) $
                |~ (f.map (p.H . q.H) . _.Arr)
                ~~ ((f.map p.H) . (f.map q.H)) . _.Arr
                                         ...(f.functoriality.comp _ _ . _.Arr)
                ~~ (f.map p.H)  . ((f.map q.H) . _.Arr)
                                         ..<(d.laws.associativity _ _ _)
                ~~  f.map p.H . _.Arr
                                         ...(f.map p.H . q.preserves)
                ~~ _.Arr
                                         ...(            p.preserves)
              }
          , homomorphic = \pq1, pq2, prf =>
              c.cong ((fst pq1).H, (snd pq1).H)
                     ((fst pq2).H, (snd pq2).H)
                     (MkAnd prf.fst prf.snd)
          }
      }
  , laws = Check
      { idRgtNeutral  = \p     => MkHomEq $ c.laws.idRgtNeutral _
      , idLftNeutral  = \p     => MkHomEq $ c.laws.idLftNeutral _
      , associativity = \p,q,r => MkHomEq $ c.laws.associativity _ _ _
      }
  }

public export
Universal : {c,d : Category} -> (x : d.Obj) -> (f : c ~> d) -> Type
Universal x f = Initial (x ~~> f)
