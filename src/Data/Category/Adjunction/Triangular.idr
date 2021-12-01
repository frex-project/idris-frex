module Data.Category.Adjunction.Triangular

import Data.Setoid
import Data.Setoid.Fun

import Data.Category.Core
import Data.Category.Construction.Pair
import Data.Category.Construction.Op
import Data.Category.Setoid

import Data.Category.Adjunction

{- It would be nice to base adjunctions on the naturality of the
   unit/counit as Carette and Hu do and triangular laws, but the laws
   must be phrased pointwise since our meta-theory doesn't normalise
   (strict) functor composition: functor composition laws such as the
   unit lft . Id = Id . lft = lft aren't true judgementally (due to
   the intensional proofs of functoriality) and so we need
   higher-dimensional gadgetry to compare them (or introduce transport
   into the definition)

   It's not super-painful, but it's not great either.
-}

public export
record AdjunctionStructure (C,D : Category) where
  constructor MkAdjunctionStructure
  lft : C ~> D
  rgt : D ~> C

  unit : Id ~> rgt . lft
  counit : lft . rgt ~> Id

-- We can phrase the triangle laws in the abstract, in any bicategory.
-- But that's painful, so we'll work with the concrete ones.
-- Here's why, for example, the left ones are equivalent.

public export 0
(.yankLawLftAbstract) : {c,d : Category} -> AdjunctionStructure c d -> Type
adjunct.yankLawLftAbstract = (adjunct.lft ~~> adjunct.lft).equivalence.relation
  ( let u : (Id . adjunct.lft) ~> adjunct.lft
        u = U $ (IdLft adjunct.lft).from
        v : (adjunct.lft . adjunct.rgt) . adjunct.lft ~> Id . adjunct.lft
        v = adjunct.counit * (Id {f = adjunct.lft})
        w :  adjunct.lft . adjunct.rgt  . adjunct.lft ~>
            (adjunct.lft . adjunct.rgt) . adjunct.lft
        w = U (Associativity adjunct.lft adjunct.rgt adjunct.lft).into
        q : (adjunct.lft . Id) ~> adjunct.lft . adjunct.rgt  . adjunct.lft
        q = (Id {f = adjunct.lft}) * adjunct.unit
        r : adjunct.lft ~> (adjunct.lft . Id)
        r = U $ (IdRgt adjunct.lft).into
  in u . v . w . q . r)
  Id


public export 0
(.yankLawLft) : {c,d : Category} -> AdjunctionStructure c d -> Type
adjunct.yankLawLft {c,d} = (a : c.Obj) ->
  (d.HomSet (adjunct.lft !! a) (adjunct.lft !! a)).equivalence.relation
    ((adjunct.counit ^ (adjunct.lft !! a)) . (adjunct.lft.map (adjunct.unit ^ a)))
    (Id)

public export 0
(.yankLawRgt) : {c,d : Category} -> AdjunctionStructure c d -> Type
adjunct.yankLawRgt {c,d} = (b : d.Obj) ->
  (c.HomSet (adjunct.rgt !! b) (adjunct.rgt !! b)).equivalence.relation
    ((adjunct.rgt.map $ adjunct.counit ^ b) . (adjunct.unit ^ (adjunct.rgt !! b)))
    (Id)

-- Mutual conversion, relies on reducing identities:
public export
lemma1 : {cat : Category} -> {a,b,c : cat.Obj} -> (u : cat.Hom b c) -> (v : cat.Hom a b) ->
  (cat.HomSet a c).equivalence.relation
    (Id . u . Id . v . Id)
    (u . v)
lemma1 u v = CalcWith (cat.HomSet a c) $
  |~ Id . u . Id . v . Id
  ~~ u . Id . v . Id ...(    cat.laws.idLftNeutral _)
  ~~ u . v . Id      ...(u . cat.laws.idLftNeutral (v . Id))
  ~~ u . v           ...(u . cat.laws.idRgtNeutral v)

public export
(.yankLawLftLemma) : {c,d : Category} ->
 (adjunct : AdjunctionStructure c d) -> (a : c.Obj) ->
   (d.HomSet (adjunct.lft !! a) (adjunct.lft !! a)).equivalence.relation
     (Id . ((adjunct.counit ^ (adjunct.lft !! a))
            . (adjunct.lft.map $ adjunct.rgt.map $ Id {a = adjunct.lft !! a}))
         . Id
         . (Id . (adjunct.lft.map (adjunct.unit ^ a)))
         . Id)
     ((adjunct.counit ^ (adjunct.lft !! a))
      . (adjunct.lft.map $ adjunct.unit ^ a))
adjunct.yankLawLftLemma a =
  let A : c.Obj
      A = a
      FA : d.Obj
      FA = adjunct.lft !! A
      C  : d ~> d
      C = adjunct.lft . adjunct.rgt
      phi : d.Hom (C !! FA) FA
      phi = ((adjunct.counit ^ FA)
                  . (C .map $ Id {a = FA}))
      psi : d.Hom FA (C !! FA)
      psi = Id . (adjunct.lft.map $ (adjunct.unit ^ a))
  in CalcWith (d.HomSet FA FA) $
  |~ _
  ~~ phi . psi ...(lemma1 phi psi)
  ~~ ((adjunct.counit ^ FA)
                  . Id)
     . (adjunct.lft.map $ (adjunct.unit ^ a))
      ...(((adjunct.counit ^ FA) . (C .functoriality.id _))
          .:. (d.laws.idLftNeutral _))
  ~~ _ ...((d.laws.idRgtNeutral _) . _)

public export
(.yankLawLftAbstractToConcrete) : {c,d : Category} ->
 (adjunct : AdjunctionStructure c d) ->
    adjunct.yankLawLftAbstract -> adjunct.yankLawLft
adjunct.yankLawLftAbstractToConcrete abst a =
  CalcWith (d.HomSet _ _) $
  |~ _
  ~~ _ ..<(adjunct.yankLawLftLemma a)
  ~~ _ ...(abst a)

public export
(.yankLawLftConcreteToAbstract) : {c,d : Category} ->
 (adjunct : AdjunctionStructure c d) ->
    adjunct.yankLawLft -> adjunct.yankLawLftAbstract
adjunct.yankLawLftConcreteToAbstract conc a =
  CalcWith (d.HomSet _ _) $
  |~ _
  ~~ _ ...(adjunct.yankLawLftLemma a)
  ~~ _ ...(conc a)

public export 0
(.yankLawRgtAbstract) : {c,d : Category} -> AdjunctionStructure c d -> Type
adjunct.yankLawRgtAbstract = (adjunct.rgt ~~> adjunct.rgt).equivalence.relation
  ( let u : (adjunct.rgt . Id) ~> adjunct.rgt
        u = U $ (IdRgt adjunct.rgt).from
        v : adjunct.rgt . adjunct.lft . adjunct.rgt ~> adjunct.rgt . Id
        v = (Id {f = adjunct.rgt}) * adjunct.counit
        w : (adjunct.rgt . adjunct.lft) . adjunct.rgt ~>
            adjunct.rgt . adjunct.lft . adjunct.rgt
        w = U (Associativity adjunct.rgt adjunct.lft adjunct.rgt).from
        q : (Id . adjunct.rgt) ~> (adjunct.rgt . adjunct.lft) . adjunct.rgt
        q = adjunct.unit * (Id {f = adjunct.rgt})
        r : adjunct.rgt ~> (Id . adjunct.rgt)
        r = U $ (IdLft adjunct.rgt).into
  in u . v . w . q . r)
  Id

public export
record TriangularLaws {C,D : Category} (adjunct : AdjunctionStructure C D) where
  constructor IsAdjunction
  lft : adjunct.yankLawLft
  rgt : adjunct.yankLawRgt


public export
record Adjunction (c,d : Category) where
  constructor MkAdjunction
  structure : AdjunctionStructure c d
  laws : TriangularLaws structure

public export
(.triangularStructure) : {c,d : Category} -> Adjunction.Adjunction c d ->
  AdjunctionStructure c d
adj.triangularStructure = MkAdjunctionStructure
  { lft = adj.lft
  , rgt = adj.rgt
  , unit = unit adj
  , counit = counit adj
  }

public export
(.triangular) : {c,d : Category} -> Adjunction.Adjunction c d ->
  Triangular.Adjunction c d
adj.triangular =
  let mate : {a : c.Obj} -> {b : d.Obj} ->
           d.HomSet (adj.lft !! a) b <~> c.HomSet a (adj.rgt !! b)
      mate = adj.adjoint.mate
  in MkAdjunction
  { structure = adj.triangularStructure
  , laws = IsAdjunction
      { lft = \a =>
          {- Diagram chasing:
             d.Hom FGFA FA ni counit ^ FA  <---- mateInv ---- Id : c.Hom GFA GFA
                 |                 mateInv naturality                    |
                 | - o F unit           =                     - o unit   |
                 v                                                       v
             (counit ^ FA) o (F Unit) = Id <---- mateInv ---- Unit = Id  o Unit

          -}
          let Fa : d.Obj
              Fa = adj.lft !! a
          in CalcWith (d.HomSet Fa Fa) $
          |~ ((counit adj) ^ Fa)
             . (adj.lft.map $ (unit adj) ^ a)
          ~~ adj.adjoint.mate.Bwd.H (Id . unit adj ^ a)
                ..<(adj.mateInvNaturalityPre _ _)
          ~~ adj.adjoint.mate.Bwd.H (unit adj ^ a)
                ...(adj.adjoint.mate.Bwd.homomorphic _ _ $
                    c.laws.idLftNeutral _)
          ~~ Id ...(adj.adjoint.mate.Iso.BwdFwdId _)
        -- Similar
      , rgt = \b =>
          let Gb : c.Obj
              Gb = adj.rgt !! b
          in CalcWith (c.HomSet Gb Gb) $
          |~ (adj.rgt.map ((counit adj) ^ b)
             . ((unit adj) ^ Gb))
          ~~ adj.adjoint.mate.Fwd.H ((counit adj ^ b) . Id)
                ..<(adj.mateNaturalityPost ((counit adj) ^ b) Id)
          ~~ adj.adjoint.mate.Fwd.H (counit adj ^ b)
                ...(adj.adjoint.mate.Fwd.homomorphic _ _ $
                    d.laws.idRgtNeutral ((counit adj) ^ b))
          ~~ Id ...(MkHomEq (adj.op.adjoint.mate.Iso.BwdFwdId Id).runEq)
      }
  }
