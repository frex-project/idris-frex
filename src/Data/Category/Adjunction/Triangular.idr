module Data.Category.Adjunction.Triangular

import Data.Setoid
import Data.Setoid.Fun

import Data.Category.Core
import Data.Category.Construction.Pair
import Data.Category.Construction.Op
import Data.Category.Setoid

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

public export 0
(.yankLawLft) : {c,d : Category} -> AdjunctionStructure c d -> Type
adjunct.yankLawLft = (adjunct.lft ~~> adjunct.lft).equivalence.relation
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
(.yankLawRgt) : {c,d : Category} -> AdjunctionStructure c d -> Type
adjunct.yankLawRgt = (adjunct.rgt ~~> adjunct.rgt).equivalence.relation
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
